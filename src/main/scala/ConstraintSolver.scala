/*
 * This file is part of TS0.
 * 
 * TS0 - Copyright (c) 2012, Iain McGinniss
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted under the terms of the 2-clause BSD license:
 * http://opensource.org/licenses/BSD-2-Clause
 */

package uk.ac.gla.dcs.ts0

import org.kiama._
import org.kiama.attribution.Attribution._
import org.kiama.util.Messaging._
import grizzled.slf4j.Logger

case class BadRootContextDef(contextDef : ContextDefinition) extends Exception
case class UnresolvedDependency(contextDef : ContextDefinition) extends Exception
case class MissingVariable(base : ContextVar, varName : String) 
  extends Exception("context " + base + " does not contain variable " + varName)
case class DuplicateDefinition(base : ContextVar, varName : String) extends Exception
case class CannotUnifyTypes(t1 : Type, t2 : Type) extends Exception

object ConstraintSolver {

  def solve(constraints : ConstraintSet, t : Term) = {
    new ConstraintSolver(t).solve(constraints)
  }

  def solvePolymorphic(constraints : ConstraintSet, t : Term) = {
    new ConstraintSolver(t).solvePolymorphic(constraints)
  }
}

class ConstraintSolver(t : Term) {

  import ConstraintGenerator.tvGen
  import ConstraintGenerator.cvGen
  import ConstraintGenerator.typeVar
  import ConstraintGenerator.inContextVar
  import ConstraintGenerator.outContextVar

  val log = Logger[this.type]

  def solve(constraints : ConstraintSet) 
    : Option[Tuple3[Context, Type, Context]] = {
    
    val polySolution = solvePolymorphic(constraints)

    polySolution.map(soln => {
      val (inCtx, freeTypeVars, termTe, outCtx) = soln
      if(!freeTypeVars.isEmpty) {
        message(t,
          "term is polymorphic with type ∀" + freeTypeVars.mkString(",") +
          "." + termTe + " --- substituting Unit for all type variables")
      }

      val unitSubstitution = ((v : TypeVar) => UnitType())

      new Tuple3(
        makeContextExplicit(inCtx, unitSubstitution), 
        makeTypeExplicit(termTe, unitSubstitution), 
        makeContextExplicit(outCtx, unitSubstitution)
      )
    })
  }

  def solvePolymorphic(constraints : ConstraintSet)
    : Option[Tuple4[PolyContext,Set[TypeVar],TypeExpr,PolyContext]] = {

    log.debug("solving constraints for " + t)
    log.debug("constraints: " + constraints)
    val contexts = expandContexts(constraints.ccs, constraints.cvcs)
    log.debug("expanded contexts: " + contexts)
    val extraTypeConstraints = matchTypes(contexts, constraints.cvcs)
    val allTypeConstraints = constraints.tecs ++ extraTypeConstraints
    log.debug("derived type constraints: " + allTypeConstraints)
    val varsToTypeExprsOpt = unifyTypes(allTypeConstraints)
    
    varsToTypeExprsOpt.map(varsToTypeExprs => {
      log.debug("type constraints solution: " + varsToTypeExprs)
      val objects = solveMethodConstraints(constraints.mcs, varsToTypeExprs)
      log.debug("inferred object types: " + objects)
      val contextConverter = ((cv : ContextVar) =>
        contexts(cv).mapValues(te => 
          eliminateVariables(te, varsToTypeExprs, objects)._2)
      )
      val inCtx = contextConverter(t->inContextVar)
      val outCtx = contextConverter(t->outContextVar)

      val (free, termTe) = 
        eliminateVariables(
          varsToTypeExprs(t->typeVar), 
          varsToTypeExprs, 
          objects)

      new Tuple4(inCtx, free, termTe, outCtx)
    })
  }

  case class SolvedContext(contents : PolyContext, free : Boolean)

  def expandContexts(
    ccs : Seq[ContextConstraint], 
    cvcs : Seq[ContextVarConstraint]) 
    : Map[ContextVar,PolyContext] = {

    val ccById = 
      (ccs.foldLeft
        (Map.empty[ContextVar, ContextConstraint])
        ((m, c) => m + (c.context -> c)))

    val cvcsByContext =
      (cvcs.foldLeft
        (Map.empty[ContextVar, Seq[ContextVarConstraint]])
        ((m, c) => m.updated(c.context, m.getOrElse(c.context, c +: Seq.empty)))
      )

    val (roots, dependencies) =
      (ccs.foldLeft
        (Pair(Map.empty[ContextVar, ContextConstraint], 
              Map.empty[ContextVar, Set[ContextConstraint]]))
        ((result, c) => c.definedAs match {
          case cwd : ContextWithDependency => {
            val (roots, deps) = result
            val amendedDeps = deps.getOrElse(cwd.base, Set.empty) + c
            (roots, deps.updated(cwd.base, amendedDeps))
          }
          case bc : BaseContext => {
            val (roots, deps) = result
            (roots + (c.context -> c), deps)
          }
        })
      )

    // we are guaranteed from the way context constraints are constructed
    // that the dependency graph is a forest. Solve all constraints from
    // the roots to leaves

    var contexts = Map.empty[ContextVar, SolvedContext]
    var transRoots = Map.empty[ContextVar, ContextVar]

    var available : Set[ContextVar] = roots.keySet
    while(!available.isEmpty) {
      val next = available.head
      var (contextsUpdated, transRootsUpdated) = 
        solveCtxConstraint(ccById(next), contexts, transRoots)

      contexts = contextsUpdated
      transRoots = transRootsUpdated

      val localCvcs = cvcsByContext.getOrElse(next, Seq.empty)
      contexts =
        (localCvcs.foldLeft
          (contexts)
          ((ctxs, cvc) => checkForFreeVariable(cvc, ctxs, transRoots))
        )
      
      val tail : Set[ContextVar] = available.tail
      val depCcs = dependencies.getOrElse(next, Set.empty[ContextConstraint])
      val depCtxs = depCcs.map(_.context)
      available = depCtxs ++ tail
    }

    contexts.mapValues(sc => sc.contents)
  }

  def solveCtxConstraint(
    cc : ContextConstraint,
    contexts : Map[ContextVar, SolvedContext],
    transRoots : Map[ContextVar, ContextVar]) 
    : (Map[ContextVar, SolvedContext], Map[ContextVar, ContextVar]) = {

    cc.definedAs match {
      case BaseContext(contents, free) => {
        val contexts2 = contexts + (cc.context -> SolvedContext(contents, free))
        val transRoots2 = transRoots + (cc.context -> cc.context)
        (contexts2, transRoots2)
      }
      case cd : ContextWithDependency =>
        contexts.get(cd.base) match {
          case None => throw new UnresolvedDependency(cd)
          case Some(base) => {
            val contexts2 = 
              normaliseContext(cc.context, cd, contexts, transRoots)
            val transRoots2 = transRoots + (cc.context -> transRoots(cd.base))
            (contexts2, transRoots2)
          }
        }
    }
  }

  def normaliseContext(
    ctxVar : ContextVar,
    spec : ContextWithDependency, 
    contexts : Map[ContextVar, SolvedContext],
    transRoots : Map[ContextVar, ContextVar]) 
    : Map[ContextVar, SolvedContext] = {

    val base = contexts(spec.base)
    spec match {
      case ModifiedContext(baseVar, changedVars) => {
        val updatedContexts =
          (changedVars.foldLeft
            (contexts)
            ((ctxs, varChange) => {
              checkForFreeVariable(
                varChange._1, 
                varChange._2, 
                spec.base, 
                ctxs, 
                transRoots)
            })
          )

        val baseContents = updatedContexts(spec.base).contents
        val updatedContents = (changedVars.foldLeft(baseContents)(_ + _))

        updatedContexts + (ctxVar -> SolvedContext(updatedContents, false))
      }
        
      case ContextAddition(baseVar, additions) => {
        val updatedContents = 
          (additions.foldLeft
            (base.contents)
            ((contents, varAdd) => {
              if(contents.contains(varAdd._1)) {
                throw new DuplicateDefinition(baseVar, varAdd._1)
              }
              contents + varAdd
            })
          )

        contexts + (ctxVar -> SolvedContext(updatedContents, false))
      }

      case ContextRemoval(baseVar, removedVar) => {
        // FIXME: type variable needs to be fresh!
        val ctxs = checkForFreeVariable(
          removedVar, 
          VarTE((t->tvGen).next()), 
          spec.base, 
          contexts, 
          transRoots)

        val updatedContents = contexts(spec.base).contents - removedVar
        ctxs + (ctxVar -> SolvedContext(updatedContents, false))
      }
    }
  }

  def checkForFreeVariable(
    cvc : ContextVarConstraint,
    contexts : Map[ContextVar, SolvedContext],
    transRoots : Map[ContextVar, ContextVar])
    : Map[ContextVar, SolvedContext] =
    checkForFreeVariable(
      cvc.varName, 
      cvc.typeExpr, 
      cvc.context, 
      contexts, 
      transRoots)

  def checkForFreeVariable(
    varName : String,
    varType : TypeExpr,
    ctxVar : ContextVar,
    contexts : Map[ContextVar, SolvedContext],
    transRoots : Map[ContextVar, ContextVar])
    : Map[ContextVar, SolvedContext] = {

    val ctx = contexts(ctxVar)
    if(ctx.contents.get(varName).isDefined) {
      return contexts
    }

    // variable is not defined, so we must add it to the root and
    // all dependents as it is a free variable. 
    // However, if the variable is already defined
    // in any of the dependent contexts, then the free variable has been
    // rebound illegally.
    addFreeVariable(
      varName, 
      varType, 
      transRoots(ctxVar), 
      contexts, 
      transRoots)
  }

  def addFreeVariable(
    varName : String, 
    varType : TypeExpr, 
    ctxVar : ContextVar,
    contexts : Map[ContextVar, SolvedContext],
    transRoots : Map[ContextVar, ContextVar])
    : Map[ContextVar, SolvedContext] = {

    val ctx = contexts(ctxVar)
    if(!ctx.free) throw new MissingVariable(ctxVar, varName)

    val ctxDeps = transRoots.filter(_._2 == ctxVar).keySet
    val duplicate = ctxDeps.find(contexts(_).contents.contains(varName))
    if(duplicate.isDefined) {
      throw new DuplicateDefinition(duplicate.get, varName)
    }

    val varBind = (varName -> varType)
    
    (ctxDeps.foldLeft
      (contexts.updated(ctxVar, ctx.copy(contents = ctx.contents + varBind)))
      ((ctxs, depCtxVar) => {
        val depCtx = ctxs(depCtxVar)
        val updatedContents = depCtx.contents + varBind
        ctxs.updated(depCtxVar, depCtx.copy(contents = updatedContents))
      })
    )
  }

  /**
   * Generates additional TypeVarConstraints by comparing the list of
   * generated ContextVarConstraints to the known contents of all contexts.
   */
  def matchTypes(
    contexts : Map[ContextVar, PolyContext], 
    varConstraints : Seq[ContextVarConstraint]) : Seq[TypeExprConstraint] = {

    varConstraints.flatMap(v => {
      contexts(v.context).get(v.varName) match {
        // for terms where we allow free variables, the context var
        // constraint gives us information on something that should be
        // in the context. Where free variables are not allowed, it
        // indicates a type error as some piece of code is trying to use
        // an unbound variable.
        // TODO: handle this
        case None => Seq.empty
        case Some(typeExpr) => Seq(TypeExprConstraint(v.typeExpr, typeExpr))
      }
    })
  }

  def unifyTypes(constraints : Seq[TypeExprConstraint]) : Option[Map[TypeVar, TypeExpr]] = {
    val sys = UnificationProblemBuilder.build(constraints :_*)
    try {
      val solvedEqs : List[MultiEquation] = Unifier.unify(sys)
      log.debug("solvedEqs: " + solvedEqs)
      Some(SolutionExtractor.extract(solvedEqs))
    } catch {
      case e => {
        log.debug("solution failed: " + e)
        None
      }
    }
  }

  def solveMethodConstraints(
    methodConstraints : Seq[MethodConstraint],
    varsToTypeExprs : Map[TypeVar, TypeExpr]) : Map[TypeVar,Seq[StateTE]] = {

    
    // 3.1 if any orphaned states exist, we do not have a complete object model?

    log.debug("method constraints: " + methodConstraints)
    // transform method constraints to use canonical variables
    // for all objects and states described
    val updatedConstraints = methodConstraints.map(c =>
      c.copy(objVar = toCanonicalVar(c.objVar, varsToTypeExprs),
        stateVar = toCanonicalVar(c.stateVar, varsToTypeExprs),
        nextState = toCanonicalVar(c.nextState, varsToTypeExprs)))

    val initState = (stateVar : TypeVar) => StateTE(stateVar, Seq.empty)

    // TODO: is it necessary to drill into the TypeExpr structure to find
    // embedded ObjectTE instances too?
    val knownObjectStates = 
      (varsToTypeExprs.foldLeft
        (Map.empty[TypeVar, Map[TypeVar, StateTE]])
        ((m, p) => p._2 match {
          case ObjectTE(objVar, stVar) => {
            val states = m.getOrElse(objVar, Map.empty)
            m.updated(objVar, states + (stVar -> initState(stVar)))
          }
          case _ => m
        })
      )

    log.debug("knownObjectStates = " + knownObjectStates)

    // populate states with methods
    val statesWithMethods = 
      (updatedConstraints.foldLeft
        (knownObjectStates)
        ((m, c) => {
          val method = MethodTE(c.method, c.retType, c.nextState)
          log.debug("processing " + method)
          val obj = m.get(c.objVar).getOrElse(Map.empty[TypeVar, StateTE])
          val state = obj.getOrElse(c.stateVar, initState(c.stateVar))
          // TODO: check if method already exists, if so, further
          // constraint solving may be necessary?
          val updatedState = state.copy(methods = method +: state.methods)
          m + (c.objVar -> (obj + (c.stateVar -> updatedState)))
        })
      ).mapValues(stateMap => Seq.empty ++ stateMap.values)

    // finally, eliminate variables used for method return types
    // TODO: any risk of cycles here that we need to worry about?
    statesWithMethods.mapValues(states => {
      states.map(state => {
        state.copy(methods = state.methods.map(m => {
          m.copy(ret = 
            eliminateVariables(m.ret, varsToTypeExprs, statesWithMethods)._2)
        }))
      })
    })
  }

  /**
   * Substitutes the known type expression for every type variable in the
   * provided type expression. Where the variable has no known explicit
   * substitution, it is left in place.
   */
  def eliminateVariables(
    te : TypeExpr, 
    typeVarMap : Map[TypeVar,TypeExpr],
    objects : Map[TypeVar, Seq[StateTE]]) : (Set[TypeVar],TypeExpr) = {

    def eliminateVarsInMethod(method : MethodTE) : (Set[TypeVar], MethodTE) = {
      val (vars, retElim) = eliminateVariables(method.ret, typeVarMap, objects)
      (vars, method.copy(ret = retElim))
    }

    def eliminateVarsInState(state : StateTE) : (Set[TypeVar], StateTE) = {
      val (vars, methodsElim) = 
        (state.methods.foldLeft
          (Pair(Set.empty[TypeVar], Seq.empty[MethodTE]))
          ((p, m) => {
            val (mVars, mElim) = eliminateVarsInMethod(m)
            Pair(p._1 ++ mVars, mElim +: p._2)
          })
        )

      (vars, state.copy(methods = methodsElim))
    }

    def eliminateVarsInObj(obj : SolvedObjectTE)
    : (Set[TypeVar], SolvedObjectTE) = {
      val (vars, statesElim) =
        (obj.states.foldLeft
          (Pair(Set.empty[TypeVar], Seq.empty[StateTE]))
          ((p, s) => {
            val (sVars, sElim) = eliminateVarsInState(s)
            Pair(p._1 ++ sVars, sElim +: p._2)
          })
        )

      (vars, obj.copy(states = statesElim))
    }

    te match {
      case VarTE(tv) => typeVarMap.get(tv) match {
        case Some(VarTE(tv2)) if tv == tv2 => 
          // this variable cannot be eliminated
          Pair(Set(tv), VarTE(tv))
        case Some(other) => eliminateVariables(other, typeVarMap, objects)
        case None => Pair(Set(tv), VarTE(tv))
      }
      case UnitTE => Pair(Set.empty, UnitTE)
      case FunTE(effects, ret) => {
        val (effVars, effElim) = 
          (effects.foldRight
            (Pair(Set.empty[TypeVar], List.empty[EffectTE]))
            ((e, p) => {
              val (inVars, inTE) = 
                eliminateVariables(e.in, typeVarMap, objects)
              val (outVars, outTE) = 
                eliminateVariables(e.out, typeVarMap, objects)

              Pair(p._1 ++ inVars ++ outVars, EffectTE(inTE, outTE) :: p._2)
            })
          )
        val (retVars, retElim) = eliminateVariables(ret, typeVarMap, objects)
        Pair(effVars ++ retVars, FunTE(effElim, retElim))
      }
      case ObjectTE(objVar, stateVar) => {
        val canonicalStateVar = toCanonicalVar(stateVar, typeVarMap)
        val canonicalObjectVar = toCanonicalVar(objVar, typeVarMap)
        objects.get(canonicalObjectVar) match {
          case Some(states) => 
            (Set.empty, SolvedObjectTE(canonicalObjectVar, states, canonicalStateVar))
          case None => 
            throw new IllegalArgumentException("unknown object " + objVar)
        }
      }

      case o : SolvedObjectTE => {
        // TODO: is this a realistic occurrence?
        (Set.empty, o)
      }
    }
  }

    def makeTypeExplicit(
      te : TypeExpr,
      substitution : TypeVar => Type) : Type =
      te match {
        case VarTE(tv) => substitution(tv)
        case UnitTE => UnitType()
        case FunTE(effects, ret) => 
          FunType(
            effects.map(e => 
              EffectType(
                makeTypeExplicit(e.in, substitution),
                makeTypeExplicit(e.out, substitution)
              )
            ), 
            makeTypeExplicit(ret, substitution)
          )
        case SolvedObjectTE(objVar, states, state) => 
          ObjType(states.map(makeStateExplicit(_, substitution)), 
            typeVarToName(state))
        case o : ObjectTE => {
          log.error("unsolved ObjectTE: " + o)
          throw new IllegalArgumentException("unsolved: " + o)
        }
      }

    def makeStateExplicit(
      st : StateTE,
      substitution : TypeVar => Type) : StateSpec = {
      val methods = st.methods.map(m => 
        MethodSpec(
          m.name, 
          makeTypeExplicit(m.ret, substitution), 
          typeVarToName(m.next)
        )
      )

      StateSpec(typeVarToName(st.nameVar), methods)
    }

    def typeVarToName(tv : TypeVar) = "S" + tv.v

    def toCanonicalVar(tv : TypeVar, varsToTypeExprs : Map[TypeVar, TypeExpr]) =
      varsToTypeExprs.get(tv) match {
        case Some(VarTE(canonical)) => canonical
        case Some(x) =>
          throw new IllegalArgumentException(
            "canonical variable expected, got" + x)
        case None =>
          tv
      }

    def makeContextExplicit(
      ctx : PolyContext,
      substitution : TypeVar => Type) : Context =
      ctx.mapValues(te => makeTypeExplicit(te, substitution))
}