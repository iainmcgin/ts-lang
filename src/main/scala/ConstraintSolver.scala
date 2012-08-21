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

  import ConstraintGenerator.typeVar
  import ConstraintGenerator.inContextVar
  import ConstraintGenerator.outContextVar

  val log = Logger[this.type]

  def solve(constraints : ConstraintSet, t : Term) 
    : Option[Tuple3[Context, Type, Context]] = {
    
    val polySolution = solvePolymorphic(constraints, t)

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

  def solvePolymorphic(constraints : ConstraintSet, t : Term) 
    : Option[Tuple4[PolyContext,Set[TypeVar],TypeExpr,PolyContext]] = {

    println("t: " + t)
    println("constraints: " + constraints)
    val contexts = expandContexts(constraints.ccs)
    println("ctx: " + contexts)
    val extraTypeConstraints = matchTypes(contexts, constraints.cvcs)
    val allTypeConstraints = constraints.tecs ++ extraTypeConstraints
    println("tcs: " + allTypeConstraints)
    val varsToTypeExprsOpt = unifyTypes(allTypeConstraints)
    
    varsToTypeExprsOpt.map(varsToTypeExprs => {
      println("soln: " + varsToTypeExprs)
      val objects = solveMethodConstraints(constraints.mcs, varsToTypeExprs)
      println("objects: " + objects)
      val contextConverter = ((cv : ContextVar) =>
        contexts(cv).mapValues(te => 
          eliminateVariables(te, varsToTypeExprs, objects)._2)
      )
      val inCtx = contextConverter(t->inContextVar)
      val outCtx = contextConverter(t->outContextVar)

      println("te: " + varsToTypeExprs(t->typeVar))
      val (free, termTe) = 
        eliminateVariables(
          varsToTypeExprs(t->typeVar), 
          varsToTypeExprs, 
          objects)

      new Tuple4(inCtx, free, termTe, outCtx)
    })
  }

  def expandContexts(constraints : Seq[ContextConstraint]) 
    : Map[ContextVar,PolyContext] = {

    val constraintsById = 
      (constraints.foldLeft
        (Map.empty[ContextVar, ContextDefinition])
        ((m, c) => m + Pair(c.context, c.definedAs)))

    val dependents : Map[ContextVar, Set[ContextVar]] =
      (constraints.foldLeft
        (Map.empty[ContextVar, Set[ContextVar]])
        ((m, c) => c.definedAs match {
          case cwd : ContextWithDependency => 
            m.updated(cwd.base, m.getOrElse(cwd.base, Set.empty) + c.context)
          case bc : BaseContext => m
        })
      )

    // we are guaranteed from the way context constraints are constructed
    // that the dependency graph is a forest. Solve all constraints from
    // the roots to leaves

    val allDependents = 
      (dependents.values.foldLeft
        (Set.empty[ContextVar])
        ((s, cvs) => s ++ cvs)
      )

    var roots : Set[ContextVar] = constraintsById.keySet -- allDependents

    var contexts : Map[ContextVar, PolyContext] = 
      (roots.foldLeft
        (Map.empty[ContextVar, PolyContext])
        ((m, r) => 
          constraintsById(r) match {
            case bc : BaseContext => 
              m + Pair(r, solveContextConstraint(bc, Map.empty))
            case _ => 
              throw new BadRootContextDef(constraintsById(r))
          })
      )

    var available = roots.flatMap(r => dependents.getOrElse(r, Set.empty))
    while(!available.isEmpty) {
      val next = available.head
      contexts += 
        Pair(next, solveContextConstraint(constraintsById(next), contexts))
      available = dependents.getOrElse(next, Set.empty) ++ available.tail
    }

    contexts
  }

  def solveContextConstraint(
    cd : ContextDefinition, 
    contexts : Map[ContextVar, PolyContext]) : PolyContext = {

    cd match {
      case bc : BaseContext => bc.vars
      case cwd : ContextWithDependency => {
        if(!contexts.contains(cwd.base)) throw new UnresolvedDependency(cwd)
        updateContext(cwd, cwd.base, contexts(cwd.base))
      }
    }
  }

  def updateContext(
    spec : ContextWithDependency, 
    baseVar : ContextVar,
    base : PolyContext) : PolyContext = {
    spec match {
      case ModifiedContext(_, changedVars) => {
        var context = base
        changedVars.keySet.foreach(v => {
          if(!context.contains(v)) {
            println("mv " + v)
            println(context)
            throw new MissingVariable(baseVar, v)
          }
          context = context.updated(v, changedVars(v))
        })

        context
      }
        
      case ContextAddition(_, additions) =>
        (additions.foldLeft
          (base)
          ((ctx, p) => {
            if(base.contains(p._1)) 
              throw new DuplicateDefinition(baseVar, p._1)
            ctx + p
          })
        )

      case ContextRemoval(_, removedVar) => {
        if(!base.contains(removedVar)) {
          println(spec)
          println("mv " + removedVar)
          println(baseVar + " = " + base)
          throw MissingVariable(baseVar, removedVar)
        }

        base - removedVar
      }
    }
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
      println("solvedEqs: " + solvedEqs)
      Some(SolutionExtractor.extract(solvedEqs))
    } catch {
      case e => {
        println("solution failed: " + e)
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

    // populate states with methods
    val statesWithMethods = 
      (updatedConstraints.foldLeft
        (knownObjectStates)
        ((m, c) => {
          val method = MethodTE(c.method, c.retType, c.nextState)
          log.debug("processing " + method)
          val state = m(c.objVar).getOrElse(c.stateVar, initState(c.stateVar))
          // TODO: check if method already exists, if so, further
          // constraint solving may be necessary?
          val updatedState = state.copy(methods = method +: state.methods)
          m.updated(c.objVar, m(c.objVar).updated(c.stateVar, updatedState))
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
      case VarTE(tv) => typeVarMap(tv) match {
        case VarTE(tv2) if tv == tv2 => 
          // this variable cannot be eliminated
          Pair(Set(tv), VarTE(tv))
        case other => eliminateVariables(other, typeVarMap, objects)
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
            (Set.empty, SolvedObjectTE(states, canonicalStateVar))
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
        case SolvedObjectTE(states, state) => 
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