/*
 * This file is part of TS.
 * 
 * TS - Copyright (c) 2012, Iain McGinniss
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted under the terms of the 2-clause BSD license:
 * http://opensource.org/licenses/BSD-2-Clause
 */

package uk.ac.gla.dcs.ts

import scala.annotation.tailrec

import org.kiama._
import org.kiama.attribution.Attribution._
import org.kiama.util.Messaging._
import grizzled.slf4j.Logger

import scalax.collection.Graph
import scalax.collection.GraphPredef._
import scalax.collection.GraphEdge._
import scalax.collection.edge.Implicits._

case class BadRootContextDef(contextDef : ContextDefinition) extends Exception
case class UnresolvedDependency(contextDef : ContextDefinition) extends Exception
case class CannotJoinContexts(contextDef : ContextDefinition) extends Exception
case class CyclicDependency(g : Graph[ContextVar, DiEdge]) extends Exception
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
          "term is polymorphic, substituting Unit for all type variables")
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
    val (contexts, extraScs) = expandContexts(constraints.ccs, constraints.cvcs)
    log.debug("expanded contexts:\n\t" + contexts.mkString("\n\t"))
    val extraTypeConstraints = matchTypes(contexts, constraints.cvcs)

    // XXX: for now, treat all subtype constraints as equality, until a closure
    // algorithm is implemented that finds correct solutions that respect
    // subtyping
    val subtypeConstraints = 
      (constraints.scs ++ extraScs).map(sc => TypeExprConstraint(sc.a, sc.b))

    val allTypeConstraints = 
      constraints.tecs ++ extraTypeConstraints ++ subtypeConstraints
    log.debug("derived type constraints:\n\t" + allTypeConstraints.mkString("\n\t"))

    val varsToTypeExprsOpt = unifyTypes(allTypeConstraints)
    
    varsToTypeExprsOpt.map(varsToTypeExprs => {
      log.debug("type constraints solution:\n\t" + varsToTypeExprs.mkString("\n\t"))
      val objects = solveMethodConstraints(constraints.mcs, varsToTypeExprs)
      log.debug("inferred object types:\n\t" + objects.mkString("\n\t"))
      val contextConverter = ((cv : ContextVar) =>
        contexts(cv).mapValues(te => 
          eliminateVariables(te, varsToTypeExprs, objects)._2)
      )
      val inCtx = contextConverter(t->inContextVar)
      val outCtx = contextConverter(t->outContextVar)

      val (free, termTe) = 
        eliminateVariables(
          varsToTypeExprs.getOrElse(t->typeVar, VarTE(t->typeVar)), 
          varsToTypeExprs, 
          objects)

      new Tuple4(inCtx, free, termTe, outCtx)
    })
  }

  case class SolvedContext(contents : PolyContext, free : Boolean)

  def expandContexts(
    ccs : Seq[ContextConstraint], 
    cvcs : Seq[ContextVarConstraint]) 
    : (Map[ContextVar,PolyContext],Seq[SubtypeConstraint]) = {

    val ccById = 
      (ccs.foldLeft
        (Map.empty[ContextVar, ContextConstraint])
        ((m, c) => m + (c.context -> c)))

    val cvcsByContext =
      (cvcs.foldLeft
        (Map.empty[ContextVar, Seq[ContextVarConstraint]])
        ((m, c) => m.updated(c.context, c +: m.getOrElse(c.context, Seq.empty)))
      )

    var dependencyGraph = buildDependencyGraph(ccs)

    // we are guaranteed from the way context constraints are constructed
    // that the dependency graph is acyclic. Solve all constraints from
    // the roots to leaves

    var contexts = Map.empty[ContextVar, SolvedContext]
    var transRoots = Map.empty[ContextVar, ContextVar]
    var extraScs = Seq.empty[SubtypeConstraint]

    val contextSortOpt = topologicalSort(dependencyGraph)
    if(contextSortOpt.isEmpty) throw new CyclicDependency(dependencyGraph)
    val contextSort = contextSortOpt.get
    contextSort.foreach(next => {
      var (contextsUpdated, transRootsUpdated, subtypeConstraints) = 
        solveCtxConstraint(ccById(next), contexts, transRoots)

      contexts = contextsUpdated
      transRoots = transRootsUpdated
      extraScs = extraScs ++ subtypeConstraints

      val localCvcs = cvcsByContext.getOrElse(next, Seq.empty)
      contexts =
        (localCvcs.foldLeft
          (contexts)
          ((ctxs, cvc) => checkForFreeVariable(cvc, ctxs, transRoots))
        )
    })

    (contexts.mapValues(sc => sc.contents), extraScs)
  }

  def buildDependencyGraph(constraints : Seq[ContextConstraint]) 
    : Graph[ContextVar, DiEdge] =
    (constraints.foldLeft
      (Graph.empty[ContextVar, DiEdge])
      ((g, c) => {
        val ctx = c.context
        c.definedAs match {
          case cwd : ContextWithDependency => g + (cwd.base ~> ctx)
          case cj : ContextJoin => g + (cj.left ~> ctx) + (cj.right ~> ctx)
          case bc : BaseContext => g + ctx
        }
      })
    )

  /*
   * code based on blog post by Andreas Flierl:
   * http://blog.flierl.eu/2012/04/fun-with-topological-sorting-using.html
   */
  def topologicalSort(g : Graph[ContextVar, DiEdge]) 
    : Option[List[ContextVar]] = {
    type NodeType = g.NodeT
    case class Memo(
      sorted : List[NodeType] = Nil, 
      grey : Graph[ContextVar, DiEdge] = Graph.empty[ContextVar, DiEdge],
      black : Graph[ContextVar, DiEdge] = Graph.empty[ContextVar, DiEdge])

    @tailrec
    def depthFirst(stack: List[NodeType], m: Memo): Option[Memo] = 
      stack match {
        case node :: nodes if m.black.contains(node) =>
          depthFirst(nodes, m)
        case node :: nodes =>
          val neighbours = stack.head.outNeighbors.toList
          if (neighbours.exists(m.grey.contains)) 
            None
          else if (neighbours.forall(m.black.contains))
            depthFirst(nodes, 
              Memo(node :: m.sorted, m.grey - node, m.black + node))
          else
            depthFirst(neighbours ++ stack, m.copy(grey = m.grey + node))
        case _ => Some(m)
      }

    (g.nodes.foldLeft
      (Option(Memo()))
      ((result, node) => result.flatMap(m => depthFirst(List(node), m)))
    ).map(_.sorted.map(_.value))
  }


  def solveCtxConstraint(
    cc : ContextConstraint,
    contexts : Map[ContextVar, SolvedContext],
    transRoots : Map[ContextVar, ContextVar]) 
    : (Map[ContextVar, SolvedContext], 
       Map[ContextVar, ContextVar],
       Seq[SubtypeConstraint]) = {

    cc.definedAs match {
      case BaseContext(contents, free) => {
        val contexts2 = contexts + (cc.context -> SolvedContext(contents, free))
        val transRoots2 = transRoots + (cc.context -> cc.context)
        (contexts2, transRoots2, Seq.empty)
      }
      case cd : ContextWithDependency =>
        contexts.get(cd.base) match {
          case None => throw new UnresolvedDependency(cd)
          case Some(base) => {
            val contexts2 = 
              normaliseContext(cc.context, cd, contexts, transRoots)
            val transRoots2 = transRoots + (cc.context -> transRoots(cd.base))
            (contexts2, transRoots2, Seq.empty)
          }
        }
      case cj : ContextJoin =>
        (contexts.get(cj.left), contexts.get(cj.right)) match {
          case (Some(left), Some(right)) => {
            joinPolyContexts(left.contents, right.contents, t->tvGen).
              map(res => {
                val (ctx, scs) = res
                val contexts2 = contexts + 
                  (cc.context -> SolvedContext(ctx, false))
                val transRoots2 = transRoots + 
                  (cc.context -> transRoots(cj.left))
                (contexts2, transRoots2, scs)
              }).
              getOrElse(throw new CannotJoinContexts(cj))
          }
          case _ => throw new UnresolvedDependency(cj)
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
              // if the variable we are modifying is free, then
              // we know nothing about its type yet and so generate
              // a new type variable for it.
              checkForFreeVariable(
                varChange._1, 
                VarTE((t->tvGen).next()),
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

    log.debug("free variable " + varName + " found with type " + varType)

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
    try {
      val sys = UnificationProblemBuilder.build(constraints :_*)
      val solvedEqs : List[MultiEquation] = Unifier.unify(sys)
      log.debug("solvedEqs: " + solvedEqs)
      Some(SolutionExtractor.extract(solvedEqs))
    } catch {
      case e => {
        log.debug("cannot solve constraints: " + e)
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

    // TODO: is it necessary to drill into the TypeExpr structure to find
    // embedded ObjectTE instances too?
    val knownObjectStates = 
      extractStatesFromConstraints(
        extractStatesFromVarMap(varsToTypeExprs),
        updatedConstraints)

    log.debug("knownObjectStates = " + knownObjectStates)

    // populate states with methods
    val statesWithMethods = 
      (updatedConstraints.foldLeft
        (knownObjectStates)
        ((m, c) => {
          val method = MethodTE(c.method, c.retType, c.nextState)
          log.debug("processing " + method)
          val obj = m.get(c.objVar).getOrElse(Map.empty[TypeVar, StateTE])
          val state = obj.getOrElse(c.stateVar, StateTE(c.stateVar))
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

  def extractStatesFromVarMap(varsToTypeExprs : Map[TypeVar, TypeExpr])
    : Map[TypeVar, Map[TypeVar, StateTE]] =
    (varsToTypeExprs.foldLeft
        (Map.empty[TypeVar, Map[TypeVar, StateTE]])
        ((m, p) => p._2 match {
          case ObjectTE(objVar, stVar) => {
            val states = m.getOrElse(objVar, Map.empty)
            m.updated(objVar, states + (stVar -> StateTE(stVar)))
          }
          case _ => m
        })
      )

  def extractStatesFromConstraints(
    stateMap : Map[TypeVar, Map[TypeVar, StateTE]],
    constraints : Seq[MethodConstraint])
    : Map[TypeVar, Map[TypeVar, StateTE]] =
    (constraints.foldLeft
      (stateMap)
      ((m, c) => {
        val states = m.getOrElse(c.objVar, Map.empty)
        val inState = 
          c.stateVar -> states.getOrElse(c.stateVar, StateTE(c.stateVar))
        val outState = 
          c.nextState -> states.getOrElse(c.nextState, StateTE(c.nextState))
        m.updated(c.objVar, states + inState + outState)
      })
    )

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
      case BoolTE => Pair(Set.empty, BoolTE)
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
        case BoolTE => BoolType()
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