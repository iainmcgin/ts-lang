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

case class BadRootContextDef(contextDef : ContextDefinition) extends Exception
case class UnresolvedDependency(contextDef : ContextDefinition) extends Exception
case class MissingVariable(base : ContextVar, varName : String) extends Exception
case class DuplicateDefinition(base : ContextVar, varName : String) extends Exception
case class CannotUnifyTypes(t1 : Type, t2 : Type) extends Exception

object ConstraintSolver {

  import ConstraintGenerator.typeVar
  import ConstraintGenerator.inContextVar
  import ConstraintGenerator.outContextVar

  type InferredContext = Map[String, TypeExpr]

  def solve(constraints : ConstraintSet, t : Term) : Tuple3[Context, Type, Context] = {
    val contexts = expandContexts(constraints.ccs)
    val extraTypeConstraints = matchTypes(contexts, constraints.cvcs)
    val allTypeConstraints = constraints.tecs ++ extraTypeConstraints
    val varsToTypeExprs = unifyTypes(allTypeConstraints)

    val contextConverter = (cv : ContextVar) => (
      contexts(cv).mapValues(makeTypeExplicit(_, varsToTypeExprs))
    )
    val inCtx = contextConverter(t->inContextVar)
    val outCtx = contextConverter(t->outContextVar)
    val termTy = makeTypeExplicit(varsToTypeExprs(t->typeVar), varsToTypeExprs)

    new Tuple3(inCtx, termTy, outCtx)
  }

  def expandContexts(constraints : Seq[ContextConstraint]) 
    : Map[ContextVar,Map[String,TypeExpr]] = {

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

    var contexts : Map[ContextVar, InferredContext] = 
      (roots.foldLeft
        (Map.empty[ContextVar, InferredContext])
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
    contexts : Map[ContextVar, InferredContext]) : InferredContext = {

    cd match {
      case bc : BaseContext => bc.vars
      case fc : FreeContext => fc.vars
      case cwd : ContextWithDependency => {
        if(!contexts.contains(cwd.base)) throw new UnresolvedDependency(cwd)
        updateContext(cwd, cwd.base, contexts(cwd.base))
      }
    }
  }

  def updateContext(
    spec : ContextWithDependency, 
    baseVar : ContextVar,
    base : InferredContext) : InferredContext = {
    spec match {
      case ModifiedContext(_, changedVars) => {
        var context = base
        changedVars.keySet.foreach(v => {
          if(!context.contains(v)) throw new MissingVariable(baseVar, v)
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
        if(!base.contains(removedVar)) 
          throw MissingVariable(baseVar, removedVar)

        base - removedVar
      }
    }
  }

  /**
   * Generates additional TypeVarConstraints by comparing the list of
   * generated ContextVarConstraints to the known contents of all contexts.
   */
  def matchTypes(
    contexts : Map[ContextVar, InferredContext], 
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

  def unifyTypes(constraints : Seq[TypeExprConstraint]) : Map[TypeVar, TypeExpr] = {
    val sys = UnificationProblemBuilder.build(constraints :_*)
    val solvedEqs : List[MultiEquation] = Unifier.unify(sys)
    SolutionExtractor.extract(solvedEqs)
  }

  def makeTypeExplicit(te : TypeExpr, typeVarMap : Map[TypeVar,TypeExpr]) : Type = {
    te match {
      case VarTE(tv) => makeTypeExplicit(typeVarMap(tv), typeVarMap)
      case UnitTE => UnitType()
      case FunTE(effects, ret) => {
        val explicitEffects = effects.map(e => 
          EffectType(
            makeTypeExplicit(e.in, typeVarMap), 
            makeTypeExplicit(e.out, typeVarMap)))
        FunType(explicitEffects, makeTypeExplicit(ret, typeVarMap))
      }
      case ObjectTE(objVar,stateVar) => {
        // TODO
        UnitType()
      }
    }
  }
}