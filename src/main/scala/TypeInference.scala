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

import scala.collection.mutable.Queue

/**
 * Simple class for allocation of unique variable identifiers.
 */
class Counter {
  private var last : Int = 0
  def next() = {
    last += 1
    last
  }
  def reset() = { last = 0 }
}

abstract class Constraint

/** 
 * Represents evidence that the specified type variable must be equal
 * to the specified type (which may itself be a type variable or contain
 * type variables in its structure).
 */
case class TypeVarConstraint(
  typeVar : TypeVar, 
  equivTo : Type) extends Constraint {

  override def toString = "α" + asSubscript(typeVar) + " = " + equivTo
}

/** 
 * Represents evidence that the specified context variable must be
 * composed of some other context and some explicit modifications,
 * as specified by a ContextDefinition.
 */
case class ContextConstraint(
  context : ContextVar, 
  definedAs : ContextDefinition) extends Constraint

/**
 * Represents evidence that the specified variable must have the
 * specified type in the specified context.
 */
case class ContextVarConstraint(
  context : ContextVar,
  varName : String,
  equalTo : Type) extends Constraint

/**
 * Represents evidence that an object in the specified type and state
 * must support a call to the named method with the specified return
 * type and state transition.
 */
case class MethodConstraint(
  objVar : ObjectVar,
  stateVar : StateVar,
  method : String,
  retType : Type,
  nextState : StateVar) extends Constraint

abstract class ContextDefinition

trait ContextWithDependency extends ContextDefinition {
  val base : ContextVar
}

/**
 * Specifies a new context based on some other known context, with
 * variables that existed in that context mapped to
 * potentially new types.
 */
case class ModifiedContext(base : ContextVar, changedVars : Map[String,Type])
  extends ContextWithDependency

/**
 * Specifies a new context based on some other known context, with
 * a new variable mapping added.
 */
case class ContextAddition(
  base : ContextVar, 
  newVar : String,
  newType : Type) extends ContextWithDependency

/**
 * Specifies a new context based on some other known context, with
 * a variable mapping removed.
 */
case class ContextRemoval(base : ContextVar, removedVar : String)
  extends ContextWithDependency

/**
 * Specifies a context explicitly, with all known variable mappings
 * for that context.
 */
case class BaseContext(vars : Map[String,TypeVar]) extends ContextDefinition

case class ConstraintSet(
    ccs : Seq[ContextConstraint],
    cvcs : Seq[ContextVarConstraint],
    tvcs : Seq[TypeVarConstraint],
    mcs : Seq[MethodConstraint]) {

  def +(cc : ContextConstraint) = ConstraintSet(cc +: ccs, cvcs, tvcs, mcs)
  def +(cvc : ContextVarConstraint) = ConstraintSet(ccs, cvc +: cvcs, tvcs, mcs)
  def +(tvc : TypeVarConstraint) = ConstraintSet(ccs, cvcs, tvc +: tvcs, mcs)
  def +(mc : MethodConstraint) = ConstraintSet(ccs, cvcs, tvcs, mc +: mcs)

  def ++(others : ConstraintSet) =
    ConstraintSet(
      ccs ++ others.ccs, 
      cvcs ++ others.cvcs,
      tvcs ++ others.tvcs,
      mcs ++ others.mcs)
}


object ConstraintGenerator {

  val empty = ConstraintSet(Seq.empty, Seq.empty, Seq.empty, Seq.empty)
  
  def sameAs(base : ContextVar) = ModifiedContext(base, Map.empty)
  def removeFrom(base : ContextVar, removedVar : String) =
    ContextRemoval(base, removedVar)
  def addTo(base : ContextVar, varName : String, varType : Type) = 
    ContextAddition(base, varName, varType)

  val typeVars = new Counter()
  val contextVars = new Counter()
  val objectVars = new Counter()
  val stateVars = new Counter()

  val typeVar : Term => Int =
    attr {
      case _ : Term => typeVars.next()
    }

  val inContextVar : Term => Int =
    attr {
      case _ : Term => contextVars.next()
    }

  val outContextVar : Term => Int =
    attr {
      case _ : Term => contextVars.next()
    }

  def allConstraints(t : Term) : ConstraintSet = {
    t->constraints ++ (t match {
      case UnitValue() => empty
      case o @ ObjValue(states,_) => methodConstraints(o)
      case FunValue(_,body) => allConstraints(body)
      case LetBind(_,value,body) => 
        allConstraints(value) ++ allConstraints(body)
      case Update(_, body) => allConstraints(body)
      case MethCall(_,_) => empty
      case Sequence(left, right) => 
        allConstraints(left) ++ allConstraints(right)
      case FunCall(_,_) => empty
    })
  }

  def methodConstraints(o : ObjValue) =
    (o.states
      .flatMap(s => s.methods)
      .map(m => m.ret)
      .foldLeft
        (empty)
        ((cs, v) => cs ++ (v->constraints) +
          ContextConstraint(v->inContextVar, sameAs(o->inContextVar)) +
          ContextConstraint(v->outContextVar, sameAs(v->inContextVar))
        )
    )

  val constraints : Term => ConstraintSet =
    attr {
      case t : UnitValue => unitValueConstraints(t)
      case t : ObjValue  => objectValueConstraints(t)
      case t : FunValue  => funValueConstraints(t)
      case t : LetBind   => letBindConstraints(t)
      case t : Update    => updateConstraints(t)
      case t : Sequence  => sequenceConstraints(t)
      case t : FunCall   => funCallConstraint(t)
      case t : MethCall  => methCallConstraint(t)
    }

  def unitValueConstraints(t : UnitValue) =
    (empty +
      TypeVarConstraint(t->typeVar, UnitType()) +
      ContextConstraint(t->outContextVar, sameAs(t->inContextVar)))
    

  def objectValueConstraints(t : ObjValue) =
    (empty +
      ContextConstraint(t->outContextVar, sameAs(t->inContextVar)) +
      TypeVarConstraint(t->typeVar, objTypeWithHoles(t))
    )

  def funValueConstraints(t : FunValue) = {
    val inTypeVars = t.params.map(paramToTypeVar)
    val outTypeVars = t.params.map(paramToTypeVar)
    val effects = buildEffects(inTypeVars, outTypeVars)
    val funType = FunType(effects, Hole(t.body->typeVar))

    val outTypeConstraints =
      (outTypeVars.foldLeft
        (empty)
        ((c,p) => 
          c + ContextVarConstraint(t.body->outContextVar, p._1, Hole(p._2))))

    outTypeConstraints ++ (empty +
      ContextConstraint(t->outContextVar, sameAs(t->inContextVar)) +
      ContextConstraint(t.body->inContextVar, 
        BaseContext(Map(inTypeVars: _*))) +
      TypeVarConstraint(t->typeVar, funType))
  }

  def letBindConstraints(t : LetBind) =
    (empty +
      ContextConstraint(t.value->inContextVar, sameAs(t->inContextVar)) +
      ContextConstraint(t.body->inContextVar, 
        addTo(t.value->outContextVar, t.varName, Hole(t.value->typeVar))) +
      ContextConstraint(t->outContextVar, 
        ContextRemoval(t.body->outContextVar, t.varName)) +
      TypeVarConstraint(t->typeVar, Hole(t.body->typeVar))
    )

  def updateConstraints(t : Update) = {
    val bodyType = Hole(t.body->typeVar)
    (empty +
      ContextConstraint(t.body->inContextVar, 
        removeFrom(t->inContextVar, t.varName)) +
      ContextConstraint(t->outContextVar, 
        addTo(t.body->outContextVar, t.varName, bodyType)) +
      TypeVarConstraint(t->typeVar, UnitType())
    )
  }

  def sequenceConstraints(t : Sequence) =
    (empty +
      ContextConstraint(t.left->inContextVar, sameAs(t->inContextVar)) +
      ContextConstraint(t.right->inContextVar, sameAs(t.left->outContextVar)) +
      TypeVarConstraint(t->typeVar, Hole(t.right->typeVar))
    )

  def funCallConstraint(t : FunCall) = {
    val paramTypeVars = 
      t.paramNames.map(p => Tuple3(p, typeVars.next(), typeVars.next()))
    val funEffects = paramTypeVars.map(t => EffectType(Hole(t._2), Hole(t._3)))
    val funRetTypeVar = typeVars.next()
    val funType = FunType(funEffects, Hole(funRetTypeVar))

    val paramConstraints = 
      (paramTypeVars.foldLeft
        (empty)
        ((c, p) => c + ContextVarConstraint(t->inContextVar, p._1, Hole(p._2)))
      )

    val contextChangedVars =
      (paramTypeVars.foldLeft
        (Map.empty[String,Type])
        ((m,p) => m + (p._1 -> Hole(p._3))))

    (paramConstraints ++
      (empty +
        ContextVarConstraint(t->inContextVar, t.funName, funType) +
        ContextConstraint(t->outContextVar, 
          ModifiedContext(t->inContextVar, contextChangedVars)) +
        TypeVarConstraint(t->typeVar, Hole(funRetTypeVar)))
    )
  }

  def methCallConstraint(t : MethCall) = {
    val objectVar = objectVars.next()
    val inStateVar = stateVars.next()
    val outStateVar = stateVars.next()
    val inObjectType = ObjectHole(objectVar, inStateVar)
    val outObjectType = ObjectHole(objectVar, outStateVar)
    val methType = Hole(t->typeVar)
    (empty +
      TypeVarConstraint(t->inContextVar, inObjectType) +
      MethodConstraint(objectVar, inStateVar, t.methName, 
        methType, outStateVar) +
      ContextConstraint(t->outContextVar, 
        ModifiedContext(t->inContextVar, Map(t.objVarName -> outObjectType)))
    )
  }

  def buildEffects(in : Seq[(String,TypeVar)], out : Seq[(String,TypeVar)]) =
    in.zip(out).map(x => EffectType(Hole(x._1._2), Hole(x._2._2)))

  val objTypeWithHoles = (objVal : ObjValue) =>
    ObjType(objVal.states map stateSpecWithHoles, objVal.state)

  val stateSpecWithHoles = (sdef : StateDef) =>
    StateSpec(sdef.name, sdef.methods.map(methodSpecWithHole))

  val methodSpecWithHole = (mdef : MethodDef) =>
    MethodSpec(mdef.name, Hole(mdef.ret->typeVar), mdef.nextState)

  val paramToTypeVar = (pdef : ParamDef) => Pair(pdef.name, typeVars.next())

}

case class BadRootContextDef(contextDef : ContextDefinition) extends Exception
case class UnresolvedDependency(contextDef : ContextDefinition) extends Exception
case class MissingVariable(base : Context, varName : String) extends Exception
case class DuplicateDefinition(base : Context, varName : String) extends Exception
case class CannotUnifyTypes(t1 : Type, t2 : Type) extends Exception

object ConstraintSolver {

  def solve(constraints : ConstraintSet, t : Term) : Tuple3[Context, Type, Context] = {
    val contexts = expandContexts(constraints.ccs)
    val extraTypeConstraints = matchTypes(contexts, constraints.cvcs)
    val allTypeConstraints = constraints.tvcs ++ extraTypeConstraints
    val types = unifyTypes(allTypeConstraints)

    new Tuple3(emptyContext, UnitType(), emptyContext)
  }

  def expandContexts(constraints : Seq[ContextConstraint]) = {
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

    var contexts = 
      (roots.foldLeft
        (Map.empty[ContextVar, Context])
        ((m, r) => 
          constraintsById(r) match {
            case bc : BaseContext => 
              m + Pair(r, solveContextConstraint(bc, Map.empty))
            case _ => 
              throw new BadRootContextDef(constraintsById(r))
          })
      )

    var available : Set[ContextVar] = roots.flatMap(r => dependents.getOrElse(r, Set.empty))
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
    contexts : Map[ContextVar, Context]) : Context = {

    cd match {
      case bc : BaseContext =>
        (bc.vars.foldLeft
          (emptyContext)
          ((m, v) => m + Pair(v._1, Hole(v._2)))
        )
      case cwd : ContextWithDependency => {
        if(!contexts.contains(cwd.base)) throw new UnresolvedDependency(cwd)
        updateContext(cwd, contexts(cwd.base))
      }
    }
  }

  def updateContext(spec : ContextWithDependency, base : Context) : Context = {
    spec match {
      case ModifiedContext(_, changedVars) => {
        var context = base
        changedVars.keySet.foreach(v => {
          if(!context.contains(v)) throw new MissingVariable(base, v)
          context = context.updated(v, changedVars(v))
        })

        context
      }
        
      case ContextAddition(_, newVar, newType) => {
        if(base.contains(newVar)) throw new DuplicateDefinition(base, newVar)
        base + Pair(newVar, newType)
      }

      case ContextRemoval(_, removedVar) => {
        if(!base.contains(removedVar)) throw MissingVariable(base, removedVar)
        base - removedVar
      }
    }
  }

  /**
   * Generates additional TypeVarConstraints by comparing the list of
   * generated ContextVarConstraints to the known contents of all contexts.
   */
  def matchTypes(
    contexts : Map[ContextVar, Context], 
    varConstraints : Seq[ContextVarConstraint]) : Seq[TypeVarConstraint] = {

    varConstraints.flatMap(v => {
      contexts(v.context).get(v.varName) match {
        // for terms where we allow free variables, the context var
        // constraint gives us information on something that should be
        // in the context. Where free variables are not allowed, it
        // indicates a type error as some piece of code is trying to use
        // an unbound variable.
        // TODO: handle this
        case None => Seq.empty
        case Some(knownType) => compareTypeStructure(v.equalTo, knownType)
      }
    })
  }

  def compareTypeStructure(t1 : Type, t2 : Type) : Seq[TypeVarConstraint] = {
    (t1,t2) match {
      case (Hole(tv), t) => Seq(TypeVarConstraint(tv, t))
      case (t, Hole(tv)) => Seq(TypeVarConstraint(tv, t))
      case (UnitType(), UnitType()) => Seq.empty
      case (f1 : FunType, f2 : FunType) => {
        if(f1.params.size != f2.params.size) throw new CannotUnifyTypes(f1, f2)
        val paramConstraints = f1.params.zip(f2.params).flatMap(effPair =>
          compareTypeStructure(effPair._1.before, effPair._2.before) ++
            compareTypeStructure(effPair._1.after, effPair._2.after)
        )
        val retConstraints = compareTypeStructure(f1.ret, f2.ret)
        paramConstraints ++ retConstraints
      }
      case (o1 : ObjType, o2 : ObjType) => {
        Seq.empty
      }
      case (ObjectHole(o1, s1), ObjectHole(o2, s2)) => Seq.empty
      case _ => throw CannotUnifyTypes(t1, t2)
    }
  }

  def filterTrivialConstraints(constraints : Seq[TypeVarConstraint]) =
    constraints.filter(c => (c.typeVar, c.equivTo) match {
      case (tv1, Hole(tv2)) if tv1 == tv2 => false
      case _ => true
    })

  def unifyTypes(constraints : Seq[TypeVarConstraint]) : Map[TypeVar, Type] = {

    
    // vars must point to their defining equation

    // 1. convert TypeVarConstraint instances into MultiEquation instances
    // 2. feed this into Unifier.unify
    // 3. take solved system of equations and use this to build the
    //    definitive typevar -> type map

    Map.empty
  }

}