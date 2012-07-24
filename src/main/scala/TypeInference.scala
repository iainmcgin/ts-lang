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
  equivTo : Type) extends Constraint

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

/**
 * Specifies a new context based on some other known context, with
 * variables that existed in that context mapped to
 * potentially new types.
 */
case class ModifiedContext(base : ContextVar, changedVars : Map[String,Type])
  extends ContextDefinition

/**
 * Specifies a new context based on some other known context, with
 * a new variable mapping added.
 */
case class ContextAddition(
  base : ContextVar, 
  newVar : String,
  newType : Type) extends ContextDefinition

/**
 * Specifies a new context based on some other known context, with
 * a variable mapping removed.
 */
case class ContextRemoval(base : ContextVar, removedVar : String)
  extends ContextDefinition

/**
 * Specifies a context explicitly, with all known variable mappings
 * for that context.
 */
case class BaseContext(vars : Map[String,TypeVar]) extends ContextDefinition

case class ConstraintSet(
    ccs : Seq[ContextConstraint],
    cvcs : Seq[ContextVarConstraint],
    tvcs : Seq[TypeVarConstraint],
    mcs : Seq[MethodConstraint]
  ) {

  def +(constraint : Constraint) = constraint match {
    case cc : ContextConstraint => ConstraintSet(cc +: ccs, cvcs, tvcs, mcs)
    case cvc : ContextVarConstraint => ConstraintSet(ccs, cvc +: cvcs, tvcs, mcs)
    case tvc : TypeVarConstraint => ConstraintSet(ccs, cvcs, tvc +: tvcs, mcs)
    case mc : MethodConstraint => ConstraintSet(ccs, cvcs, tvcs, mc +: mcs)
  }
}

object TypeInferer {

  def inferTyping(t : Term) : Tuple3[Context,Type,Context] = {
    val constraints = allConstraints(t)

    new Tuple3(emptyContext, Hole(typeVars.next()), emptyContext)
  }
  
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

  def allConstraints(t : Term) : Seq[Constraint] = {
    t->constraints ++ (t match {
      case UnitValue() => Seq.empty
      case ObjValue(states,_) => Seq.empty
      case FunValue(_,body) => allConstraints(body)
      case LetBind(_,value,body) => 
        allConstraints(value) ++ allConstraints(body)
      case Update(_, body) => allConstraints(body)
      case MethCall(_,_) => Seq.empty
      case Sequence(left, right) => 
        allConstraints(left) ++ allConstraints(right)
      case FunCall(_,_) => Seq.empty
    })
  }

  val constraints : Term => Seq[Constraint] =
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
    Seq(
      TypeVarConstraint(t->typeVar, UnitType()),
      ContextConstraint(t->outContextVar, sameAs(t->inContextVar))
    )

  def objectValueConstraints(t : ObjValue) =
    Seq(
      ContextConstraint(t->outContextVar, sameAs(t->inContextVar)),
      TypeVarConstraint(t->typeVar, objTypeWithHoles(t))
    )

  def funValueConstraints(t : FunValue) = {
    val inTypeVars = t.params.map(paramToTypeVar)
    val outTypeVars = t.params.map(paramToTypeVar)
    val effects = buildEffects(inTypeVars, outTypeVars)
    val funType = FunType(effects, Hole(t.body->typeVar))

    val outTypeConstraints =
      (outTypeVars.foldLeft
        (Seq.empty[Constraint])
        ((s,p) => 
          ContextVarConstraint(t.body->outContextVar, p._1, Hole(p._2)) +: s))

    outTypeConstraints ++ Seq(
      ContextConstraint(t->outContextVar, sameAs(t->inContextVar)),
      ContextConstraint(t.body->inContextVar, 
        BaseContext(Map(inTypeVars: _*))),
      TypeVarConstraint(t->typeVar, funType)
    )
  }

  def letBindConstraints(t : LetBind) =
    Seq(
      ContextConstraint(t.value->inContextVar, sameAs(t->inContextVar)),
      ContextConstraint(t.body->inContextVar, 
        addTo(t.value->outContextVar, t.varName, Hole(t.value->typeVar))),
      ContextConstraint(t->outContextVar, 
        ContextRemoval(t.body->outContextVar, t.varName)),
      TypeVarConstraint(t->typeVar, Hole(t.body->typeVar))
    )

  def updateConstraints(t : Update) = {
    val bodyType = Hole(t.body->typeVar)
    Seq(
      ContextConstraint(t.body->inContextVar, 
        removeFrom(t->inContextVar, t.varName)),
      ContextConstraint(t->outContextVar, 
        ModifiedContext(t.body->outContextVar, Map(t.varName -> (bodyType)))),
      TypeVarConstraint(t->typeVar, UnitType())
    )
  }

  def sequenceConstraints(t : Sequence) =
    Seq(
      ContextConstraint(t.left->inContextVar, sameAs(t->inContextVar)),
      ContextConstraint(t.right->inContextVar, sameAs(t.left->outContextVar)),
      TypeVarConstraint(t->typeVar, Hole(t.right->typeVar))
    )

  def funCallConstraint(t : FunCall) = {
    val paramTypeVars = 
      t.paramNames.map(p => Tuple3(p, typeVars.next(), typeVars.next()))
    val funEffects = paramTypeVars.map(t => EffectType(Hole(t._2), Hole(t._3)))
    val funRetTypeVar = typeVars.next()
    val funType = FunType(funEffects, Hole(funRetTypeVar))

    val paramInConstraints = paramTypeVars.map(p =>
      ContextVarConstraint(t->inContextVar, p._1, Hole(p._2)))
    val paramOutConstraints = paramTypeVars.map(p =>
      ContextVarConstraint(t->outContextVar, p._1, Hole(p._3)))

    val contextChangedVars =
      (paramTypeVars.foldLeft
        (Map.empty[String,Type])
        ((m,p) => m + (p._1 -> Hole(p._3))))

    paramInConstraints ++ paramOutConstraints ++ Seq(
      ContextVarConstraint(t->inContextVar, t.funName, funType),
      ContextConstraint(t->outContextVar, 
        ModifiedContext(t->inContextVar, contextChangedVars)),
      TypeVarConstraint(t->typeVar, Hole(funRetTypeVar))
    )
  }

  def methCallConstraint(t : MethCall) = {
    val objectVar = objectVars.next()
    val inStateVar = stateVars.next()
    val outStateVar = stateVars.next()
    val inObjectType = ObjectHole(objectVar, inStateVar)
    val outObjectType = ObjectHole(objectVar, outStateVar)
    val methType = Hole(t->typeVar)
    Seq(
      TypeVarConstraint(t->inContextVar, inObjectType),
      MethodConstraint(objectVar, inStateVar, t.methName, 
        methType, outStateVar),
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