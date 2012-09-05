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

sealed abstract class Constraint

/** 
 * Represents evidence that a must be an equivalent type to b.
 */
case class TypeExprConstraint(a : TypeExpr, b : TypeExpr) extends Constraint {
  override def toString = a + " = " + b
}

/**
 * Represents evidence that a must be a subtype of b.
 */
case class SubtypeConstraint(a : TypeExpr, b : TypeExpr) extends Constraint {
  override def toString = a + " <: " + b
}

/** 
 * Represents evidence that the specified context variable must be
 * composed of some other context and some explicit modifications,
 * as specified by a ContextDefinition.
 */
case class ContextConstraint(
  context : ContextVar, 
  definedAs : ContextDefinition) extends Constraint {
  override def toString = context + " = " + definedAs
}

/**
 * Represents evidence that the specified variable must have the
 * specified type in the specified context.
 */
case class ContextVarConstraint(
  context : ContextVar,
  varName : String,
  typeExpr : TypeExpr) extends Constraint {

  override def toString = varName + " : " + typeExpr + " ∈ " + context
}

/**
 * Represents evidence that an object in the specified type and state
 * must support a call to the named method with the specified return
 * type and state transition.
 */
case class MethodConstraint(
  objVar : TypeVar,
  stateVar : TypeVar,
  method : String,
  retType : TypeExpr,
  nextState : TypeVar) extends Constraint {

  override def toString = method + " : " + retType + " ⇒ " + nextState + 
    " ∈ " + objVar + "@" + stateVar
}

abstract class ContextDefinition

trait ContextWithDependency extends ContextDefinition {
  val base : ContextVar
}

/**
 * Specifies a new context based on some other known context, with
 * variables that existed in that context mapped to
 * potentially new types.
 */
case class ModifiedContext(
  base : ContextVar, 
  changedVars : PolyContext)
  extends ContextWithDependency {

  override def toString = {
    base + " [ " + MapUtil.sortedStr(changedVars, " → ") + " ] "
  }
}

/**
 * Specifies a new context based on some other known context, with
 * a new variable mapping added.
 */
case class ContextAddition(
  base : ContextVar, 
  newVars : PolyContext) 
extends ContextWithDependency {

  override def toString = base + ", " + MapUtil.sortedStr(newVars, " : ")
}

/**
 * Specifies a new context based on some other known context, with
 * a variable mapping removed.
 */
case class ContextRemoval(base : ContextVar, removedVar : String)
  extends ContextWithDependency {

  override def toString = base + " - { " + removedVar + " }"
}

/**
 * Specifies a context explicitly, with all known variable mappings
 * for that context. Used as the input context for a function body.
 */
case class BaseContext(vars : PolyContext, free : Boolean) 
  extends ContextDefinition {

  override def toString = 
    (if (free) "<FREE> " else "<FIXED> ") + MapUtil.sortedStr(vars, " : ")
}

case class ConstraintSet(
    ccs : Seq[ContextConstraint] = Seq.empty,
    cvcs : Seq[ContextVarConstraint] = Seq.empty,
    tecs : Seq[TypeExprConstraint] = Seq.empty,
    scs : Seq[SubtypeConstraint] = Seq.empty,
    mcs : Seq[MethodConstraint] = Seq.empty) {

  def +(cc : ContextConstraint) = this.copy(ccs = cc +: ccs)
  def +(cvc : ContextVarConstraint) = this.copy(cvcs = cvc +: cvcs)
  def +(tec : TypeExprConstraint) = this.copy(tecs = tec +: tecs)
  def +(sc : SubtypeConstraint) = this.copy(scs = sc +: scs)
  def +(mc : MethodConstraint) = this.copy(mcs = mc +: mcs)
  

  def ++(others : ConstraintSet) =
    ConstraintSet(
      ccs ++ others.ccs, 
      cvcs ++ others.cvcs,
      tecs ++ others.tecs,
      scs ++ others.scs,
      mcs ++ others.mcs)

  override def toString = {
    val sortedCcs = ccs.sortBy(_.context.v)

    (sortedCcs ++ cvcs ++ tecs ++ scs ++ mcs).mkString("; ")
  }
}

object MapUtil {
  def sortedStr(changes : PolyContext, pairSep : String) =
    (changes.toList
      .sortBy(_._1)
      .map(p => p._1 + pairSep + p._2)
      .mkString(",")
    )
}