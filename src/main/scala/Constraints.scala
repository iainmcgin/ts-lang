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

abstract class Constraint

/** 
 * Represents evidence that the specified type variable must be equal
 * to the specified type (which may itself be a type variable or contain
 * type variables in its structure).
 */
case class TypeExprConstraint(a : TypeExpr, b : TypeExpr) extends Constraint {
  override def toString = a + " = " + b
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

class ConstraintSet(
    val ccs : Seq[ContextConstraint],
    val cvcs : Seq[ContextVarConstraint],
    val tecs : Seq[TypeExprConstraint],
    val mcs : Seq[MethodConstraint]) {

  def +(cc : ContextConstraint) = ConstraintSet(cc +: ccs, cvcs, tecs, mcs)
  def +(cvc : ContextVarConstraint) = ConstraintSet(ccs, cvc +: cvcs, tecs, mcs)
  def +(tec : TypeExprConstraint) = ConstraintSet(ccs, cvcs, tec +: tecs, mcs)
  def +(mc : MethodConstraint) = ConstraintSet(ccs, cvcs, tecs, mc +: mcs)

  def ++(others : ConstraintSet) =
    ConstraintSet(
      ccs ++ others.ccs, 
      cvcs ++ others.cvcs,
      tecs ++ others.tecs,
      mcs ++ others.mcs)

  override def toString = {
    val sortedCcs = ccs.sortBy(_.context.v)

    (sortedCcs ++ cvcs ++ tecs ++ mcs).mkString("; ")
  }
}

object ConstraintSet {
  def apply(
    ccs : Seq[ContextConstraint],
    cvcs : Seq[ContextVarConstraint],
    tecs : Seq[TypeExprConstraint],
    mcs : Seq[MethodConstraint]) = new ConstraintSet(ccs, cvcs, tecs, mcs)

  val empty = ConstraintSet(Seq.empty, Seq.empty, Seq.empty, Seq.empty)
}

object MapUtil {
  def sortedStr(changes : PolyContext, pairSep : String) =
    (changes.toList
      .sortBy(_._1)
      .map(p => p._1 + pairSep + p._2)
      .mkString(",")
    )
}