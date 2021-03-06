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
sealed abstract class TypeConstraint extends Constraint
/** 
 * Represents evidence that a must be an equivalent type to b.
 */
case class EqualityConstraint(a : TypeExpr, b : TypeExpr) extends TypeConstraint {
  override def toString = a + " = " + b
}

/**
 * Represents evidence that a must be a subtype of b.
 */
case class SubtypeConstraint(a : TypeExpr, b : TypeExpr) extends TypeConstraint {
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

sealed abstract class ContextDefinition

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

case class ContextJoin(left : ContextVar, right : ContextVar)
  extends ContextDefinition {

  override def toString = left + " ⊔ " + right
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
    tecs : Seq[EqualityConstraint] = Seq.empty,
    scs : Seq[SubtypeConstraint] = Seq.empty) {

  def +(cc : ContextConstraint) = this.copy(ccs = cc +: ccs)
  def +(cvc : ContextVarConstraint) = this.copy(cvcs = cvc +: cvcs)
  def +(tec : EqualityConstraint) = this.copy(tecs = tec +: tecs)
  def +(sc : SubtypeConstraint) = this.copy(scs = sc +: scs)
  

  def ++(others : ConstraintSet) =
    ConstraintSet(
      ccs ++ others.ccs, 
      cvcs ++ others.cvcs,
      tecs ++ others.tecs,
      scs ++ others.scs)

  override def toString = {
    val sortedCcs = ccs.sortBy(_.context.v)
    val typeCs = tecs ++ scs
    ("context constraints:\n\t" +
      (if (sortedCcs.isEmpty) "none" else sortedCcs.mkString("\n\t")) +
      "\nvar constraints:\n\t" +
      (if (cvcs.isEmpty) "none" else cvcs.mkString("\n\t")) +
      "\ntype constraints:\n\t" +
      (if (typeCs.isEmpty) "none" else typeCs.mkString("\n\t"))
    )
  }

  def toStringSimple = {
    val sortedCcs = ccs.sortBy(_.context.v)
    (sortedCcs ++ cvcs ++ tecs ++ scs).mkString("; ")
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