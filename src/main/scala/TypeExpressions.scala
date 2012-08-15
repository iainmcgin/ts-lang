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

abstract class TypeExpr {
  def >>(te : TypeExpr) = EffectTE(this, te)
}

case object UnitTE extends TypeExpr {
  override def toString = "Unit"
}

case class FunTE(params : Seq[EffectTE], ret : TypeExpr) extends TypeExpr {
  override def toString = "(" + params.mkString(",") + ") → " + ret
}

case class ObjectTE(objVar : TypeVar, stateVar : TypeVar) extends TypeExpr {
  override def toString = objVar + "@" + stateVar
}

case class VarTE(typeVar : TypeVar) extends TypeExpr {
  override def toString = typeVar.toString

  def =^=(equivTo : TypeExpr) = TypeExprConstraint(this, equivTo)
}

case class EffectTE(in : TypeExpr, out : TypeExpr) {
  override def toString = in + " ≫ " + out
}