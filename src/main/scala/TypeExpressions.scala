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

import sm.StateGraph

sealed abstract class TypeExpr {
  def >>(te : TypeExpr) = EffectTE(this, te)
  def isomorphic(te : TypeExpr) = TypeExprUtil.isomorphic(this, te)
  def isomorphic(te : TypeExpr, varEquiv : Equivalence[TypeVar, TypeVar]) =
    TypeExprUtil.isomorphic(this, te, varEquiv)
}

case object UnitTE extends TypeExpr {
  override def toString = "Unit"
}

case object BoolTE extends TypeExpr {
  override def toString = "Bool"
}

case class FunTE(params : Seq[EffectTE], ret : TypeExpr) extends TypeExpr {
  override def toString = "(" + params.mkString(",") + ") → " + ret
}

case class ObjectTE(objVar : TypeVar, stateVar : TypeVar) extends TypeExpr {
  override def toString = objVar + "@" + stateVar
}

case class SolvedObjectTE(
  graph : StateGraph, 
  states : Set[String]) extends TypeExpr

case class JoinTE(left : TypeExpr, right : TypeExpr) extends TypeExpr {
  override def toString = left + " ⊔ " + right
}

case class MeetTE(left : TypeExpr, right : TypeExpr) extends TypeExpr {
  override def toString = left + " ⊔ " + right
}

case class RemapTE(input : TypeExpr, effect : EffectTE) extends TypeExpr {
  override def toString = "remap(" + input + ", " + effect + ")"
}

case class VarTE(typeVar : TypeVar) extends TypeExpr {
  override def toString = typeVar.toString

  def =^=(equivTo : TypeExpr) = EqualityConstraint(this, equivTo)
}

case class EffectTE(in : TypeExpr, out : TypeExpr) {
  override def toString = in + " ≫ " + out
}

object TypeExprUtil {

  /**
   * Determines whether t1 and t2 are isomorphic.
   */
  def isomorphic(t1 : TypeExpr, t2 : TypeExpr) : Boolean = 
    isomorphic(t1, t2, new Equivalence(Map.empty))

  /**
   * Represents a bijective mapping between type variables in two
   * different type expressions t1 and t2. The boolean in the key pair
   * represents the "direction" of the mapping: true for a variable
   * in t2 mapped to t1, and false for a variable in t1 mapped to t2.
   * Both mappings will exist for fast lookup in either direction.
   */
  type TVEquivalence = Equivalence[TypeVar,TypeVar]

  def isomorphic(
    t1 : TypeExpr, 
    t2 : TypeExpr, 
    equivVars : TVEquivalence) 
    : Boolean = {

    (t1, t2) match {
      case (UnitTE, UnitTE) => true
      case (VarTE(v1), VarTE(v2)) => equivVars.addEquivalence(v1, v2)
      case (FunTE(f1params, f1ret), FunTE(f2params, f2ret)) =>
        functionsIsomorphic(f1params, f1ret, f2params, f2ret, equivVars)
      case (ObjectTE(o1v, o1s), ObjectTE(o2v, o2s)) =>
        (equivVars.addEquivalence(o1v, o2v) &&
          equivVars.addEquivalence(o1s, o2s))
      case (SolvedObjectTE(ss1, s1), SolvedObjectTE(ss2, s2)) => {
        // TODO
        false
      }
      case _ => false
    }
  }

  private def functionsIsomorphic(
    f1params : Seq[EffectTE], 
    f1ret : TypeExpr,
    f2params : Seq[EffectTE],
    f2ret : TypeExpr,
    equivVars : TVEquivalence)
    : Boolean = {

    if(f1params.length != f2params.length) {
      false
    } else {
      val paramPairs = f1params.zip(f2params)
      val paramIso = paramPairs.forall { case Pair(eff1, eff2) => {
        val inIso = isomorphic(eff1.in, eff2.in, equivVars)
        val outIso = isomorphic(eff1.out, eff2.out, equivVars)
        inIso && outIso
      }}

      paramIso && isomorphic(f1ret, f2ret, equivVars)
    }
  }
}