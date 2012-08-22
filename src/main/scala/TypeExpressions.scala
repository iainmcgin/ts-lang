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

sealed abstract class TypeExpr {
  def >>(te : TypeExpr) = EffectTE(this, te)
  def isomorphic(te : TypeExpr) = TypeExprUtil.isomorphic(this, te)
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

case class SolvedObjectTE(
  objVar : TypeVar,
  states : Seq[StateTE], 
  state : TypeVar) 
  extends TypeExpr {

  override def toString = "{ " + states.mkString(" ") + " }@" + state
}

case class StateTE(nameVar : TypeVar, methods : Seq[MethodTE]) {
  override def toString = nameVar + "{ " + methods.mkString("; ") + " }"
}

case class MethodTE(name : String, ret : TypeExpr, next : TypeVar) {
  override def toString = name + " : " + ret + " ≫ " + next
}

case class VarTE(typeVar : TypeVar) extends TypeExpr {
  override def toString = typeVar.toString

  def =^=(equivTo : TypeExpr) = TypeExprConstraint(this, equivTo)
}

case class EffectTE(in : TypeExpr, out : TypeExpr) {
  override def toString = in + " ≫ " + out
}

object TypeExprUtil {

  /**
   * Determines whether a value of type t1 can be used where a value
   * of type t2 is expected.
   */
  def assignable(t1 : TypeExpr, t2 : TypeExpr) : Boolean = {
    val equivCheck = TypeExprConstraint(t1, t2)
    ConstraintSolver.unifyTypes(Seq(equivCheck)).isDefined
  }

  /**
   * Determines whether t1 and t2 are isomorphic.
   */
  def isomorphic(t1 : TypeExpr, t2 : TypeExpr) : Boolean = 
    isomorphic(t1, t2, Map.empty)._1

  /**
   * Represents a bijective mapping between type variables in two
   * different type expressions t1 and t2. The boolean in the key pair
   * represents the "direction" of the mapping: true for a variable
   * in t2 mapped to t1, and false for a variable in t1 mapped to t2.
   * Both mappings will exist for fast lookup in either direction.
   */
  type TVEquivalence = Map[(Boolean, TypeVar), TypeVar]

  private def isomorphic(
    t1 : TypeExpr, 
    t2 : TypeExpr, 
    equivVars : TVEquivalence) 
    : (Boolean, TVEquivalence) = {

    (t1, t2) match {
      case (UnitTE, UnitTE) => (true, Map.empty)
      case (VarTE(v1), VarTE(v2)) => varsEquivalent(v1, v2, equivVars)
      case (FunTE(f1params, f1ret), FunTE(f2params, f2ret)) =>
        functionsIsomorphic(f1params, f1ret, f2params, f2ret, equivVars)
      case (ObjectTE(o1v, o1s), ObjectTE(o2v, o2s)) => {
        val (ovIso, ev2) = varsEquivalent(o1v, o2v, equivVars)
        val (osIso, ev3) = varsEquivalent(o1s, o2s, equivVars)

        (ovIso && osIso, ev3)
      }
      case (SolvedObjectTE(o1, ss1, s1), SolvedObjectTE(o2, ss2, s2)) => {
        val (sIso, ev2) = varsEquivalent(s1, s2, equivVars)
        val (oIso, ev3) = varsEquivalent(o1, o2, equivVars)
        val (obIso, ev4) = statesIsomorphic(ss1, ss2, ev3)
        (sIso && oIso && obIso, ev4)
      }
      case other => (false, equivVars)
    }
  }

  private def varsEquivalent(
    v1 : TypeVar, 
    v2 : TypeVar, 
    equivVars : TVEquivalence) : (Boolean,TVEquivalence) = {

    val v1Equiv = equivVars.get(false -> v1)
    val v2Equiv = equivVars.get(true -> v2)
    (v1Equiv, v2Equiv) match {
      case (None, None) => {
        (true, equivVars + ((true -> v2) -> v1) + ((false -> v1) -> v2))
      }

      case (Some(v1eq), _) => {
        (v1eq == v2, equivVars)
      }

      case (None, Some(v2eq)) => {
        (v1 == v2eq, equivVars)
      }
    }
  }

  private def functionsIsomorphic(
    f1params : Seq[EffectTE], 
    f1ret : TypeExpr,
    f2params : Seq[EffectTE],
    f2ret : TypeExpr,
    equivVars : TVEquivalence)
    : (Boolean, TVEquivalence) = {

    if(f1params.length != f2params.length) {
      (false, equivVars)
    } else {
      val paramPairs = f1params.zip(f2params)
      val (paramIso, ev4) = (paramPairs.foldLeft
        (Pair(true, equivVars))
        ((result, paramPair) => {
          if(!result._1) result

          val ev = result._2
          val (eff1, eff2) = paramPair
          val (inIso, ev2) = isomorphic(eff1.in, eff2.in, ev)
          val (outIso, ev3) = isomorphic(eff1.out, eff2.out, ev2)
          Pair(inIso && outIso, ev3)
        })
      )

      val (resultIso, ev5) = isomorphic(f1ret, f2ret, ev4)
      Pair(paramIso && resultIso, ev5)
    }
  }

  private def statesIsomorphic(
    o1 : Seq[StateTE], 
    o2 : Seq[StateTE],
    equivVars : TVEquivalence)
    : (Boolean, TVEquivalence) = {

    if(o1.size != o2.size) (false, equivVars)

    val o1sorted = o1.sortBy(_.nameVar.v)
    val o2sorted = o2.sortBy(_.nameVar.v)

    (o1sorted.zip(o2sorted).foldLeft
      (Pair(true, equivVars))
      ((result, p) => {
        if(!result._1) result

        val ev = result._2
        val (st1, st2) = p
        statesIsomorphic(st1, st2, ev)
      })
    )
  }

  private def statesIsomorphic(
    s1 : StateTE,
    s2 : StateTE,
    equivVars : TVEquivalence)
    : (Boolean, TVEquivalence) = {

    val (namesIso, equivVars2) = 
      varsEquivalent(s1.nameVar, s2.nameVar, equivVars)
    
    if(!namesIso) (false, equivVars2)

    val s1meths = s1.methods.sortBy(_.name)
    val s2meths = s2.methods.sortBy(_.name)
    (s1meths.zip(s2meths).foldLeft
      (Pair(true, equivVars2))
      ((result, p) => {
        if(!result._1) result

        val ev = result._2
        val (m1, m2) = p
        if(m1.name != m2.name) (false, ev)
        val (nextStatesIso, ev2) = 
          varsEquivalent(m1.next, m2.next, ev)
        val (retTypesIso, ev3) = isomorphic(m1.ret, m2.ret, ev2)
        (nextStatesIso && retTypesIso, ev3)
      })
    )
  }
}