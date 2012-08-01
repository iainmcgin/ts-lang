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

import scala.math.max

object UnificationProblemBuilder {
  def build(varConstraints : TypeVarConstraint*) = {
    val builder = new UnificationProblemBuilder()
    val eqs = builder.build(varConstraints)
    builder.buildUPart(eqs)
  }

  def buildForTest(varConstraints : TypeVarConstraint*) = {
    val builder = new UnificationProblemBuilder()
    val eqs = builder.build(varConstraints)
    val upart = builder.buildUPart(eqs)
    Pair(eqs, upart)
  }
}

class UnificationProblemBuilder {

  private var vars = Map.empty[TypeVar, Variable]

  private def getVarSpec(v : TypeVar) = {
    if(!vars.contains(v)) {
      vars = vars.updated(v, Variable(v, null))
    }
    vars(v)
  }

  type EqWithRefs = Pair[MultiEquation,Set[TypeVar]]

  def buildUPart(eqs : Set[MultiEquation]) : UPart = {

    val zeroRefEqs = eqs.filter(_.counter == 0)

    UPart(zeroRefEqs.toList, eqs.size)
  }

  def build(varConstraints : Seq[TypeVarConstraint]) : Set[MultiEquation] = {

    val eqsWithRefsByVariable = (varConstraints.foldLeft
      (Map.empty[TypeVar,EqWithRefs])
      ((m,c) => {
        val v = c.typeVar
        val (eq, varsInEq) = m.getOrElse(v, emptyEq(v))

        c.equivTo match {
          case Hole(otherVar) => {
            val (eq2, varsInEq2) = m.getOrElse(otherVar, emptyEq(otherVar))
            val merged = Pair(eq.merge(eq2), varsInEq ++ varsInEq2)
            val dupReferences = varsInEq intersect varsInEq2

            val m2 = fixReferenceCount(dupReferences, m, -1)

            m2 + (v -> merged) + (otherVar -> merged)
          }
          case ty => {
            val (multiTerm,varsInMultiTerm) = typeToMultiTerm(ty)
            val newEq = MultiEquation(0, Set(getVarSpec(v)), Some(multiTerm))
            val merged = Pair(newEq.merge(eq), varsInMultiTerm ++ varsInEq)

            val newReferences = varsInMultiTerm -- varsInEq
            val m2 = fixReferenceCount(newReferences, m, 1)
            m2 + (v -> merged)
          }
        }
      })
    )

    vars.values.foreach(v => v.m = eqsWithRefsByVariable(v.num)._1)

    eqsWithRefsByVariable.values.map(_._1).toSet
  }

  private def emptyEq(v : TypeVar) : EqWithRefs = 
    Pair(MultiEquation(0, Set(getVarSpec(v)), None),Set.empty[TypeVar])

  private def fixReferenceCount(
    vs : Set[TypeVar], 
    m : Map[TypeVar,EqWithRefs], 
    d : Int) = 
    (vs.foldLeft
      (m)
      ((m2, v) => {
        val newEq = m2.get(v) match {
          case None => 
            Pair(
              MultiEquation(max(0, d), Set(getVarSpec(v)), None), 
              Set.empty[TypeVar]
            )
          case Some(Pair(MultiEquation(c, s, m),refs)) => 
            Pair(MultiEquation(c + d, s, m), refs)
        }
        m2.updated(v, newEq)
      })
    )

  private def typeToMultiTerm(ty : Type) : (MultiTerm,Set[TypeVar]) = {
    ty match {
      case UnitType() => Pair(MultiTerm(0, List.empty), Set.empty)
      case FunType(params, ret) => 
        val (retTempEq,retVars) = typeToTempEq(ret)
        val (effectEqs, effectVars) = effectsToTempEqs(params)
        val args = (retTempEq +: effectEqs).reverse
        Pair(MultiTerm(1, args), retVars ++ effectVars)
      // TODO
      case ObjType(_,_) => Pair(MultiTerm(2, List.empty), Set.empty)
    }
  }

  private def typeToTempEq(ty : Type) : (TempMultiEquation, Set[TypeVar]) = {
    ty match {
      case Hole(tv) =>
        Pair(TempMultiEquation(Set(getVarSpec(tv)), None), Set(tv))
      case _ => {
        val (multiTerm,varsInMultiTerm) = typeToMultiTerm(ty)
        Pair(TempMultiEquation(Set.empty, Some(multiTerm)), varsInMultiTerm)
      }
    }
  }

  /**
   * Converts all the effect types into a reversed list of TempMultiEquations,
   * along with the referenced set of type variables.
   */
  private def effectsToTempEqs(effects : Seq[EffectType]) 
    : (List[TempMultiEquation],Set[TypeVar]) = {

    val (effEqs,effVars) = (effects.foldLeft
      (Pair(List.empty[TempMultiEquation],Set.empty[TypeVar]))
      ((p, eff) => {
        val (beforeTempEq, varsInBefore) = typeToTempEq(eff.before)
        val (afterTempEq, varsInAfter) = typeToTempEq(eff.after)

        val eqs = afterTempEq +: beforeTempEq +: p._1
        val vars : Set[TypeVar] = p._2 ++ varsInBefore ++ varsInAfter
        Pair(eqs, vars)
      })
    )
    
    (effEqs, effVars)
  }
}