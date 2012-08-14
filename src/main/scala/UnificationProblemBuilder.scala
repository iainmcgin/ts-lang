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

object TypeUtil {

  val UNIT_LABEL = 0
  val FUN_LABEL = 1
  val OBJ_LABEL = 2

  def labelForType(x : Type) = x match {
    case _ : UnitType => UNIT_LABEL
    case _ : FunType => FUN_LABEL
    case _ : ObjType => OBJ_LABEL
  }
}

object UnificationProblemBuilder {
  def build(varConstraints : TypeExprConstraint*) = {
    val builder = new UnificationProblemBuilder()
    val eqs = builder.build(varConstraints)
    System(List.empty, builder.buildUPart(eqs))
  }

  def buildForTest(varConstraints : TypeExprConstraint*) = {
    val builder = new UnificationProblemBuilder()
    val eqs = builder.build(varConstraints)
    val upart = builder.buildUPart(eqs)
    Pair(eqs, upart)
  }
}

class UnificationProblemBuilder {

  private var vars = Map.empty[TypeVar, Variable]

  private def getVarSpec(tv : TypeVar) = {
    if(!vars.contains(tv)) {
      vars = vars.updated(tv, Variable(tv.v, null))
    }
    vars(tv)
  }

  type EqWithRefs = Pair[MultiEquation,Set[TypeVar]]

  def buildUPart(eqs : Set[MultiEquation]) : UPart = {

    val zeroRefEqs = eqs.filter(_.counter == 0)

    UPart(zeroRefEqs.toList, eqs.size)
  }

  def build(varConstraints : Seq[TypeExprConstraint]) : Set[MultiEquation] = {

    val eqsWithRefsByVariable = (varConstraints.foldLeft
      (Map.empty[TypeVar,EqWithRefs])
      ((m,c) => {
        (c.a, c.b) match {
          case (VarTE(v), VarTE(otherVar)) => {
            val (eq, varsInEq) = m.getOrElse(v, emptyEq(v))
            val (eq2, varsInEq2) = m.getOrElse(otherVar, emptyEq(otherVar))
            val merged = Pair(eq.merge(eq2), varsInEq ++ varsInEq2)
            val dupReferences = varsInEq intersect varsInEq2

            val m2 = fixReferenceCount(dupReferences, m, -1)

            m2 + (v -> merged) + (otherVar -> merged)
          }
          case (VarTE(v), te) => {
            val (eq, varsInEq) = m.getOrElse(v, emptyEq(v))
            val (multiTerm,varsInMultiTerm) = typeToMultiTerm(te)
            val newEq = MultiEquation(0, Set(getVarSpec(v)), Some(multiTerm))
            val merged = Pair(newEq.merge(eq), varsInMultiTerm ++ varsInEq)

            val newReferences = varsInMultiTerm -- varsInEq
            val m2 = fixReferenceCount(newReferences, m, 1)
            m2 + (v -> merged)
          }
          case (te1, te2) => {
            // TODO: unsure what to do here yet
            m
          }
        }
      })
    )

    vars.values.foreach(v => v.m = eqsWithRefsByVariable(TypeVar(v.num))._1)

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

  private def typeToMultiTerm(te : TypeExpr) : (MultiTerm,Set[TypeVar]) = {
    te match {
      case UnitTE => Pair(MultiTerm(TypeUtil.UNIT_LABEL, List.empty), Set.empty)
      case FunTE(params, ret) => 
        val (retTempEq,retVars) = typeToTempEq(ret)
        val (effectEqs, effectVars) = effectsToTempEqs(params)
        val args = (retTempEq +: effectEqs).reverse
        Pair(MultiTerm(TypeUtil.FUN_LABEL, args), retVars ++ effectVars)
      case ObjectTE(objVar, stVar) => {
        val (objVarEq, objVars) = typeToTempEq(VarTE(objVar))
        val (stVarEq, stVars) = typeToTempEq(VarTE(stVar))
        val vars = objVars ++ stVars
        Pair(MultiTerm(TypeUtil.OBJ_LABEL, List(objVarEq, stVarEq)), vars)
      }
    }
  }

  private def typeToTempEq(te : TypeExpr) : (TempMultiEquation, Set[TypeVar]) = {
    te match {
      case VarTE(tv) =>
        Pair(TempMultiEquation(Set(getVarSpec(tv)), None), Set(tv))
      case _ => {
        val (multiTerm,varsInMultiTerm) = typeToMultiTerm(te)
        Pair(TempMultiEquation(Set.empty, Some(multiTerm)), varsInMultiTerm)
      }
    }
  }

  /**
   * Converts all the effect types into a reversed list of TempMultiEquations,
   * along with the referenced set of type variables.
   */
  private def effectsToTempEqs(effects : Seq[EffectTE]) 
    : (List[TempMultiEquation],Set[TypeVar]) = {

    val (effEqs,effVars) = (effects.foldLeft
      (Pair(List.empty[TempMultiEquation],Set.empty[TypeVar]))
      ((p, eff) => {
        val (inTempEq, inVars) = typeToTempEq(eff.in)
        val (outTempEq, outVars) = typeToTempEq(eff.out)

        val eqs = outTempEq +: inTempEq +: p._1
        val vars : Set[TypeVar] = p._2 ++ inVars ++ outVars
        Pair(eqs, vars)
      })
    )
    
    (effEqs, effVars)
  }
}

case class PolymorphicSolutionException() extends Exception

object SolutionExtractor {
  def extract(eqs : List[MultiEquation]) : Map[TypeVar, TypeExpr] = {
    new SolutionExtractor(eqs).buildTypeMap()
  }
}

class SolutionExtractor(val eqs : List[MultiEquation]) {

  type EqOrType = Either[MultiEquation,TypeExpr]
  type VarToEqOrType = Map[TypeVar, EqOrType]

  private var varToEqOrType = 
    (eqs.foldLeft
      (Map.empty[TypeVar, EqOrType])
      ((m, eq) => 
        (eq.s.foldLeft
          (m)
          ((m2, v) => m2.updated(TypeVar(v.num), Left(eq)))
        )
      )
    )

  def buildTypeMap() : Map[TypeVar, TypeExpr] =
    varToEqOrType.mapValues(_.fold(
          (eq => eq.m match {
          case None => throw PolymorphicSolutionException()
          case Some(mt) => multiTermToType(mt)
          }),
          (ty => ty)
        )
    )

  private def multiTermToType(mt : MultiTerm) : TypeExpr = {
    mt.fn match {
      case TypeUtil.UNIT_LABEL => UnitTE
      case TypeUtil.FUN_LABEL => {
        val argTypes = mt.args.map(arg => {
          if(!arg.s.isEmpty) {
            varToType(arg.s.head)
          } else {
            multiTermToType(arg.m.get)
          }
        })
        
        val retType = argTypes.last
        val (effectTypes,_) = 
          (argTypes.dropRight(1).foldRight
            (Pair(List.empty[EffectTE], Option.empty[TypeExpr]))
            ((arg, p) => p._2 match {
              case None => Pair(p._1, Some(arg))
              case Some(x) => Pair(EffectTE(x, arg) :: p._1, None)
            })
          )

        FunTE(effectTypes, retType)
      }
      
      case TypeUtil.OBJ_LABEL => {
        // TODO: extract canonical object var and state var
        // ObjectTE(canObjVar, canStVar)
        UnitTE
      }
    }
  }

  private def varToType(v : Variable) : TypeExpr = {
    varToEqOrType(TypeVar(v.num)) match {
      case Left(meq) => {
        val ty = multiTermToType(meq.m.get)
        varToEqOrType = varToEqOrType.updated(TypeVar(v.num), Right(ty))
        ty
      }
      case Right(ty) => ty
    }
  }
}