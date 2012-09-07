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

import scala.math.max
import grizzled.slf4j.Logger

object TypeUtil {

  val UNIT_LABEL = 0
  val BOOL_LABEL = 1
  val FUN_LABEL = 2
  val OBJ_LABEL = 3

  def labelForType(x : Type) = x match {
    case _ : UnitType => UNIT_LABEL
    case _ : BoolType => BOOL_LABEL
    case _ : FunType => FUN_LABEL
    case _ : ObjType => OBJ_LABEL
    case _ => throw new IllegalArgumentException("invalid type for unification")
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

  val log = Logger[this.type]

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

    val (eqsWithRefsByVariable, noVarEqs) = (varConstraints.foldLeft
      (Pair(Map.empty[TypeVar,EqWithRefs], List.empty[MultiEquation]))
      ((p,c) => {
        val m = p._1
        val l = p._2

        log.debug("processing " + c)
        val res = (c.a, c.b) match {
          case (VarTE(v), VarTE(otherVar)) => {
            val (eq, varsInEq) = m.getOrElse(v, emptyEq(v))
            val (eq2, varsInEq2) = m.getOrElse(otherVar, emptyEq(otherVar))
            val merged = Pair(eq.merge(eq2), varsInEq ++ varsInEq2)
            val dupReferences = varsInEq intersect varsInEq2

            log.debug("eq = " + merged._1)

            val m2 = fixReferenceCount(dupReferences, m, -1)
            Pair(pointVarsToEq(m2, merged), l)
          }
          case (VarTE(v), te) => Pair(processVarToTypeEquality(m, v, te), l)
          case (te, VarTE(v)) => Pair(processVarToTypeEquality(m, v, te), l)
          case (te1, te2) => {
            val (mt1, vmt1) = typeToMultiTerm(te1)
            val (mt2, vmt2) = typeToMultiTerm(te2)
            val merged = MultiEquation(0, Set.empty, Some(mt1.merge(Some(mt2))))

            log.debug("eq = " + merged)

            val m2 = fixReferenceCount(vmt1 ++ vmt2, m, 1)
            
            Pair(m2, merged :: l)
          }
        }

        log.debug("eqn state: " + (res._1.map(p => (p._1, p._2._1))) + " and " + res._2)
        res
      })
    )

    vars.values.foreach(v => v.m = eqsWithRefsByVariable(TypeVar(v.num))._1)

    val allEqs = eqsWithRefsByVariable.values.map(_._1).toSet ++ noVarEqs
    log.debug("all eqs: " + allEqs)
    allEqs
  }

  private def processVarToTypeEquality(eqsByVar : Map[TypeVar, EqWithRefs],
    v : TypeVar,
    te : TypeExpr) : Map[TypeVar, EqWithRefs] = {

    val (eq, varsInEq) = eqsByVar.getOrElse(v, emptyEq(v))
    val (multiTerm,varsInMultiTerm) = typeToMultiTerm(te)
    val newEq = MultiEquation(0, Set(getVarSpec(v)), Some(multiTerm))
    val merged = Pair(newEq.merge(eq), varsInMultiTerm ++ varsInEq)

    log.debug("eq = " + merged._1)

    val newReferences = varsInMultiTerm -- varsInEq
    val eqsByVar2 = fixReferenceCount(newReferences, eqsByVar, 1)

    pointVarsToEq(eqsByVar2, merged)
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
        pointVarsToEq(m2, newEq)
      })
    )

  private def pointVarsToEq(
    eqsByVar : Map[TypeVar, EqWithRefs], 
    eq : EqWithRefs) : Map[TypeVar, EqWithRefs] =
    (eq._1.s.foldLeft
      (eqsByVar)
      ((m, v) => m + (TypeVar(v.num) -> eq))
    )

  private def typeToMultiTerm(te : TypeExpr) : (MultiTerm,Set[TypeVar]) = {
    te match {
      case UnitTE => Pair(MultiTerm(TypeUtil.UNIT_LABEL, List.empty), Set.empty)
      case BoolTE => Pair(MultiTerm(TypeUtil.BOOL_LABEL, List.empty), Set.empty)
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
      case SolvedObjectTE(objVar, states, stateVar) => {
        val (objVarEq, objVars) = typeToTempEq(VarTE(objVar))
        val (stVarEq, stVars) = typeToTempEq(VarTE(stateVar))
        val vars = objVars ++ stVars
        Pair(MultiTerm(TypeUtil.OBJ_LABEL, List(objVarEq, stVarEq)), vars)
      }
      case VarTE(_) => 
        throw new IllegalArgumentException("type variables cannot be multiterms")
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
          case None => VarTE(TypeVar(getCanonicalVar(eq).num))
          case Some(mt) => multiTermToType(mt)
          }),
          (ty => ty)
        )
    )

  private def multiTermToType(mt : MultiTerm) : TypeExpr = {
    mt.fn match {
      case TypeUtil.UNIT_LABEL => UnitTE
      case TypeUtil.BOOL_LABEL => BoolTE
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
              case Some(x) => Pair(EffectTE(arg, x) :: p._1, None)
            })
          )

        FunTE(effectTypes, retType)
      }
      
      case TypeUtil.OBJ_LABEL => {
        val extractCanonical = (v : Variable) => 
          TypeVar(getCanonicalVar(v.m).num)
        val objVar = extractCanonical(mt.args(0).s.head)
        val stateVar = extractCanonical(mt.args(1).s.head)

        ObjectTE(objVar, stateVar)
      }
    }
  }

  private def varToType(v : Variable) : TypeExpr = {
    varToEqOrType(TypeVar(v.num)) match {
      case Left(meq) => {
        val ty = meq.m match {
          case Some(m) => multiTermToType(m)
          case None => VarTE(TypeVar(getCanonicalVar(meq).num))
        }
        varToEqOrType = varToEqOrType.updated(TypeVar(v.num), Right(ty))
        ty
      }
      case Right(ty) => ty
    }
  }

  /** choose the lowest index type variable as the canonical variable */
  private def getCanonicalVar(meq : MultiEquation) : Variable =
    meq.s.toList.minBy(_.num)
}