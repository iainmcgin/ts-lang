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

import sm._

import scalax.collection.GraphPredef._
import scalax.collection.Graph
import scalax.collection.GraphEdge._

object TestUtils {

  /* parser utility */
  object parse extends Parser {
    def apply(termStr : String) = parseString(term, termStr)
  }

  /* term short-hand creation */
  def unitv = { UnitValue() }
  def truev = { TrueValue() }
  def falsev = { FalseValue() }
  def funv(body : Term, params : ParamDef*) = FunValue(params, body)
  def p(name : String, effectType : EffectType) = 
    ParamDef(name, Some(effectType))
  def p(name : String) = ParamDef(name, None)
  def seq(ts : Term*) : Term = {
    ts.reduceRight((t1, t2) => Sequence(t1, t2))
  }
  def up(name : String, t : Term) = Update(name, t)

  /* type short-hand creation */
  def unitt = { UnitType() }
  def boolt = { BoolType() }
  def funt(retType : Type, paramTypes : EffectType*) =
    FunType(paramTypes, retType)


  /* unification related helpers */
  val unitMT = MultiTerm(0, List.empty)

  def v(tv : TypeVar) = Variable(tv.v, null)
  def vset(tvs : TypeVar*) = Set(tvs.map(tv => v(tv)) :_*)


  /* type inference related helpers */
  implicit def intToVarTE(i : Int) = VarTE(TypeVar(i))
  implicit def intToTypeVar(i : Int) = TypeVar(i)

  case class UpdateHelper(varName : String) {
    def :=(t : Term) = Update(varName, t)
  }

  implicit def strToUpdateHelper(str : String) = UpdateHelper(str)

  /* state and method creation helpers */

  def s(name : String) = State(name)
  def m(name : String) = Method(name, UnitTE)
  def m(name : String, typ : TypeExpr) = Method(name, UnitTE)

  def methodGraph(m : Method) : (StateGraph, String, String) = 
    (Graph(s("A") ~> s("B") by m), "A", "B")

}

class TestUtilsTest extends org.scalatest.FunSuite {

  import TestUtils._

  test("single term to seq returns term") {
    assert(unitv === seq(unitv))
  }

  test("seq building, 4 terms") {
    def seq2(a : Term, b : Term) = Sequence(a, b)
    val t1 = unitv
    val t2 = funv(unitv)
    val t3 = funv(unitv, p("x"))
    val t4 = funv(unitv, p("x"), p("y"))
    val s = seq(t1, t2, t3, t4)

    assert(seq2(t1, seq2(t2, seq2(t3, t4))) === s)
  }
}