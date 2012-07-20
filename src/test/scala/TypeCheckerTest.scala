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

import org.scalatest.FunSuite

class TypeCheckerTest extends FunSuite {

  import TypeChecker._
  import org.kiama.attribution.Attribution.initTree

  def checkType(t : Term, expectedType : Type)
    = assert(t->ttype === expectedType)

  def t(t : Term) = { initTree(t); t }

  def p(name : String, effectType : EffectType) =
    ParamDef(name, Some(effectType))

  def fv(body : Term, params : ParamDef*) =
    FunValue(params, body)

  def ft(retType : Type, paramTypes : EffectType*) =
    FunType(paramTypes, retType)

  def unit = UnitValue()
  def unitt = UnitType()

  val empty = Map.empty[String,Type]

  test("unit term type") {
    checkType(t(unit), unitt)
  }

  test("function term type no params") {
    checkType(t(fv(unit)), ft(unitt))
  }

  test("function term unit param") {
    val body = unit
    val fun = t(fv(body, p("x", (unitt >> unitt))))
    checkType(fun, ft(unitt, unitt >> unitt))
    assert(body->input === Map("x" -> unitt))
    assert(body->output === Map("x" -> unitt))
  }

  test("let term") {
    val value = unit
    val body = unit
    val let = t(LetBind("x", value, body))
    checkType(let, unitt)
    assert(value->input === empty)
    assert(value->output === empty)
    assert(body->input === Map("x" -> unitt))
    assert(body->output === Map("x" -> unitt))
    assert(let->input === empty)
    assert(let->output === empty)
  }

  test("update term") {
    val update = Update("x", fv(unit))
    val value = unit
    val let = t(LetBind("x", value, update))
    checkType(update, unitt)
    assert(update->input === Map("x" -> unitt))
    assert(update->output === Map("x" -> ft(unitt)))
  }
}