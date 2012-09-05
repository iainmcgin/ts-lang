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

import org.scalatest.FunSuite
import org.scalatest.matchers.ShouldMatchers

class TypeCheckerTest extends FunSuite with ShouldMatchers {

  import TypeChecker._
  import org.kiama.util.Messaging._

  def checkType(t : Term, expectedType : Type) = {
    TypeChecker.check(t)
    assert(t->ttype === expectedType)
    assert(messagecount === 0)
  }

  def checkInvalid(t : Term, expectedErrors : Seq[String]) = {
    TypeChecker.check(t)
    messagecount should be (expectedErrors.size)

    expectedErrors.foreach(err => {
      if(messages.find(_.message == err).isEmpty) {
        fail("expected error \"" + err + "\" was not found amongst [\n" 
          + messages.map(_.message).mkString("\n") + "\n]")
      }
    })
  }

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
    checkType(unit, unitt)
  }

  test("function term type no params") {
    checkType(fv(unit), ft(unitt))
  }

  test("function term unit param") {
    val body = unit
    val fun = fv(body, p("x", (unitt >> unitt)))
    checkType(fun, ft(unitt, unitt >> unitt))
    assert(body->input === Map("x" -> unitt))
    assert(body->output === Map("x" -> unitt))
  }

  test("let term") {
    val value = unit
    val body = unit
    val let = LetBind("x", value, body)
    checkType(let, unitt)
    assert(value->input === empty)
    assert(value->output === empty)
    assert(body->input === Map("x" -> unitt))
    assert(body->output === Map("x" -> unitt))
    assert(let->input === empty)
    assert(let->output === empty)
  }

  test("update term") {
    val updateExpr = fv(unit)
    val update = Update("x", updateExpr)
    val value = unit
    val let = LetBind("x", value, update)
    checkType(let, unitt)
    assert(let->input === Map.empty)
    assert(let->output === Map.empty)
    assert(value->ttype === unitt)
    assert(updateExpr->input === Map.empty)
    assert(updateExpr->ttype == ft(unitt))
    assert(updateExpr->output === Map.empty)
    assert(update->input === Map("x" -> unitt))
    assert(update->output === Map("x" -> ft(unitt)))
  }

  test("invalid parameter type") {
    val application = FunCall("f", Seq("x"))
    val letParam = LetBind("x", unit, application)
    val funBody = FunCall("a", Seq.empty)
    val fun = fv(funBody, p("a", ft(unitt) >> ft(unitt)))
    val letFun = LetBind("f", fun, letParam)

    checkInvalid(letFun, 
      Seq("parameter x is not of the required type for function f: expected " 
        + ft(unitt) + ", but found " + unitt)
    )
  }
}