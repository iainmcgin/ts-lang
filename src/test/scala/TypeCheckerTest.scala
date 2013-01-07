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

  import TestUtils._
  import TypeChecker._
  import org.kiama.util.Messaging._

  def checkType(t : Term, expectedType : Type) = {
    resetmessages
    TypeChecker.check(t)
    assert(t->ttype === expectedType)
    if(messagecount > 0) {
      fail("error messages reported:\n" + messages.mkString("\n"))
    }
  }

  def checkInvalid(t : Term, expectedErrors : String*) = {
    resetmessages
    TypeChecker.check(t)
    messagecount should be (expectedErrors.size)

    expectedErrors.foreach(err => {
      if(messages.find(_.message == err).isEmpty) {
        fail("expected error \"" + err + "\" was not found amongst [\n" 
          + messages.map(_.message).mkString("\n") + "\n]")
      }
    })
  }

  val empty = Map.empty[String,Type]

  test("unit value type") {
    checkType(unitv, unitt)
  }

  test("true value type") {
    checkType(truev, boolt)
  }

  test("false value type") {
    checkType(falsev, boolt)
  }

  test("function term type no params") {
    checkType(funv(unitv), funt(unitt))
  }

  test("function term unit param") {
    val body = unitv
    val fun = funv(body, p("x", (unitt >> unitt)))
    checkType(fun, funt(unitt, unitt >> unitt))
    assert(body->input === Map("x" -> unitt))
    assert(body->output === Map("x" -> unitt))
  }

  test("let term") {
    val value = unitv
    val body = unitv
    val let = LetBind("x", value, body)
    checkType(let, unitt)
    assert(value->input === empty)
    assert(value->output === empty)
    assert(body->input === Map("x" -> unitt))
    assert(body->output === Map("x" -> unitt))
    assert(let->input === empty)
    assert(let->output === empty)
  }

  test("invalid parameter type") {
    val application = FunCall("f", Seq("x"))
    val letParam = LetBind("x", unitv, application)
    val funBody = FunCall("a", Seq.empty)
    val fun = funv(funBody, p("a", funt(unitt) >> funt(unitt)))
    val letFun = LetBind("f", fun, letParam)

    checkInvalid(letFun, 
      "parameter x is not of the required type for function f: expected " 
        + funt(unitt) + ", but found " + unitt
    )
  }

  test("if-then-else with true value branches") {
    val ift = If(truev, truev, truev)
    checkType(ift, boolt)
  }

  test("if-then-else with different branch effects") {
    val xObjStates = 
      Seq(
        StateDef("S1", 
          Seq(MethodDef("m", unitv, "S2"), 
              MethodDef("n", truev, "S2"))),
        StateDef("S2", Seq.empty)
      )

    val xObjTypeStates =
      Seq(
        StateSpec("S1",
          Seq(
            MethodSpec("m", unitt, "S2"),
            MethodSpec("n", boolt, "S2")
          )),
        StateSpec("S2", Seq.empty)
      )

    val xObjStart = ObjValue(xObjStates, "S1")
    val ift = If(truev, MethCall("x", "m"), MethCall("x", "n"))
    val let = LetBind("x", xObjStart, ift)

    checkType(let, topt)
    assert(ift.whenTrue->output === Map("x" -> ObjType(xObjTypeStates, "S2")))
    assert(ift.whenFalse->output === Map("x" -> ObjType(xObjTypeStates, "S2")))
    assert(ift->output === Map("x" -> ObjType(xObjTypeStates, "S2")))
  }
}