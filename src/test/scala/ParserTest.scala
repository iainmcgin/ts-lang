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

/**
 * Non-exhaustive set of sanity check tests for the TS language parser.
 */
class ParserTest extends FunSuite {

  import TestUtils._

  def checkTerm(termStr : String, expected : Term) = 
    assert(parse(termStr) === Left(expected))

	test("parse unit value") {
		checkTerm("unit", unitv)
	}

  test("parse zero argument function") {
    checkTerm("\\().unit", funv(unitv))
  }

  test("parse multi argument (no types) function") {
    checkTerm(
      "\\(x,y).unit",
      funv(unitv, p("x"), p("y"))
    )
  }

  test("parse function with typed argument") {
    checkTerm(
      "\\(x : Unit >> Unit).unit",
      funv(unitv, p("x", unitt >> unitt))
    )
  }

  test("parse function with object type argument") {
    val objType = 
      ObjType(Seq(StateSpec("S", Seq(MethodSpec("a", unitt, "S")))), "S")

    checkTerm(
      "\\(x : {S{a : Unit >> S}}@S >> {S{a : Unit >> S}}@S).unit",
      funv(unitv, p("x", objType >> objType))
    )
  }

  test("parse minimal object value") {
    checkTerm(
      "[S{}]@S",
      ObjValue(
        Seq(StateDef("S", Seq())),
        "S"
        )
      )
  }

  test("parse object value for pattern (ab)*") {
    checkTerm(
      "[ A{ a=(unit,B) } B { b=(unit,A) } ]@A",
      ObjValue(
        Seq(
          StateDef("A", Seq(MethodDef("a", unitv, "B"))),
          StateDef("B", Seq(MethodDef("b", unitv, "A")))
          ),
        "A"
        )
      )
  }

  test("parse triple sequence") {
    checkTerm(
      "unit; unit; unit",
      seq(unitv, unitv, unitv)
    )
  }

  test("parse true literal") {
    checkTerm("true", truev)
  }

  test("parse false literal") {
    checkTerm("false", falsev)
  }

  test("parse simple if-then-else") {
    checkTerm("if true then unit else unit", If(truev, unitv, unitv))
  }

  test("parse if-then-else with sequences in branches") {
    checkTerm("if true then (x := unit; y := unit) else (y := unit; x := unit)",
      If(truev, seq("x" := unitv, "y" := unitv), seq("y" := unitv, "x" := unitv))
    )
  }
}