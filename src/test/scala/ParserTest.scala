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

/**
 * Non-exhaustive set of sanity check tests for the TS0 parser.
 */
class ParserTest extends FunSuite with Parser {

  def parseTerm(termStr : String) = parseString(term, termStr)
  def checkTerm(termStr : String, expected : Term) = 
    assert(parseTerm(termStr) === Left(expected))

	test("parse unit value") {
		checkTerm("unit", UnitValue())
	}

  test("parse zero argument function") {
    checkTerm("\\().unit", FunValue(Seq(), UnitValue()))
  }

  test("parse multi argument (no types) function") {
    checkTerm(
      "\\(x,y).unit",
      FunValue(
        Seq(ParamDef("x", None), ParamDef("y", None)), 
        UnitValue()
        )
      )
  }

  test("parse function with typed argument") {
    checkTerm(
      "\\(x : Unit >> Unit).unit",
      FunValue(
        Seq(ParamDef("x", Some(EffectType(UnitType(), UnitType())))),
        UnitValue()
        )
      )
  }

  test("parse function with object type argument") {
    val objType = 
      ObjType(Seq(StateSpec("S", Seq(MethodSpec("a", UnitType(), "S")))), "S")

    checkTerm(
      "\\(x : {S{a : Unit >> S}}@S >> {S{a : Unit >> S}}@S).unit",
      FunValue(
        Seq(ParamDef("x", Some(EffectType(objType, objType)))), 
        UnitValue()
      )
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
          StateDef("A", Seq(MethodDef("a", UnitValue(), "B"))),
          StateDef("B", Seq(MethodDef("b", UnitValue(), "A")))
          ),
        "A"
        )
      )
  }

  test("parse triple sequence") {
    checkTerm(
      "unit; unit; unit",
      Sequence(
        UnitValue(),
        Sequence(
          UnitValue(),
          UnitValue()
          )
        )
    )
  }
}