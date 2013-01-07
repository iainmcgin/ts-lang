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

  def parseTest(termStr : String, expected : => Term) =
    test("parse " + termStr) { 
      assert(parse(termStr) === Left(expected))
    }

  // basic values
	parseTest("unit", unitv)
  parseTest("true", truev)
  parseTest("false", falsev)

  // function values
  parseTest("\\().unit", funv(unitv))
  parseTest("\\(x,y).unit", funv(unitv, p("x"), p("y")))
  parseTest("\\(x : Unit >> Unit).unit", funv(unitv, p("x", unitt >> unitt)))
  parseTest("\\(x : Bool >> Bool).unit", funv(unitv, p("x", boolt >> boolt)))
  parseTest("\\(x : Top >> Top).unit", funv(unitv, p("x", topt >> topt)))
  parseTest("\\(x : {S{a : Unit >> S}}@S >> {S{a : Unit >> S}}@S).unit", {
    val objType = 
      ObjType(Seq(StateSpec("S", Seq(MethodSpec("a", unitt, "S")))), "S")
    funv(unitv, p("x", objType >> objType))
  })

  // object values
  parseTest("[S{}]@S", ObjValue(Seq(StateDef("S", Seq())), "S"))
  parseTest("[ A{ a=(unit,B) } B { b=(unit,A) } ]@A",
      ObjValue(
        Seq(StateDef("A", Seq(MethodDef("a", unitv, "B"))),
            StateDef("B", Seq(MethodDef("b", unitv, "A")))),
        "A"
        )
      )

  // sequences
  parseTest("unit; unit; unit", seq(unitv, unitv, unitv))

  // conditionals
  parseTest("if true then unit else unit", If(truev, unitv, unitv))
  parseTest("if true then (x.m; y.n) else (y.n; x.m)",
      If(truev, seq(MethCall("x", "m"), MethCall("y", "n")), 
                seq(MethCall("y", "n"), MethCall("x", "m"))))

  // let-bindings
  parseTest("let x = unit in true", LetBind("x", unitv, truev))
  parseTest("let x = unit in let y = unit in true",
    LetBind("x", unitv, LetBind("y", unitv, truev)))
  parseTest("let x = (let y = unit in unit) in let z = true in false",
    LetBind("x", LetBind("y", unitv, unitv), LetBind("z", truev, falsev)))

  // method calls
  parseTest("x.m", MethCall("x", "m"))
  parseTest("y.y", MethCall("y", "y"))

  // function calls
  parseTest("f()", FunCall("f", Seq.empty))
  parseTest("x(a, b, c)", FunCall("x", Seq("a", "b", "c")))
  parseTest("f(f)", FunCall("f", Seq("f"))) 
    //        ^  semantically invalid but syntactically fine

  // parsing precedence of seq and let binding
  parseTest("let x = \\().unit in x() ; unit ; true",
    LetBind("x", funv(unitv), seq(FunCall("x", Seq.empty), unitv, truev)))
  parseTest("(let x = unit in unit) ; unit",
    seq(LetBind("x", unitv, unitv), unitv))
}