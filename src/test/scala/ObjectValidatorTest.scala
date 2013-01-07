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

import org.kiama.attribution.Attribution.initTree
import org.kiama.attribution.Attributable
import org.scalatest.FunSuite
import ObjectValidator._

class ObjectValidatorTest extends FunSuite with Parser {

  def parseTerm(termStr : String) = parseString(term, termStr)

  def objTest(termStr : String, errors : Seq[ObjValidationError]) = 
    test(termStr + " is " + (if (errors.isEmpty) "valid" else "invalid")) {
      val result = parseTerm(termStr)
      
      result match {
        case Left(t) => {
          initTree(t)
          val foundErrors = allObjectErrors(t)
          assert(foundErrors.length === errors.length)
          errors.foreach(e => assert(foundErrors.contains(e)))
        }
        case Right(_) => fail("unable to parse term " + termStr)
      }
    }

  def validObjTest(termStr : String) = 
    objTest(termStr, Seq.empty)

  def invalidObjTest(
    termStr : String, 
    expectedErrors : ObjValidationError*) =
    objTest(termStr, expectedErrors)

  validObjTest("[ S {} ]@S")
  validObjTest("[ S{ m = (unit, S) } ]@S")
  validObjTest("[ S { m = (unit, S2) } S2 {} ]@S2")

  invalidObjTest("[ S2 {} ]@S", MissingState("S")())
  invalidObjTest("[ S { m = (unit, S2) } ]@S", MissingState("S2")())

  invalidObjTest(
    "let x = [ S { m = (unit, S2) } ]@S in [ A { n = (unit, A) } ]@B",
    MissingState("S2")(), MissingState("B")())

  invalidObjTest("[ S { m = (unit, S) ; m = (unit, S2) } ]@S",
    MissingState("S2")(), DuplicateMethod("S", "m")()
    )

  invalidObjTest("[ S {} S {}]@S", DuplicateState("S")())

  // invalid object types
  def invalidObjTypeTest(typeStr : String, expectedErrors : ObjValidationError*) =
    objTest("\\(x : " + typeStr + " >> {S{}}@S).unit", expectedErrors)

  invalidObjTypeTest("{ S{} S{} }@S", DuplicateState("S")())
  invalidObjTypeTest("{ S { m : Unit => S2 } }@S", MissingState("S2")())
  invalidObjTypeTest("{ S {} }@S2", MissingState("S2")())
  invalidObjTypeTest("{ S { m : Unit => S ; m : Unit => S2 } S2 {}}@S", 
    DuplicateMethod("S", "m")())
}