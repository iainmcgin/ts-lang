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
import TestUtils._

class TypeOpTest extends FunSuite with ShouldMatchers {


  def opTest(expected : Type, 
    t1 : Type, 
    t2 : Type,
    opStr : String,
    op : (Type, Type) => Option[Type]) {

    test("%s %s %s = %s" format(t1, opStr, t2, expected)) {
      op(t1, t2) match {
        case Some(t) => assert(expected === t)
        case None => fail("no result")
      }
    }
  }

  def opFailTest(
    t1 : Type, 
    t2 : Type, 
    opStr : String, 
    op : (Type, Type) => Option[Type]) {
    test("%s %s %s should be undefined" format(t1, opStr, t2)) {
      op(t1, t2).foreach(res => 
        fail("%s %s %s = %s" format (t1, opStr, t2, res))
      )
    }
  }

  val joinOp = (x : Type, y : Type) => Option(x.join(y))
  val meetOp = (_ : Type).meet((_ : Type))

  def testJoin(expected : Type, t1 : Type, t2 : Type) {
    opTest(expected, t1, t2, "∨", joinOp)
  }

  def testCannotJoin(t1 : Type, t2 : Type) {
    opFailTest(t1, t2, "∨", joinOp)
  }

  def testMeet(expected : Type, t1 : Type, t2 : Type) {
    opTest(expected, t1, t2, "∧", meetOp)
  }

  def testCannotMeet(t1 : Type, t2 : Type) {
    opFailTest(t1, t2, "∧", meetOp)
  }

  def testIncompatible(t1 : Type, t2 : Type) {
    testJoin(TopType(), t1, t2)
    testCannotMeet(t1, t2)
  }

  val emptyObj = ObjType(Seq(StateSpec("S1", Seq.empty)), "S1")

  // obvious kind incompatibilities
  testIncompatible(unitt, boolt)
  testIncompatible(unitt, funt(unitt))
  testIncompatible(unitt, emptyObj)
  testIncompatible(boolt, funt(unitt))
  testIncompatible(boolt, emptyObj)
  testIncompatible(funt(unitt), emptyObj)

  // mismatched parameter lengths
  testIncompatible(funt(unitt), funt(unitt, unitt >> unitt))

  // incompatible return types
  testIncompatible(funt(unitt), funt(boolt))

  // incompatible output type on effect
  testIncompatible(funt(unitt, unitt >> unitt), funt(unitt, unitt >> boolt))

  // incompatible input type on effect
  testIncompatible(funt(unitt, unitt >> unitt), funt(unitt, boolt >> unitt))

  // join with self
  testJoin(unitt, unitt, unitt)
  testJoin(boolt, boolt, boolt)
  testJoin(funt(unitt), funt(unitt), funt(unitt))

  testJoin(topt, unitt, boolt)

}