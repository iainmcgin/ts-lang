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

class ObjTypeTest extends FunSuite with ShouldMatchers {

  val o1states = Seq(
      StateSpec("A", Seq(
        MethodSpec("m", unitt, "A"),
        MethodSpec("n", boolt, "B"),
        MethodSpec("g", funt(boolt), "B")
      )),
      StateSpec("B", Seq(
        MethodSpec("m", boolt, "B"),
        MethodSpec("f", unitt, "A"),
        MethodSpec("g", funt(unitt), "B")
      ))
    )

  test("return type with single known current state") {
    val obj = ObjType(o1states, Set("A"))
    (obj.retType("m")) should be (Some(unitt))
    (obj.retType("n")) should be (Some(boolt))
    (obj.retType("f")) should be (None)
  }

  test("return type with state set") {
    val obj = ObjType(o1states, Set("A", "B"))
    (obj.retType("m")) should be (Some(topt))
    (obj.retType("n")) should be (None)
    (obj.retType("f")) should be (None)
    (obj.retType("g")) should be (Some(funt(topt)))
  }

  test("nextStateSet with single known current state") {
    val obj = ObjType(o1states, Set("B"))
    (obj.nextStateSet("m")) should be (Some(Set("B")))
    (obj.nextStateSet("n")) should be (None)
    (obj.nextStateSet("f")) should be (Some(Set("A")))
    (obj.nextStateSet("g")) should be (Some(Set("B")))
  }

  test("nextStateSet with state set") {
    val obj = ObjType(o1states, Set("A", "B"))
    (obj.nextStateSet("m")) should be (Some(Set("A", "B")))
    (obj.nextStateSet("n")) should be (None)
    (obj.nextStateSet("f")) should be (None)
    (obj.nextStateSet("g")) should be (Some(Set("B")))
  }

}