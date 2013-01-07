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

package uk.ac.gla.dcs.ts.sm

import org.scalatest.FunSuite
import org.scalatest.matchers.ShouldMatchers

import StateGraphUtils._

class PermuteTest extends FunSuite with ShouldMatchers {

  val empty = Set.empty[Int]
  val emptyPairs = Set.empty[Set[(Int,Int)]]

  test("empty sets") {
    (emptyPairs) should equal (permuteMatch(empty, empty))
  }

  test("mismatched set sizes") {
    (emptyPairs) should equal (permuteMatch(Set(1), Set()))
  }

  test("single value sets") {
    (Set(Set(1 -> 2))) should equal (permuteMatch(Set(1), Set(2)))
  }

  test("two value sets") {
    val expected = 
      Set(Set(1 -> 3, 2 -> 4),
          Set(1 -> 4, 2 -> 3))

    val actual = permuteMatch(Set(1,2), Set(3,4))
    (expected) should equal (actual)
  }

  test("three value sets") {
    val expected =
      Set(Set(1 -> 4, 2 -> 5, 3 -> 6),
          Set(1 -> 4, 2 -> 6, 3 -> 5),
          Set(1 -> 5, 2 -> 4, 3 -> 6),
          Set(1 -> 5, 2 -> 6, 3 -> 4),
          Set(1 -> 6, 2 -> 4, 3 -> 5),
          Set(1 -> 6, 2 -> 5, 3 -> 4))

    val actual = permuteMatch(Set(1,2,3), Set(4,5,6))
    (expected) should equal (actual)
  }
}