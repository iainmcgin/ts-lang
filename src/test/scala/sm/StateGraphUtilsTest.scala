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

import uk.ac.gla.dcs.ts._

import scalax.collection.GraphPredef._
import scalax.collection.Graph

import org.scalatest.FunSuite
import org.scalatest.matchers.ShouldMatchers

class StateGraphUtilsTest extends FunSuite with ShouldMatchers {

  import StateGraphUtils._

  def s(name : String) = State(name)

  def m(name : String) = Method(name, UnitTE)
  def m(name : String, te : TypeExpr) = Method(name, te)

  def checkEquiv(
      expected : StateGraph, 
      expectedStart : String, 
      actual : StateGraph,
      actualStart : String) {
    val hasInconsistency = findInconsistency(
      expected, 
      State(expectedStart), 
      actual, 
      State(actualStart))

    if(hasInconsistency.isLeft) {
      fail("expected graph " + expected + 
           " was not alpha equivalent to " + actual +
           ": " + hasInconsistency.left)
    }
  }

  test("includeInto with no conflicting names") {
    val g1 : StateGraph = Graph(
      s("A") ~> s("B") by m("a"),
      s("B") ~> s("C") by m("b")
    )

    val g2 : StateGraph = Graph(
      s("D") ~> s("E") by m("a"),
      s("E") ~> s("E") by m("b")
    )

    val expected : StateGraph = Graph(
      s("A") ~> s("B") by m("a"),
      s("B") ~> s("C") by m("b"),
      s("D") ~> s("E") by m("a"),
      s("E") ~> s("E") by m("b")
    )

    val (resGraph,g2Equiv) = includeInto(g1, g2)

    (resGraph) should equal (expected)
  }

  test("includeInto with conflicting names") {
    val g1 : StateGraph = Graph(
      s("A") ~> s("B") by m("a"),
      s("B") ~> s("C") by m("b")
    )

    val g2 : StateGraph = Graph(
      s("A") ~> s("B") by m("b"),
      s("B") ~> s("D") by m("a")
    )

    val (resGraph,g2Equiv) = includeInto(g1, g2)

    // A and B should be relabeled, D is fine
    val newA = g2Equiv.findUniqueRightEquivOrFail("A")
    val newB = g2Equiv.findUniqueRightEquivOrFail("B")

    (newA) should not equal ("A")
    (newA) should not equal ("B")
    (newA) should not equal ("C")

    val expected : StateGraph = Graph(
      s("A") ~> s("B") by m("a"),
      s("B") ~> s("C") by m("b"),
      s(newA) ~> s(newB) by m("b"),
      s(newB) ~> s("D") by m("a")
    )

    (resGraph) should equal (expected)
  }

  test("trimToPath has no effect on single state graph with no edges") {
    val g : StateGraph = Graph(s("A"))

    (trimToPath(g, "A", Set("A"))) should equal (g)
  }

  test("trimToPath has no effect on single state graph with cyclic edges") {
    val g : StateGraph = Graph(s("A") ~> s("A") by m("a"))

    (trimToPath(g, "A", Set("A"))) should equal (g)
  }

  test("trimToPath has no effect on clique") {
    val g : StateGraph = Graph(
      s("A") ~> s("B") by m("a"),
      s("B") ~> s("A") by m("b")
    )

    (trimToPath(g, "A", Set("B"))) should equal (g)
  }

  test("trimToPath removes irrelevant forward path") {
    val g : StateGraph = Graph(
      s("A") ~> s("A") by m("a"),
      s("A") ~> s("B") by m("b"),
      s("B") ~> s("B") by m("b")
    )

    val expected : StateGraph = Graph(
      s("A") ~> s("A") by m("a")
    )

    (trimToPath(g, "A", Set("A"))) should equal (expected)
  }

  test("trimToPath keeps relevant forward paths") {
    val g : StateGraph = Graph(
      s("A") ~> s("A") by m("a"),
      s("A") ~> s("B") by m("b"),
      s("B") ~> s("B") by m("b"),
      s("B") ~> s("A") by m("a"),
      s("A") ~> s("C") by m("c")
    )

    val expected : StateGraph = Graph(
      s("A") ~> s("A") by m("a"),
      s("A") ~> s("B") by m("b"),
      s("B") ~> s("B") by m("b"),
      s("B") ~> s("A") by m("a")
    )

    (trimToPath(g, "A", Set("A"))) should equal (expected)
  }

  test("connect states with no cycles, no common paths") {
    val g : StateGraph = Graph(
      s("A") ~> s("B") by m("a"),
      s("C") ~> s("D") by m("b")
    )

    val (actual, _, equiv) = connect(g, Set(s("A"), s("C")))

    val aEquiv = equiv.findUniqueRightEquivOrFail("A")

    val expected : StateGraph = Graph(
      s(aEquiv) ~> s("B") by m("a"), 
      s(aEquiv) ~> s("D") by m("b")
    )

    (actual) should equal (expected)
  }

  test("connect states with no cycles, common paths") {
    val g : StateGraph = Graph(
      s("A") ~> s("B") by m("a"),
      s("B") ~> s("C") by m("b"),
      s("D") ~> s("E") by m("a"),
      s("E") ~> s("F") by m("c")
    )

    val (actual, _, equiv) = connect(g, Set(s("A"), s("D")))

    val aEquiv = equiv.findUniqueRightEquivOrFail("A")
    val bEquivs = equiv.findRightEquivsOrFail("B")  

    (bEquivs) should have size (2)
    (bEquivs) should contain ("B")

    val bEquiv = (bEquivs - "B").head

    val expected : StateGraph = Graph(
      s(aEquiv) ~> s(bEquiv) by m("a"),
      s(bEquiv) ~> s("C") by m("b"),
      s(bEquiv) ~> s("F") by m("c"),
      // the following transitions remain, they cannot be
      // determined to be redundant in the context of this operation
      s("B") ~> s("C") by m("b"),
      s("E") ~> s("F") by m("c")
    )

    (actual) should equal (expected)
  }

  test("connect simple cycles") {
    val g : StateGraph = Graph(
      s("A") ~> s("A") by m("a"),
      s("B") ~> s("B") by m("b")
    )

    val (actual, _, stateEquiv) = connect(g, Set(s("A"), s("B")))

    println(actual)
    println(stateEquiv)

    val aEquiv = stateEquiv.findUniqueRightEquivOrFail("A")

    val expected : StateGraph = Graph(
      s(aEquiv) ~> s(aEquiv) by m("a"),
      s(aEquiv) ~> s(aEquiv) by m("b")
    )

    (actual) should equal (expected)
  }

  test("connect indirect cycles") {
    val g : StateGraph = Graph(
      s("A") ~> s("B") by m("a"),
      s("B") ~> s("A") by m("b"),
      s("C") ~> s("D") by m("c"),
      s("D") ~> s("C") by m("d")
    )

    val (actual, _, stateEquiv) = connect(g, Set(s("A"), s("C")))

    val aEquiv = stateEquiv.findUniqueRightEquivOrFail("A")

    val expected : StateGraph = Graph(
      s(aEquiv) ~> s("B") by m("a"),
      s("B") ~> s(aEquiv) by m("b"),
      s(aEquiv) ~> s("D") by m("c"),
      s("D") ~> s(aEquiv) by m("d")
    )

    (actual) should equal (expected)
  }

  test("internalIntersection, no shared paths, no cycles") {
    val g : StateGraph = Graph(
      s("A") ~> s("B") by m("a"),
      s("C") ~> s("D") by m("d")
    )

    val (res, _, equiv) = internalIntersection(g, Set("A", "C"))

    val aEquiv = equiv.findUniqueRightEquivOrFail("A")
    (aEquiv) should equal (equiv.findUniqueRightEquivOrFail("C"))
    (equiv.findRightEquivs("B")) should be ('empty)
    (equiv.findRightEquivs("D")) should be ('empty)

    val expected : StateGraph = Graph(s(aEquiv))

    (res) should equal (expected)
  }

  test("internalIntersection, shared paths, no cycles") {
    val g : StateGraph = Graph(
      s("A") ~> s("B") by m("a"),
      s("B") ~> s("C") by m("b"),
      s("B") ~> s("D") by m("c"),

      s("E") ~> s("F") by m("a"),
      s("F") ~> s("G") by m("c"),
      s("G") ~> s("H") by m("a")
    )

    val (actual, actualStart, equiv) = internalIntersection(g, Set("A", "E"))

    val aEquiv = equiv.findUniqueRightEquivOrFail("A")
    (aEquiv) should equal (actualStart)

    val bEquiv = equiv.findUniqueRightEquivOrFail("B")
    val dEquiv = equiv.findUniqueRightEquivOrFail("D")

    val expected : StateGraph = Graph(
      s(actualStart) ~> s(bEquiv) by m("a"),
      s(bEquiv) ~> s(dEquiv) by m("c")
    )

    (actual) should equal (expected)

    (aEquiv) should equal (equiv.findUniqueRightEquivOrFail("E"))
    (bEquiv) should equal (equiv.findUniqueRightEquivOrFail("F"))
    (dEquiv) should equal (equiv.findUniqueRightEquivOrFail("G"))
    (equiv.findRightEquivs("C")) should be ('empty)
    (equiv.findRightEquivs("H")) should be ('empty)
  }

}