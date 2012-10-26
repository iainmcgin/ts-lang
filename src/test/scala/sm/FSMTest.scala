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

import uk.ac.gla.dcs.ts.UnitTE

import scalax.collection.Graph
import scalax.collection.GraphPredef._
import scalax.collection.GraphEdge._

import scalax.collection.edge.LDiEdge
import scalax.collection.edge.Implicits._

import org.scalatest.FunSuite
import org.scalatest.matchers.ShouldMatchers

class FSMTest extends FunSuite with ShouldMatchers {

  def m(s : String) = Method(s, UnitTE)

  val s = new StateGenerator()

  val A = State("A")
  val B = State("B")
  val C = State("C")
  val D = State("D")
  val E = State("E")
  val X = State("X")

  val ma = Method("a", UnitTE)
  val mb = Method("b", UnitTE)
  val mc = Method("c", UnitTE)
  val md = Method("d", UnitTE)

  def aOrB = StateMachine(Graph(A ~> B by ma, A ~> C by mb), A, Set(B, C))
  def aOrC = StateMachine(Graph(A ~> B by ma, A ~> C by mc), A, Set(B, C))
  def cOrD = StateMachine(Graph(A ~> B by mc, A ~> C by md), A, Set(B, C))
  def aStar = StateMachine(Graph(A ~> A by ma), A, Set(A))
  def abStar = StateMachine(Graph(A ~> B by ma, B ~> A by mb), A, Set(A))
  def aOrBaStar = StateMachine(
    Graph(A ~> A by ma, A ~> B by mb, B ~> A by ma),
    A, Set(A)
  )
  def abStarStandard = StateMachine(
    Graph(A ~> C by ma, B ~> C by ma, C ~> B by mb),
    A, Set(A,B)
  )

  def checkEquiv(expected : StateMachine, actual : StateMachine) {
    ((expected findInconsistency actual)
      foreach (err => fail("expected machine " + expected + 
                           " was not alpha equivalent to " + actual +
                           ": " + err))
    )
  }

  test("intersection with self is a no-op") {
    val sm = aOrB
    val res = sm intersection sm
    (res) should be theSameInstanceAs (sm)
  }

  test("union with self is a no-op") {
    val sm = emptySM

    val res = sm union sm
    res should be theSameInstanceAs (sm)
  }

  test("a|b ∩ a|c = a") {
    val res = aOrB intersection aOrC
    val expected = StateMachine(Graph(A ~> B by ma), A, Set(B))
    checkEquiv(expected, res)
  }

  test("a|b ∩ c|d = ∅") {
    val res = aOrB intersection cOrD
    checkEquiv(emptySM, res)
  }

  test("(ab)* ∩ (a|ba)* = ∅") {
    val res = abStar intersection(aOrBaStar, "YYYYY")
    checkEquiv(emptySM, res)
  }

  test("(abc)* ∩ ((ab)|c)* = (abc)*") {
    val sm1 = StateMachine(
      Graph(
        A ~> B by ma,
        B ~> C by mb,
        C ~> A by mc
      ),
      A,
      Set(A)
    )

    val sm2 = StateMachine(
      Graph(
        A ~> B by ma,
        B ~> A by mb,
        A ~> A by mc
      ),
      A,
      Set(A)
    )

    checkEquiv(sm1, sm1 intersection sm2)
  }

  test("a|b ∪ a|c = a|b|c") {
    val res = aOrB union aOrC
    val expected = StateMachine(
      Graph(
        A ~> B by ma,
        A ~> C by mb,
        A ~> D by mc
      ),
      A,
      Set(B,C,D)
    )

    checkEquiv(expected, res)
  }

  test("a|b ∪ c|d = a|b|c|d") {
    val res = aOrB union cOrD
    val expected = StateMachine(
      Graph(A ~> B by ma, A ~> C by mb, A ~> D by mc, A ~> E by md),
      A,
      Set(B,C,D,E)
    )
  }

  test("a*bc* ∪ (ab*)|c = aaa*bc*|abbb*|abcc*|bc*|c") {
    val `a*bc*` = StateMachine(
      Graph(A ~> A by ma, A ~> B by mb, B ~> B by mc),
      A,
      Set(B)
    )

    val `(ab*)|c` = StateMachine(
      Graph(A ~> B by ma, B ~> B by mb, A ~> C by mc),
      A,
      Set(B, C)
    )

    val F = State("F")
    val G = State("G")
    val expected = StateMachine(
      Graph(
        A ~> B by ma, A ~> C by mb, A ~> D by mc,
        B ~> E by ma, B ~> F by mb,
        C ~> C by mc,
        E ~> E by ma, E ~> C by mb,
        F ~> G by mb, F ~> C by mc,
        G ~> G by mb
        ),
      A,
      Set(B, C, D, F, G)
    )

    val res = `a*bc*` union `(ab*)|c`
    checkEquiv(expected, res)
  }

  test("isStandardized on example machines") {
    (aOrB.isStandardized) should be (true)
    (aOrC.isStandardized) should be (true)
    (cOrD.isStandardized) should be (true)
    (abStar.isStandardized) should be (false)
    (aOrBaStar.isStandardized) should be (false)
  }

  test("standardize abStar") {
    val res = abStar.standardize()
    checkEquiv(abStarStandard, res)
  }

  test("standardize already standardized FSM is a no-op") {
    val sm = abStarStandard
    val res = sm.standardize()
    res should be theSameInstanceAs (sm)
  }

  test("standardize machine with multiple edges out of entry state") {
    val sm = StateMachine(
      Graph(A ~> A by ma, A ~> B by mb, A ~> C by mc, A ~> A by md),
      A,
      Set(A,B,C))

    val expected = StateMachine(
      Graph(
        // new edges
        D ~> A by ma, D ~> B by mb, D ~> C by mc, D ~> A by md,
        // original
        A ~> A by ma, A ~> B by mb, A ~> C by mc, A ~> A by md
        ),
      D,
      Set(A,B,C,D)
      )

    checkEquiv(expected, sm.standardize())
  }

  test("a|b then a|c = aa|ac|ba|bc") {
    val expected = StateMachine(
      Graph(A ~> B by ma, A ~> C by mb, 
        B ~> D by ma, B ~> E by mc,
        C ~> D by ma, C ~> E by mc),
      A,
      Set(D,E)
    )

    checkEquiv(expected, aOrB then aOrC)
  }

  test("a|b then a* = aaa*|baa*") {
    val expected = StateMachine(
      Graph(A ~> B by ma, A ~> C by mb,
        B ~> D by ma,
        C ~> D by ma,
        D ~> D by ma),
      A,
      Set(B, C, D)
    )

    val res = aOrB then aStar
    checkEquiv(expected, aOrB then aStar)
  }

  test("(ab)* then (a|ba)*") {
    val expected = StateMachine(
      Graph(
        A ~> B by ma, A ~> D by mb,
        B ~> C by ma, B ~> A by mb,
        C ~> C by ma, C ~> D by mb,
        D ~> C by ma
      ),
      A,
      Set(A,B,C)
    )

    checkEquiv(expected, abStar then aOrBaStar)
  }

  test("(ab)* then (ab)* = (ab)*") {
    checkEquiv(abStar, abStar then abStar)
  }

  test("(ab)* then a*") {
    val expected = StateMachine(
      Graph(
        A ~> B by ma,
        B ~> A by mb,
        B ~> C by ma,
        C ~> C by ma
      ),
      A,
      Set(A,B,C))
    checkEquiv(expected, abStar then aStar)
  }
}