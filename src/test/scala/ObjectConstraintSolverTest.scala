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

import sm._
import StateGraphUtils._

import scalax.collection.GraphPredef._
import scalax.collection.Graph

import org.scalatest.FunSuite
import org.scalatest.matchers.ShouldMatchers
import TestUtils._

class ObjectConstraintSolverTest extends FunSuite with ShouldMatchers {

  implicit def intToTypeVar(i : Int) : TypeVar = TypeVar(i)
  def tvp(tv1 : Int, tv2 : Int) = Pair(TypeVar(tv1), TypeVar(tv2))

  def getSolutionsOrFail
      (objIds : Range)
      (implicit solver : ObjectConstraintSolver) 
      : Seq[SolvedObjectTE] =
    getSolutionsOrFail(objIds map (obj(_)))

  def getSolutionsOrFail
    (objects : Seq[ObjectTE])
    (implicit solver : ObjectConstraintSolver) : Seq[SolvedObjectTE] = {

    objects map { o =>
      val soln = solver.getSolutionFor(o)
      assert(soln.isDefined, "solution for " + o + " not found")
      soln.get
    }
  }

  def obj(id : Int) = ObjectTE(objVar(id), stVar(id))
  def objVar(id : Int) = id*2
  def stVar(id : Int) = id*2+1

  test("resolve direct equalities") {
    val constraints = Seq(
      obj(0) =-= obj(1),
      obj(1) =-= obj(2),
      obj(3) =-= obj(4),
      obj(5) =-= obj(3),
      obj(6) =-= obj(1)
    )

    val ocs = new ObjectConstraintSolver(constraints)
    ocs.solve()

    ocs.objects.getCanonicalEquiv(2) should be (intToTypeVar(0))
    ocs.objects.getCanonicalEquiv(4) should be (intToTypeVar(0))
    ocs.objects.getCanonicalEquiv(12) should be (intToTypeVar(0))

    ocs.objects.getCanonicalEquiv(8) should be (intToTypeVar(6))
    ocs.objects.getCanonicalEquiv(10) should be (intToTypeVar(6))

    ocs.states.getCanonicalEquiv(3) should be (intToTypeVar(1))
    ocs.states.getCanonicalEquiv(5) should be (intToTypeVar(1))
    ocs.states.getCanonicalEquiv(13) should be (intToTypeVar(1))

    ocs.states.getCanonicalEquiv(9) should be (intToTypeVar(7))
    ocs.states.getCanonicalEquiv(11) should be (intToTypeVar(7))
  }

  test("extract equalities from remap") {
    val constraints = Seq(
      ObjectTE(1,2) =-= remap(ObjectTE(3,4), ObjectTE(5,6) >> ObjectTE(5,7)),
      ObjectTE(3,4) =-= remap(ObjectTE(8,9), ObjectTE(10,11) >> ObjectTE(10,12))
    )

    val ocs = new ObjectConstraintSolver(constraints)
    val (objEqualities, stateEqualities, _) = ocs.extractEqualities()
    (objEqualities) should contain (tvp(1,3))
    (objEqualities) should contain (tvp(3,8))
  }

  test("solve simple remap for single method call") {
    val (graph, in, out) = methodGraph(m("m", VarTE(20)))

    val constraints = Seq(
      obj(0) =-= remap(obj(1), obj(2) >> obj(3)),
      obj(2) =-= SolvedObjectTE(graph, Set(in)),
      obj(3) =-= SolvedObjectTE(graph, Set(out))
    )

    implicit val ocs = new ObjectConstraintSolver(constraints)
    if(!ocs.solve()) fail("failed to find a solution")

    val solutions = getSolutionsOrFail(0 to 3)

    val paramSolnOpt = ocs.getSolutionFor(obj(1))
    paramSolnOpt should be ('defined)
    val paramSoln = paramSolnOpt.get

    (paramSoln.states) should have size (1)

    val resultSolnOpt = ocs.getSolutionFor(obj(0))
    resultSolnOpt should be ('defined)
    val resultSoln = resultSolnOpt.get

    (resultSoln.states) should have size (1)
    (paramSoln.graph) should equal (resultSoln.graph)

    val errOrEquiv = findInconsistency(
      graph, s(in), paramSoln.graph, State(paramSoln.states.head))
    
    if(errOrEquiv.isLeft) {
      fail("remap solution not as expected: " + errOrEquiv.left.get)
    }

    val equiv = errOrEquiv.right.get
    val inEquiv = equiv.getRightEquivalent(s(in)).get.name
    val outEquiv = equiv.getRightEquivalent(s(out)).get.name

    (paramSoln.states) should equal (Set(inEquiv))
    (resultSoln.states) should equal (Set(outEquiv))
  }

  test("solve pair of remaps and an equality") {
    val (g1, in1, out1) = methodGraph(m("a"))
    val (g2, in2, out2) = methodGraph(m("b"))

    val constraints = Seq(
      obj(1) =-= remap(obj(0), obj(2) >> obj(3)),
      obj(5) =-= remap(obj(4), obj(6) >> obj(7)),
      obj(1) =-= obj(4),
      obj(2) =-= SolvedObjectTE(g1, Set(in1)),
      obj(3) =-= SolvedObjectTE(g1, Set(out1)),
      obj(6) =-= SolvedObjectTE(g2, Set(in2)),
      obj(7) =-= SolvedObjectTE(g2, Set(out2))
    )

    implicit val ocs = new ObjectConstraintSolver(constraints)
    if(!ocs.solve()) fail("failed to find a solution")

    val solutions = getSolutionsOrFail(0 to 7)

    (solutions(1)) should equal (solutions(4))
    (solutions(0).graph) should equal (solutions(1).graph)
    (solutions(0).graph) should equal (solutions(5).graph)

    val expectedGraph = Graph(
      s("A") ~> s("B") by m("a"),
      s("B") ~> s("C") by m("b")
    )

    (solutions(0).states) should have size (1)

    val errOrEquiv = 
      findInconsistency(
        expectedGraph, s("A"), 
        solutions(0).graph, s(solutions(0).states.head))

    if(!errOrEquiv.isRight) {
      fail("remap solution not as expected: " + errOrEquiv.left.get)
    }
    
    val equiv = errOrEquiv.right.get
    val aEquiv = equiv.getRightEquivalent(s("A")).get.name
    val bEquiv = equiv.getRightEquivalent(s("B")).get.name
    val cEquiv = equiv.getRightEquivalent(s("C")).get.name

    (solutions(0).states) should equal (Set(aEquiv))
    (solutions(1).states) should equal (Set(bEquiv))
    (solutions(5).states) should equal (Set(cEquiv))
  }

  test("solve remap branch") {
    val (g1, in1, out1) = methodGraph(m("a"))
    val (g2, in2, out2) = methodGraph(m("b"))
    val (g3, in3, out3) = methodGraph(m("c"))

    val constraints = 
      call(m("a"), obj(0) >> obj(1), obj(2) >> obj(3)) ++
      call(m("b"), obj(1) >> obj(4), obj(5) >> obj(6)) ++
      call(m("c"), obj(1) >> obj(7), obj(8) >> obj(9))

    val expectedGraph = Graph(
      s("A") ~> s("B") by m("a"),
      s("B") ~> s("C") by m("b"),
      s("B") ~> s("D") by m("c")
    )

    val expectedSolutions = Map(
      0 -> SolvedObjectTE(expectedGraph, "A"),
      1 -> SolvedObjectTE(expectedGraph, "B"),
      4 -> SolvedObjectTE(expectedGraph, "C"),
      7 -> SolvedObjectTE(expectedGraph, "D")
    )

    checkSolutions(constraints, 0 to 9, expectedSolutions)
  }

  def checkSolutions(
      constraints : Seq[TypeConstraint],
      allObjects : Range,
      expectedSolutions : Map[Int,SolvedObjectTE]) = {

    implicit val ocs = new ObjectConstraintSolver(constraints)
    if(!ocs.solve()) fail("failed to find a solution")

    val solutions = getSolutionsOrFail(allObjects)

    expectedSolutions foreach { case (objId, expected) =>
      val actual = solutions(objId)

      /* TODO: need new checking approach
      val errOrEquiv = 
        findInconsistency(
          expected.graph, expected.states map (State(_)), 
          actual.graph, actual.states map (State(_)))

      if(!errOrEquiv.isRight) {
        fail("remap solution not as expected: " + errOrEquiv.left.get + 
          "; expected = " + expected + 
          ", actual = " + actual)
      }
      */
      fail("solution checking currently broken")
    }
  }

  test("solve join separate constraint") {

    val g1 = Graph(
      s("A") ~> s("B") by m("a"),
      s("A") ~> s("C") by m("b"),
      s("C") ~> s("C") by m("b")
    )

    val g2 = Graph(
      s("A") ~> s("B") by m("b"),
      s("B") ~> s("A") by m("a"),
      s("B") ~> s("B") by m("b")
    )

    val constraints = Seq(
      obj(0) =-= SolvedObjectTE(g1, Set("A")),
      obj(1) =-= SolvedObjectTE(g2, Set("A")),
      obj(2) =-= SeparateJoinTE(obj(0), obj(1))
    )

    implicit val ocs = new ObjectConstraintSolver(constraints)
    ocs.solve()

    val solutions = getSolutionsOrFail(0 to 2)

    val expectedJoin = Graph(
      s("A") ~> s("B") by m("b"),
      s("B") ~> s("B") by m("b")
    )

    val joinSolution = solutions(2)

    (joinSolution.states) should have size (1)
    val errOrEquiv = 
      findInconsistency(
        joinSolution.graph, s(joinSolution.states.head),
        expectedJoin, s("A"))

    if(!errOrEquiv.isRight) {
      fail("join solution not as expected: " + errOrEquiv.left.get)
    }
  }
}