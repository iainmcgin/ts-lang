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

  test("resolve direct equalities") {
    val constraints = Seq(
      EqualityConstraint(ObjectTE(1,2),ObjectTE(3,4)),
      EqualityConstraint(ObjectTE(3,4),ObjectTE(5,6)),
      EqualityConstraint(ObjectTE(7,8),ObjectTE(9,10)),
      EqualityConstraint(ObjectTE(7,8),ObjectTE(11,12)),
      EqualityConstraint(ObjectTE(13,14),ObjectTE(5,6))
    )

    val ocs = new ObjectConstraintSolver(constraints)
    val partition = ocs.partitionConstraints()
    ocs.resolveDirectObjectEqualities(partition.objectEqualities)
    ocs.resolveDirectStateEqualities(partition.stateEqualities)

    ocs.objects.getCanonicalEquiv(3) should be (intToTypeVar(1))
    ocs.objects.getCanonicalEquiv(5) should be (intToTypeVar(1))
    ocs.objects.getCanonicalEquiv(13) should be (intToTypeVar(1))

    ocs.objects.getCanonicalEquiv(9) should be (intToTypeVar(7))
    ocs.objects.getCanonicalEquiv(11) should be (intToTypeVar(7))

    ocs.states.getCanonicalEquiv(4) should be (intToTypeVar(2))
    ocs.states.getCanonicalEquiv(6) should be (intToTypeVar(2))
    ocs.states.getCanonicalEquiv(14) should be (intToTypeVar(2))

    ocs.states.getCanonicalEquiv(10) should be (intToTypeVar(8))
    ocs.states.getCanonicalEquiv(12) should be (intToTypeVar(8))
  }

  test("extract equalities from remap") {
    val constraints = Seq(
      EqualityConstraint(
        ObjectTE(1,2), 
        RemapTE(ObjectTE(3,4), ObjectTE(5,6) >> ObjectTE(5,7))),
      EqualityConstraint(
        ObjectTE(3,4),
        RemapTE(ObjectTE(8,9), ObjectTE(10,11) >> ObjectTE(10,12))
      )
    )

    val ocs = new ObjectConstraintSolver(constraints)
    val partition = ocs.partitionConstraints()
    (partition.objectEqualities) should contain (tvp(1,3))
    (partition.objectEqualities) should contain (tvp(3,8))
  }

  test("solve simple remap for single method call") {
    val (graph, in, out) = methodGraph(m("m", VarTE(20)))

    val effect = 
      SolvedObjectTE(graph, Set(in)) >> SolvedObjectTE(graph, Set(out))

    val constraints = Seq(
      EqualityConstraint(ObjectTE(1,2), RemapTE(ObjectTE(3,4), effect))
    )

    val ocs = new ObjectConstraintSolver(constraints)
    ocs.solve()

    val paramSolnOpt = ocs.getSolutionFor(ObjectTE(3,4))
    paramSolnOpt should be ('defined)
    val paramSoln = paramSolnOpt.get

    (paramSoln.states) should have size (1)

    val resultSolnOpt = ocs.getSolutionFor(ObjectTE(1,2))
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

    val eff1 = SolvedObjectTE(g1, Set(in1)) >> SolvedObjectTE(g1, Set(out1))
    val eff2 = SolvedObjectTE(g2, Set(in2)) >> SolvedObjectTE(g2, Set(out2))

    val constraints = Seq(
      EqualityConstraint(ObjectTE(3,4), RemapTE(ObjectTE(1,2), eff1)),
      EqualityConstraint(ObjectTE(7,8), RemapTE(ObjectTE(5,6), eff2)),
      EqualityConstraint(ObjectTE(3,4), ObjectTE(5,6))
    )

    val ocs = new ObjectConstraintSolver(constraints)
    ocs.solve()

    val o1s2Opt = ocs.getSolutionFor(ObjectTE(1,2))
    val o3s4Opt = ocs.getSolutionFor(ObjectTE(3,4))
    val o5s6Opt = ocs.getSolutionFor(ObjectTE(5,6))
    val o7s8Opt = ocs.getSolutionFor(ObjectTE(7,8))

    (o1s2Opt) should be ('defined)
    (o3s4Opt) should be ('defined)
    (o5s6Opt) should be ('defined)
    (o7s8Opt) should be ('defined)

    val o1s2 = o1s2Opt.get
    val o3s4 = o3s4Opt.get
    val o5s6 = o5s6Opt.get
    val o7s8 = o7s8Opt.get

    (o3s4) should equal (o5s6)

    (o1s2.graph) should equal (o3s4.graph)
    (o1s2.graph) should equal (o7s8.graph)

    val expectedGraph = Graph(
      s("A") ~> s("B") by m("a"),
      s("B") ~> s("C") by m("b")
    )

    (o1s2.states) should have size (1)

    val errOrEquiv = 
      findInconsistency(expectedGraph, s("A"), o1s2.graph, s(o1s2.states.head))

    if(!errOrEquiv.isRight) {
      fail("remap solution not as expected: " + errOrEquiv.left.get)
    }
    
    val equiv = errOrEquiv.right.get
    val aEquiv = equiv.getRightEquivalent(s("A")).get.name
    val bEquiv = equiv.getRightEquivalent(s("B")).get.name
    val cEquiv = equiv.getRightEquivalent(s("C")).get.name

    (o1s2.states) should equal (Set(aEquiv))
    (o3s4.states) should equal (Set(bEquiv))
    (o7s8.states) should equal (Set(cEquiv))
  }
}