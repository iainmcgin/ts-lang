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

import scalax.collection.GraphPredef._
import scalax.collection.Graph

import org.scalatest.FunSuite
import org.scalatest.matchers.ShouldMatchers

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

    val obj1 = ocs.objects(1)()
    val obj7 = ocs.objects(7)()

    ocs.objects(3)() should be theSameInstanceAs obj1
    ocs.objects(5)() should be theSameInstanceAs obj1
    ocs.objects(13)() should be theSameInstanceAs obj1

    ocs.objects(9)() should be theSameInstanceAs obj7
    ocs.objects(11)() should be theSameInstanceAs obj7

    val st2 = ocs.states(2)()
    val st8 = ocs.states(8)()

    ocs.states(4)() should be theSameInstanceAs st2
    ocs.states(6)() should be theSameInstanceAs st2
    ocs.states(14)() should be theSameInstanceAs st2

    ocs.states(10)() should be theSameInstanceAs st8
    ocs.states(12)() should be theSameInstanceAs st8
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
    val graph = Graph(
      State("S1") ~> State("S2") by Method("m", VarTE(20))
    )

    val effect = SolvedObjectTE(graph, Set("S1")) >> 
      SolvedObjectTE(graph, Set("S2"))

    val constraints = Seq(
      EqualityConstraint(ObjectTE(1,2), RemapTE(ObjectTE(3,4), effect))
    )

    val ocs = new ObjectConstraintSolver(constraints)
    ocs.solve()
    val solnOpt = ocs.getSolutionFor(ObjectTE(1,2))
    solnOpt should be ('defined)
    val soln = solnOpt.get
    
  }
}