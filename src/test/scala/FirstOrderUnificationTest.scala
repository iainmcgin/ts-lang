/*
 * This file is part of TS0.
 * 
 * TS0 - Copyright (c) 2012, Iain McGinniss
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted under the terms of the 2-clause BSD license:
 * http://opensource.org/licenses/BSD-2-Clause
 */

package uk.ac.gla.dcs.ts0

import org.scalatest.FunSuite
import org.scalatest.matchers.ShouldMatchers

class FirstOrderUnificationTest extends FunSuite with ShouldMatchers {

  import TestUtils._

  var vars = Map.empty[Int,Variable]
  def initVars(vs : Range) = { vars = Map((vs map (i => i -> v(i))) :_*) }
  def vset(vs : Int*) = Set(vs.map(v => vars(v)) :_*)

  def f(tme : TempMultiEquation*) = MultiTerm(1, List(tme :_*))
  def g(tme : TempMultiEquation*) = MultiTerm(2, List(tme :_*))
  def h(tme : TempMultiEquation*) = MultiTerm(3, List(tme :_*))
  val ca = MultiTerm(4, List.empty)
  val cb = MultiTerm(5, List.empty)

  def varsTME(vs : Int*) = TempMultiEquation(vset(vs :_*), None)
  def tme(vars : Set[Variable], mt : MultiTerm = null) = {
    val mtOpt = mt match { 
      case null => None 
      case x => Some(x)
    }
    TempMultiEquation(vars, mtOpt)
  }

  def system(eqs : List[MultiEquation], size : Int) =
    System(List.empty, UPart(eqs.filter(_.counter == 0).toList, size))

  test("example page 260") {
    // x0 = f(x1, h(x1), x2) = f(g(x3), x4, x3)
    initVars(0 to 4)

    val gOfX3 = g(varsTME(3))
    val x1EqGOfX3 = TempMultiEquation(vset(1), Some(gOfX3))

    val hOfX1 = h(varsTME(1))
    val x4EqGOfX1 = TempMultiEquation(vset(4), Some(hOfX1))

    val x2EqX3 = TempMultiEquation(vset(2,3), None)

    vars(0).m = MultiEquation(
      0, 
      vset(0), 
      Some(MultiTerm(1, List(x1EqGOfX3, x4EqGOfX1, x2EqX3)))
    )
    vars(1).m = MultiEquation(1, vset(1), None)
    vars(2).m = MultiEquation(1, vset(2), None)
    vars(3).m = MultiEquation(1, vset(3), None)
    vars(4).m = MultiEquation(1, vset(4), None)

    val r = system((vars.values.map(_.m)).toList, 5)
    
    val solution = Unifier.unify(r)

    val x0solution = MultiEquation(
      0, vset(0), Some(f(varsTME(1), varsTME(4), varsTME(2)))
    )
    val x1solution = MultiEquation(0, vset(1), Some(gOfX3))
    val x2solution = MultiEquation(0, vset(2, 3), None)
    val x4solution = MultiEquation(0, vset(4), Some(hOfX1))

    solution should have length 4
    solution should contain (x0solution)
    solution should contain (x1solution)
    solution should contain (x2solution)
    solution should contain (x4solution)
  }

  test("example page 262") {
    // x1 = g(x2)
    // x0 = f(x1, h(x1), x2) = f(g(x3), x4, x3)

    initVars(0 to 4)

    vars(0).m = MultiEquation(
      0,
      vset(0),
      Some(f(
        TempMultiEquation(vset(1), Some(g(varsTME(3)))),
        TempMultiEquation(vset(4), Some(h(varsTME(1)))),
        TempMultiEquation(vset(2,3), None)
      ))
    )
    vars(1).m = MultiEquation(2, vset(1), Some(g(varsTME(2))))
    vars(2).m = MultiEquation(2, vset(2), None)
    vars(3).m = MultiEquation(2, vset(3), None)
    vars(4).m = MultiEquation(1, vset(4), None)

    val r = system((vars.values.map(_.m)).toList, 5)

    println("----------------TEST 2-------------------------")
    println("input: " + vars.map(p => p._1 + " -> " + p._2.m))
    val solution = Unifier.unify(r)
    println("----------------TEST 2 end---------------------")

    val expected = Seq(
      MultiEquation(0, vset(0), Some(f(varsTME(1), varsTME(4), varsTME(2)))),
      MultiEquation(0, vset(1), Some(g(varsTME(2)))),
      MultiEquation(0, vset(2, 3), None),
      MultiEquation(0, vset(4), Some(h(varsTME(1))))
    )

    solution should have length (expected.length)
    expected.foreach(s => solution should contain (s))
  }

  test("example page 268") {
    // x0 = f(x1, g(x2, x3), x2, b) = f( g( h(a, x5), x2), x1, h(a, x4), x4)
    initVars(0 to 5)

    vars(0).m = MultiEquation(0, vset(0), Some(
      f(
        tme(vset(1), g(tme(vset(), h(tme(vset(), ca), tme(vset(5)))), tme(vset(2)))),
        tme(vset(1), g(tme(vset(2)), tme(vset(3)))),
        tme(vset(2), h(tme(vset(), ca), tme(vset(4)))),
        tme(vset(4), cb)
      )
    ))

    vars(1).m = MultiEquation(2, vset(1), None)
    vars(2).m = MultiEquation(3, vset(2), None)
    vars(3).m = MultiEquation(1, vset(3), None)
    vars(4).m = MultiEquation(2, vset(4), None)
    vars(5).m = MultiEquation(1, vset(5), None)

    var r = system(vars.values.map(_.m).toList, 6)

    println("----------------TEST 3-------------------------")
    val solution = Unifier.unify(r)
    println("----------------TEST 3 end---------------------")

    val expected = Seq(
      MultiEquation(0, vset(0), 
        Some(f(varsTME(1), varsTME(1), varsTME(2), varsTME(4)))),
      MultiEquation(0, vset(2, 3), Some(h(tme(vset(), ca), varsTME(4)))),
      MultiEquation(0, vset(1), Some(g(varsTME(2), varsTME(2)))),
      MultiEquation(0, vset(4, 5), Some(cb))
    )

    solution should have length (expected.length)
    expected foreach (s => solution should contain (s))
  }
}