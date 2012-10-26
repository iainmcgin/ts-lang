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

import scalax.collection.GraphPredef._
import scalax.collection.Graph

import org.scalatest.FunSuite
import org.scalatest.matchers.ShouldMatchers

import org.kiama.util.Messaging._

import TypeChecker._
import sm._

import grizzled.slf4j.Logger

class TypeInferenceTest extends FunSuite with ShouldMatchers {

  val log = Logger[this.type]

  def infTest
    (testDesc : String, termStr : String)
    (testBody : (Term, PolyContext, Set[TypeVar], TypeExpr, PolyContext) => Unit) =
    // test(testDesc) {
    ignore(testDesc) {
      resetmessages
      TestUtils.parse(termStr) match {
        case Left(t) => {
          org.kiama.attribution.Attribution.initTree(t)
          log.debug("----")
          log.debug(termStr)
          val constraints = ConstraintGenerator.generateConstraints(t)
          val soln = ConstraintSolver.solvePolymorphic(constraints, t)
          log.debug("====")

          soln match {
            case None => fail("could not infer type of term")
            case Some(Tuple4(inCtx, freeVars, te, outCtx)) =>
              testBody(t, inCtx, freeVars, te, outCtx)
          }
        }

        case Right(err) => {
          fail("failed to parse term: " + err)
        }
      }
    }

  def v(i : Int) = VarTE(TypeVar(i))
  def tv(i : Int) = TypeVar(i)

  def checkIsomorphic(actual : TypeExpr, expected : TypeExpr) = {
    if(!actual.isomorphic(expected)) {
      fail(actual + " is not isomorphic to expected type " + expected)
    }
  }

  infTest("function taking no-arg function",
    """\(a).(a())""")((t, inCtx, freeVars, te, outCtx) => {

    
    val expectedType = funTe(v(1), funTe(v(1)) >> funTe(v(1)))
    checkIsomorphic(te, expectedType)
  })

  infTest("function taking ignored argument",
    """\(a).(unit)""")((t, inCtx, freeVars, te, outCtx) => {

    val expectedType = funTe(UnitTE, v(1) >> v(1))
    checkIsomorphic(te, expectedType)
  })

  infTest("function overwrites argument with unit",
    """\(a).(a := unit)""")((t, inCtx, freeVars, te, outCtx) => {

    
    val expectedType = funTe(UnitTE, v(1) >> UnitTE)
    checkIsomorphic(te, expectedType)
  })

  infTest("double overwrite",
    """\(a).(a := unit; a := \(b).(unit))""")(
    (t, inCtx, freeVars, te, outCtx) => {

    val expectedType = funTe(UnitTE, v(1) >> funTe(UnitTE, v(2) >> v(2)))
    checkIsomorphic(te, expectedType)
  })

  infTest("function invoking function",
    """\(a,b).(a(b))"""
  )((t, inCtx, freeVars, te, outCtx) => {

    val bInType = v(1)
    val bOutType = v(2)
    val aResultType = v(3)
    val aType = funTe(aResultType, bInType >> bOutType)
    
    val expectedType = funTe(aResultType, aType >> aType, bInType >> bOutType)
    checkIsomorphic(te, expectedType)
  })

  // object tests
  infTest("object value, no methods",
    """[ S1 { } ]@S1""")((t, inCtx, freeVars, te, outCtx) => {

    checkIsomorphic(
      te, 
      SolvedObjectTE(
        Graph(State("S1")),
        Set("S1")
      )
    )
  })

  infTest("object value, single method",
    """[ S1 { m = (unit, S1) } ]@S1""")((t, inCtx, freeVars, te, outCtx) => {

    checkIsomorphic(
      te, 
      SolvedObjectTE(
        Graph(State("S1") ~> State("S2") by Method("m", UnitTE)),
        Set("S1")
      )
    )
  })

  infTest("object value, alternating calls",
    """[ S1 { m = (unit, S2) } S2 { n = (unit, S1) } ]@S1""")(
    (t, inCtx, freeVars, te, outCtx) => {
      checkIsomorphic(
        te,
        SolvedObjectTE(
          Graph(
            State("S1") ~> State("S2") by Method("m", UnitTE),
            State("S2") ~> State("S1") by Method("n", UnitTE)
          ),
          Set("S1")
        )
      )
    })

  infTest("object parameter, single method call",
    """\(x).(x.m)""")((t, inCtx, freeVars, te, outCtx) => {

    val mRetType = v(3)
    val inObjType = SolvedObjectTE(
      Graph(State("S1") ~> State("S2") by Method("m", mRetType)),
      Set("S1")
    )
    val outObjType = inObjType.copy(states = Set("S2"))

    checkIsomorphic(
      te,
      funTe(mRetType, inObjType >> outObjType))

  })

  infTest("object parameter, multiple method calls",
    """\(x).(x.m ; x.n ; x.o )""")((t, inCtx, freeVars, te, outCtx) => {

    val mRetType = v(1)
    val nRetType = v(2)
    val oRetType = v(3)
    val s1 = tv(4)
    val s2 = tv(5)
    val s3 = tv(6)
    val s4 = tv(7)

    val inObjType = SolvedObjectTE(
      Graph(
        State("S1") ~> State("S2") by Method("m", mRetType),
        State("S2") ~> State("S3") by Method("n", nRetType),
        State("S3") ~> State("S4") by Method("o", oRetType)
      ),
      Set("S1")
    )
    val outObjType = inObjType.copy(states = Set("S4"))

    checkIsomorphic(
      te,
      funTe(oRetType, inObjType >> outObjType))
  })

  // free variable discovery tests

  infTest("free variable overwrite",
    """x := unit""")((t, inCtx, freeVars, te, outCtx) => {

    inCtx should contain key ("x")
    checkIsomorphic(inCtx("x"), v(1))
    outCtx should contain key ("x")
    assert(outCtx("x") === UnitTE)
  })

  infTest("free variable used as no-arg function",
    """a()""")((t, inCtx, freeVars, te, outCtx) => {

    checkIsomorphic(te, v(1))
    inCtx should have size (1)
    inCtx should contain key ("a")
    checkIsomorphic(inCtx("a"), funTe(v(1)))
    assert(inCtx("a") === outCtx("a"))
  })

  infTest("free variable used as function argument",
    """let f = \(x).unit in f(a)""")((t, inCtx, freeVars, te, outCtx) => {

    assert(te == UnitTE)
    inCtx should contain key ("a")
    outCtx should contain key ("a")
    checkIsomorphic(inCtx("a"), v(1))
    assert(inCtx("a") === outCtx("a"))
  })

  infTest("sequence of method calls",
    """x.m ; x.n""")((t, inCtx, freeVars, te, outCtx) => {

    checkIsomorphic(
      inCtx("x"),
      SolvedObjectTE(
        Graph(
          State("S1") ~> State("S2") by Method("m", v(1)),
          State("S2") ~> State("S3") by Method("n", v(2))
        ),
        Set("S1")
      )
    )
  })
}