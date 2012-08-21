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
import org.kiama.util.Messaging._
import TypeChecker._

class TypeInferenceTest extends FunSuite with ShouldMatchers {

  def infTest
    (testDesc : String, termStr : String)
    (testBody : (Term, PolyContext, Set[TypeVar], TypeExpr, PolyContext) => Unit) =
    test(testDesc) {
      resetmessages
      TestUtils.parse(termStr) match {
        case Left(t) => {
          org.kiama.attribution.Attribution.initTree(t)
          println("----")
          println(termStr)
          val constraints = ConstraintGenerator.generateConstraints(t)
          val soln = ConstraintSolver.solvePolymorphic(constraints, t)
          println("----")

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

    checkIsomorphic(te, SolvedObjectTE(Seq(StateTE(tv(1), Seq.empty)), tv(1)))

  })

  infTest("object value, single method",
    """[ S1 { m = (unit, S1) } ]@S1""")((t, inCtx, freeVars, te, outCtx) => {

    checkIsomorphic(
      te, 
      SolvedObjectTE(
        Seq(
          StateTE(tv(1), Seq(
            MethodTE("m", UnitTE, tv(1)))
          )
        ),
        tv(1)
      )
    )
  })

  infTest("object value, alternating calls",
    """[ S1 { m = (unit, S2) } S2 { n = (unit, S1) } ]@S1""")(
    (t, inCtx, freeVars, te, outCtx) => {
      checkIsomorphic(
        te,
        SolvedObjectTE(
          Seq(
            StateTE(tv(1), Seq(
              MethodTE("m", UnitTE, tv(2))
            )),
            StateTE(tv(2), Seq(
              MethodTE("n", UnitTE, tv(1))
            ))
          ),
          tv(1)
        )
      )
    })

  // free variable discovery tests
  /*
  infTest(
    "no-arg function",
    """a()""")((t, inCtx, ty, outCtx, errs) => {

    (errs) should have length (1)
    assert(ty === UnitType())
    inCtx should have size (1)
    inCtx should contain key ("a")
  })

  infTest("sequence of method calls",
    """x.m ; x.n""")((t, inCtx, freeVars, te, outCtx) => {

    checkIsomorphic(
      inCtx("x"),
      SolvedObjectTE(
        Seq(
          StateTE(tv(1), Seq(
            MethodTE("m", v(5), tv(2))
          )),
          StateTE(tv(2), Seq(
            MethodTE("n", v(6), tv(3))
          )),
          StateTE(tv(3), Seq.empty)
        ),
        tv(1)
      )
    )
  })
  */
}