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
import org.kiama.util.Messaging._
import TypeChecker._
import grizzled.slf4j.Logger

class TypeInferenceTest extends FunSuite with ShouldMatchers {

  val log = Logger[this.type]

  def infTest
    (testDesc : String, termStr : String)
    (testBody : (Term, PolyContext, Set[TypeVar], TypeExpr, PolyContext) => Unit) =
    test(testDesc) {
      resetmessages
      TestUtils.parse(termStr) match {
        case Left(t) => {
          org.kiama.attribution.Attribution.initTree(t)
          log.debug("----")
          log.debug(termStr)
          val constraints = ConstraintGenerator.generateConstraints(t)
          val soln = ConstraintSolver.solvePolymorphic(constraints, t)
          log.debug("----")

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
        tv(1), 
        Seq(
          StateTE(tv(2), Seq.empty)
        ), 
        tv(2)))
  })

  infTest("object value, single method",
    """[ S1 { m = (unit, S1) } ]@S1""")((t, inCtx, freeVars, te, outCtx) => {

    checkIsomorphic(
      te, 
      SolvedObjectTE(
        tv(1),
        Seq(
          StateTE(tv(2), Seq(
            MethodTE("m", UnitTE, tv(2)))
          )
        ),
        tv(2)
      )
    )
  })

  infTest("object value, alternating calls",
    """[ S1 { m = (unit, S2) } S2 { n = (unit, S1) } ]@S1""")(
    (t, inCtx, freeVars, te, outCtx) => {
      checkIsomorphic(
        te,
        SolvedObjectTE(
          tv(1),
          Seq(
            StateTE(tv(2), Seq(
              MethodTE("m", UnitTE, tv(3))
            )),
            StateTE(tv(3), Seq(
              MethodTE("n", UnitTE, tv(2))
            ))
          ),
          tv(2)
        )
      )
    })

  infTest("object parameter, single method call",
    """\(x).(x.m)""")((t, inCtx, freeVars, te, outCtx) => {

    val mRetType = v(3)
    val inObjType = SolvedObjectTE(
      tv(1),
      Seq(
        StateTE(tv(2), Seq(MethodTE("m", mRetType, tv(4)))),
        StateTE(tv(4), Seq.empty[MethodTE])
      ),
      tv(2)
    )
    val outObjType = inObjType.copy(state = tv(4))

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
    val objVar = tv(8)

    val inObjType = SolvedObjectTE(
      objVar,
      Seq(
        StateTE(s1, Seq(MethodTE("m", mRetType, s2))),
        StateTE(s2, Seq(MethodTE("n", nRetType, s3))),
        StateTE(s3, Seq(MethodTE("o", oRetType, s4))),
        StateTE(s4, Seq.empty[MethodTE])
      ),
      s1
    )
    val outObjType = inObjType.copy(state = s4)

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
        tv(7),
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
}