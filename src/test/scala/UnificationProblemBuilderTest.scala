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

import scala.collection.mutable.Queue

import org.scalatest.FunSuite
import org.scalatest.matchers.ShouldMatchers

class UnificationProblemBuilderTest extends FunSuite with ShouldMatchers {

  import TestUtils._
  import TypeUtil._

  def sanityCheck(eqs : Set[MultiEquation]) = {
    eqs.foreach(meq => { 
      meq.s.foreach(v => { v.m eq meq })
    })
  }

  def uniTest(cs : EqualityConstraint*)(fn : Set[MultiEquation] => Unit) = 
    test(cs.mkString(", ")) {
      val (eqs,upart) = 
        UnificationProblemBuilder.buildForTest(cs :_*)
      sanityCheck(eqs)
      upart.zeroCounterMultEq.foreach(eq => eq.counter should be (0))
      upart.unsolvedCount should be (eqs.size)
      fn(eqs)
    }

  def badTest(cs : EqualityConstraint*) = 
    test("bad: " + cs.mkString(", ")) {
      (evaluating { UnificationProblemBuilder.build(cs :_*) } 
        should produce [CannotUnifyMultiTerms])
    }

  uniTest(0 =^= UnitTE)
  { (eqs) =>

    eqs should have size (1)
    eqs should contain (MultiEquation(0, vset(0), Some(unitMT)))
  }

  uniTest(
    0 =^= UnitTE, 
    0 =^= 1) 
  { (eqs) =>
    
    eqs should have size (1)
    eqs should contain (MultiEquation(0, vset(0,1), Some(unitMT)))
  }

  uniTest(
      0 =^= funTe(4, 2 >> UnitTE),
      1 =^= funTe(5, UnitTE >> 3),
      0 =^= 1)
    { (eqs) =>

    eqs should have size (5)
    eqs should contain (
      MultiEquation(0, 
        vset(0, 1),
        Some(MultiTerm(TypeUtil.FUN_LABEL, List(
          TempMultiEquation(vset(2), Some(unitMT)),
          TempMultiEquation(vset(3), Some(unitMT)),
          TempMultiEquation(vset(4, 5), None)
        )))
      )
    )

    eqs should contain (MultiEquation(1, vset(2), None))
    eqs should contain (MultiEquation(1, vset(3), None))
    eqs should contain (MultiEquation(1, vset(4), None))
    eqs should contain (MultiEquation(1, vset(5), None))
  }

  badTest(
    0 =^= UnitTE,
    1 =^= funTe(UnitTE),
    0 =^= 1
  )

  badTest(
    0 =^= funTe(2, VarTE(3) >> 4),
    0 =^= funTe(1)
  )
}