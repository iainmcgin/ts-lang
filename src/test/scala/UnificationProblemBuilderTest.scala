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

import scala.collection.mutable.Queue

import org.scalatest.FunSuite
import org.scalatest.matchers.ShouldMatchers

class UnificationProblemBuilderTest extends FunSuite with ShouldMatchers {

  import TestUtils._

  def sanityCheck(eqs : Set[MultiEquation]) = {
    eqs.foreach(meq => { 
      meq.s.foreach(v => { v.m eq meq })
    })
  }

  def uniTest(cs : TypeVarConstraint*)(fn : Set[MultiEquation] => Unit) = 
    test(cs.mkString(", ")) {
      val (eqs,upart) = 
        UnificationProblemBuilder.buildForTest(cs :_*)
      sanityCheck(eqs)
      upart.zeroCounterMultEq.foreach(eq => eq.counter should be (0))
      upart.unsolvedCount should be (eqs.size)
      fn(eqs)
    }

  def badTest(cs : TypeVarConstraint*) = 
    test("bad: " + cs.mkString(", ")) {
      (evaluating { UnificationProblemBuilder.build(cs :_*) } 
        should produce [CannotUnifyMultiTerms])
    }

  uniTest(0 =^= unitTy) 
  { (eqs) =>

    eqs should have size (1)
    eqs should contain (MultiEquation(0, vset(0), Some(unitMT)))
  }

  uniTest(
    0 =^= unitTy, 
    0 =^= 1) 
  { (eqs) =>
    
    eqs should have size (1)
    eqs should contain (MultiEquation(0, vset(0,1), Some(unitMT)))
  }

  uniTest(
      0 =^= funTy(Hole(4), Hole(2) >> unitTy),
      1 =^= funTy(Hole(5), unitTy >> Hole(3)),
      0 =^= 1)
    { (eqs) =>

    eqs should have size (5)
    eqs should contain (
      MultiEquation(0, 
        vset(0, 1),
        Some(MultiTerm(1, List(
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
    0 =^= unitTy,
    1 =^= funTy(unitTy),
    0 =^= 1
  )

  badTest(
    0 =^= funTy(Hole(2), Hole(3) >> Hole(4)),
    0 =^= funTy(Hole(1))
  )
}