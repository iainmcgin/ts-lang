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

case class CannotUnifyMultiTerms(m1 : MultiTerm, m2 : MultiTerm) 
  extends Exception

case class UPart(
  var zeroCounterMultEq : List[MultiEquation],
  var unsolvedCount : Int)

case class System(var t : List[MultiEquation], var u : UPart)

case class MultiTerm(fn : Int, var args : List[TempMultiEquation]) {

  def merge(m2 : Option[MultiTerm]) : MultiTerm = m2 match {
    case None => this
    case Some(MultiTerm(fn2, args2)) => {
      if (fn != fn2 || args.length != args2.length) {
        throw CannotUnifyMultiTerms(this, m2.get)
      }

      val newArgs = args.zip(args2).map(p => p._1.merge(p._2))
      MultiTerm(fn, newArgs)
    }
  }

  override def toString = "F" + fn + "(" + args.mkString(", ") + ")"
}

case class MultiEquation(var s : Set[Variable], var m : Option[MultiTerm])
                        (var counter : Int) {

  def merge(other : MultiEquation) : MultiEquation =
    if(this == other) {
      this
    } else {
      val merged = MultiEquation(
        this.s ++ other.s, 
        this.m.map(_.merge(other.m)).orElse(other.m))(
        this.counter + other.counter)
      merged.s.foreach(v => { v.m = merged })
      merged
    }

  override def toString =
    "[" + counter + "] {" + s.mkString(", ") + "} = " + m.map(_.toString).getOrElse("∅")
}

object MultiEquation {

  /**
   * alternative "constructor" for case class with the old signature, to avoid
   * changing all the existing test code
   */
  def apply(counter : Int, s : Set[Variable], m : Option[MultiTerm]) : MultiEquation = 
    MultiEquation(s, m)(counter)
}

case class TempMultiEquation(
  var s : Set[Variable], 
  var m : Option[MultiTerm]) {
  def merge(other : TempMultiEquation) : TempMultiEquation = {
    val s = this.s ++ other.s
    val m = this.m.map(_.merge(other.m)).orElse(other.m)
    TempMultiEquation(s, m)
  }

  override def toString = 
    ("<" + (if(s.isEmpty) "" else "{" + s.mkString(", ") + "} ") + 
      m.map(_.toString).getOrElse("∅") + ">")
}

/** !!! cyclic references between meqs and vars. Need to unroll somehow */
case class Variable(val num : Int)(var m : MultiEquation) {
  override def toString = "v" + num
}

/**
 * Finds the most general unifier for a system of equalities using the
 * algorithm in "An Efficient Unification Algorithm" by
 * Martelli and Montanari 1982. The implementation is rather imperative,
 * unfortunately.
 */
object Unifier {
	
  def unify(r : System) = {
    while(r.u.unsolvedCount > 0) {
      val mult = selectMultiEquation(r.u)
      if(!mult.m.isEmpty) {
        val (commonPart, frontier) = reduce(mult.m.get)
        mult.m = Some(commonPart)
        compact(frontier, r.u)
      }
      r.t = mult :: r.t
    }

    r.t
  }

  def selectMultiEquation(u : UPart) : MultiEquation =
    u.zeroCounterMultEq match {
      case Nil => fail("cycle")
      case mult :: mults => {
        u.zeroCounterMultEq = mults
        u.unsolvedCount -= 1
        mult
      }
    }

  def reduce(m : MultiTerm) : (MultiTerm, List[TempMultiEquation]) = {
    val (commonArgs, frontier) = 
      (m.args.foldRight
        (Pair(List.empty[TempMultiEquation], List.empty[TempMultiEquation]))
        ((arg, p) => {
          if(arg.s.isEmpty) {
            val (c, f) = reduce(arg.m.get)
            val newArg = TempMultiEquation(Set.empty, Some(c))
            Pair(newArg :: p._1, f ++ p._2)
          } else {
            Pair(TempMultiEquation(Set(arg.s.head), None) :: p._1, arg :: p._2)
          }
        })
      )

    val newM = MultiTerm(m.fn, commonArgs)
    Pair(newM, frontier)
  }

  def compact(frontier : List[TempMultiEquation], u : UPart) = {
    frontier.foreach(tme => {
      var mult = tme.s.head.m
      mult.counter -= 1

      tme.s.tail.foreach(v => {
        val mult1 = v.m
        mult1.counter -= 1
        val merged = mult.merge(mult1)
        if(!(merged eq mult)) u.unsolvedCount -= 1
        mult = merged
      })

      tme.s.head.m = mult

      mult.m = mult.m.map(_.merge(tme.m)).orElse(tme.m)
      if(mult.counter <= 0) {
        u.zeroCounterMultEq = mult :: u.zeroCounterMultEq
      }
    })
  }

  def fail(reason : String) = throw new IllegalArgumentException(reason)
}