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
        println(this + " != " + m2.get)
        throw CannotUnifyMultiTerms(this, m2.get)
      }

      val newArgs = args.zip(args2).map(p => p._1.merge(p._2))
      MultiTerm(fn, newArgs)
    }
  }

  override def toString = "F" + fn + "(" + args.mkString(", ") + ")"
}

case class MultiEquation(
  var counter : Int,
  var s : Set[Variable],
  var m : Option[MultiTerm]) {

  def merge(other : MultiEquation) : MultiEquation =
    if(this eq other) 
      this
    else {
      val merged = MultiEquation(
        this.counter + other.counter, 
        this.s ++ other.s, 
        this.m.map(_.merge(other.m)).orElse(other.m)
      )
      merged.s.foreach(v => { v.m = merged })
      merged
    }

  override def equals(o : Any) = o match {
    case MultiEquation(_,s2,m2) => s == s2 && m == m2
  }

  override def toString =
    "{" + s.mkString(", ") + "} = " + m.map(_.toString).getOrElse("∅")
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
case class Variable(val num : Int, var m : MultiEquation) {

  override def toString = "v" + num
  override def equals(o : Any) = o match { 
    case Variable(num2,_) => num == num2
    case _ => false
  }
  override def hashCode = num.hashCode
}

/**
 * Finds the most general unifier for a system of equalities using the
 * algorithm in "An Efficient Unification Algorithm" by
 * Martelli and Montanari 1982. The implementation is rather imperative,
 * unfortunately.
 */
object Unifier {
	
  // DONE
  def unify(r : System) = {
    while(!r.u.zeroCounterMultEq.isEmpty) {
      val mult = selectMultiEquation(r.u)
      println("unsolved: " + r.u.unsolvedCount)
      println("processing " + mult)
      if(!mult.m.isEmpty) {
        val (commonPart, frontier) = reduce(mult.m.get)
        mult.m = Some(commonPart)
        compact(frontier, r.u)
      }
      r.t = mult :: r.t
    }

    r.t
  }

  // DONE
  def selectMultiEquation(u : UPart) : MultiEquation =
    u.zeroCounterMultEq match {
      case Nil => fail("cycle")
      case mult :: mults => {
        u.zeroCounterMultEq = mults
        mult
      }
    }

  // DONE
  def reduce(m : MultiTerm) : (MultiTerm, List[TempMultiEquation]) = {
    println("reducing " + m)
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
    println("common part: " + newM)
    println("frontier: " + frontier)

    Pair(newM, frontier)
  }

  // DONE, potential optimisations / clearer expression possible?
  def compact(frontier : List[TempMultiEquation], u : UPart) = {
    frontier.foreach(tme => {
      println("compacting " + tme)
      var mult = tme.s.head.m
      println("meq for v" + tme.s.head.num + " is " + mult)
      mult.counter -= 1

      tme.s.tail.foreach(v => {
        val mult1 = v.m
        mult1.counter -= 1
        println("merging" + mult + " and " + mult1)
        mult = mult.merge(mult1)
        tme.s.head.m = mult
      })

      mult.m = mult.m.map(_.merge(tme.m)).orElse(tme.m)
      println("merged eq: " + mult)
      if(mult.counter == 0) {
        u.zeroCounterMultEq = mult :: u.zeroCounterMultEq
      }
      u.unsolvedCount -= 1
    })
  }
  

  def fail(reason : String) = throw new IllegalArgumentException(reason)
}