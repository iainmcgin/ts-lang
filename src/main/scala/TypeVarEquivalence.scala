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

/**
 * A mutable equivalence class.
 */
class Equivalence[T, U](private var equivMap : Map[T, U]) {

  def addEquivalence(t1 : T, t2 : U) : Boolean = {
    equivMap.get(t1) match {
      case None => { equivMap += t1 -> t2; true }
      case Some(t1eq) => t1eq == t2
    }
  }

  // TODO: what about the reverse, t2 is equivalent to something else?
  def checkEquivalent(t1 : T, t2 : U) : Option[Boolean] =
    equivMap.get(t1).map(_ == t2)

  def getRightEquivalent(t1 : T) : Option[U] = equivMap.get(t1)

  def toMap = equivMap

}

object Equivalence {
  def empty[T, U] = new Equivalence(Map.empty[T, U])
}

class Bijection[T,U](private val t2u : Map[T,U], private val u2t : Map[U,T]) {
  
  def addEquivalence(t : T, u : U) : Option[Bijection[T,U]] =
    (checkEquivalent(t,u).
      flatMap(if(_) Some(this) else None).
      orElse { Some(new Bijection(t2u + (t -> u), u2t + (u -> t))) }
    )

  def checkEquivalent(t : T, u : U) : Option[Boolean] = {
    // as the mappings are symmetric, if (t -> u) does not exist in t2u
    // then there must not be a mapping (u -> v) for some v in u2t, otherwise
    // they are not equivalent.
    t2u.get(t).map(_ == u) orElse (u2t.get(u).map(_ => false))
  }

  def getRightEquivalent(t : T) : Option[U] = t2u.get(t)
  def getLeftEquivalent(u : U) : Option[T] = u2t.get(u)
}

object Bijection {
  def empty[T,U] = new Bijection[T,U](Map.empty, Map.empty)
  def apply[T,U](t2u : Map[T,U]) : Bijection[T,U] = {
    val u2t = (t2u.foldLeft
      (Map.empty[U,T])
      { case (revMap, (t,u)) =>
        if(revMap contains u) throw new IllegalArgumentException()
        revMap + (u -> t)
      }
    )

    new Bijection(t2u, u2t)
  }
}