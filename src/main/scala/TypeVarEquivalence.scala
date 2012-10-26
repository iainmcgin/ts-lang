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

  def checkEquivalent(t1 : T, t2 : U) : Option[Boolean] =
    equivMap.get(t1).map(_ == t2)

  def getRightEquivalent(t1 : T) : Option[U] = equivMap.get(t1)

}

object Equivalence {
  def empty[T, U] = new Equivalence(Map.empty[T, U])
}