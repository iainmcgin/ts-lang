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

class Relation[T,U](val relation : Set[(T,U)]) {

  def findRightEquivs(left : T) : Set[U] =
    relation.filter(_._1 == left).map(_._2)

  def findRightEquivsOrFail(left : T) : Set[U] = {
    val equivs = findRightEquivs(left)
    if(equivs.isEmpty)
      throw new IllegalStateException("no equivalents")
    equivs
  }

  def findUniqueRightEquivOrFail(left : T) : U = {
    val equivs = findRightEquivs(left)
    if(equivs.size != 1)
      throw new IllegalStateException("no unique equivalent for " + left + " found in relation " + relation)
    equivs.head
  }

  def findLeftEquivs(right : U) : Set[T] =
    relation.filter(_._2 == right).map(_._1)

  def findLeftEquivsOrFail(right : U) : Set[T] = {
    val equivs = findLeftEquivs(right)
    if(equivs.isEmpty)
      throw new IllegalStateException("no equivalents")
    equivs
  }

  def findUniqueLeftEquivOrFail(right : U) : T = {
    val equivs = findLeftEquivs(right)
    if(equivs.isEmpty)
      throw new IllegalStateException("no unique equivalent ")
    equivs.head
  }

  def subset(lefts : Set[T]) = 
    Relation(lefts.flatMap(l => relation.filter(_._1 == l)))

  def union(other : Relation[T,U]) = 
    Relation(this.relation union other.relation)

  def leftIntersection[U2](other : Relation[T,U2]) : Relation[T,(U,U2)] = {
    val tMap =
      (relation.foldLeft
        (Map.empty[T,Set[U]])
        { case (tMap, (t, u)) =>
          tMap.updated(t, tMap.getOrElse(t, Set.empty) + u)
        }
      )

    val intersectionSet = 
      (tMap.foldLeft
        (Set.empty[(T,(U,U2))])
        { case (set, (t, uset)) => {
          val u2set = other.relation.filter(_._1 == t).map(_._2)
          set ++ uset.flatMap(u => u2set.map(u2 => (t, (u, u2))))
        }}
      )

    Relation(intersectionSet)
  }

  def rightIntersection[T2](other : Relation[T2,U]) : Relation[(T,T2),U] = {
    val uMap = 
      (relation.foldLeft
        (Map.empty[U,Set[T]])
        { case (uMap, (t, u)) => 
          uMap.updated(u, uMap.getOrElse(u, Set.empty) + t)
        }
      )

    val intersectionSet = 
      (uMap.foldLeft
        (Set.empty[((T,T2),U)])
        { case (set, (u, tset)) => {
          val t2set = other.relation.filter(_._2 == u).map(_._1)
          set ++ tset.flatMap(t => t2set.map(t2 => ((t, t2), u)))
        }}
      )

    Relation(intersectionSet)
  }

  def compose[V](other : Relation[U,V]) : Relation[T,V] =
    Relation(this.relation.flatMap { case (t, u) => 
      other.findRightEquivs(u).map(v => (t,v)) 
    })


  override def toString = 
    relation.
    map(entry => entry._1 + " = " + entry._2).
    mkString("Relation(", ", ", ")")
}

object Relation {
  def apply[T,U](equivs : Set[(T,U)]) : Relation[T,U] = 
    new Relation(equivs)

  def empty[T,U] : Relation[T,U] = 
    new Relation(Set.empty)
}