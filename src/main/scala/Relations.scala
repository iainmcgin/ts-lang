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

trait Relation[T,U] {
  def findRightEquivs(left : T) : Set[U]
  def findRightEquivsOrFail(left : T) : Set[U]
  def findUniqueRightEquivOrFail(left : T) : U
  def findLeftEquivs(right : U) : Set[T]
  def findLeftEquivsOrFail(right : U) : Set[T]
  def findUniqueLeftEquivOrFail(right : U) : T
}

class IdentityRelation[T] extends Relation[T,T] {
  override def findRightEquivs(left : T) = Set(left)
  override def findRightEquivsOrFail(left : T) = Set(left)
  override def findUniqueRightEquivOrFail(left : T) = left
  override def findLeftEquivs(right : T) = Set(right)
  override def findLeftEquivsOrFail(right : T) = Set(right)
  override def findUniqueLeftEquivOrFail(right : T) = right
}

class SetBasedRelation[T,U](private val relation : Set[(T,U)]) 
    extends Relation[T,U] {

  override def findRightEquivs(left : T) : Set[U] =
    relation.filter(_._1 == left).map(_._2)

  override def findRightEquivsOrFail(left : T) : Set[U] = {
    val equivs = findRightEquivs(left)
    if(equivs.isEmpty)
      throw new IllegalStateException("no equivalents")
    equivs
  }

  override def findUniqueRightEquivOrFail(left : T) : U = {
    val equivs = findRightEquivs(left)
    if(equivs.size != 1)
      throw new IllegalStateException("no unique equivalent")
    equivs.head
  }

  override def findLeftEquivs(right : U) : Set[T] =
    relation.filter(_._2 == right).map(_._1)

  override def findLeftEquivsOrFail(right : U) : Set[T] = {
    val equivs = findLeftEquivs(right)
    if(equivs.isEmpty)
      throw new IllegalStateException("no equivalents")
    equivs
  }

  override def findUniqueLeftEquivOrFail(right : U) : T = {
    val equivs = findLeftEquivs(right)
    if(equivs.isEmpty)
      throw new IllegalStateException("no unique equivalent")
    equivs.head
  }
}

object Relation {
  def apply[T,U](equivs : Set[(T,U)]) : Relation[T,U] = 
    new SetBasedRelation(equivs)
  def empty[T,U] : Relation[T,U] = 
    new SetBasedRelation(Set.empty)
  def identity[T] : Relation[T,T]= new IdentityRelation()
}