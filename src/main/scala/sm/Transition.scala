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

package uk.ac.gla.dcs.ts.sm

import scalax.collection.GraphPredef._
import scalax.collection.Graph
import scalax.collection.GraphEdge._

class Transition[N](nodes : Product, val m : Method)
  extends DiEdge[N](nodes)
  with ExtendedKey[N]
  with EdgeCopy[Transition]
  with EdgeIn[N,Transition] {

  def keyAttributes = Seq(m)
  override def copy[NN](newNodes : Product) =
    new Transition[NN](newNodes, m)

  override def toString = from + "~>" + to + "#" + m.name
}

object Transition {
  def apply(from : State, to : State, m : Method) = 
    new Transition[State](NodeProduct(from, to), m)
  def unapply(e : Transition[State]) = Some(e)
}

final class TransitionAssoc[S <: State](val e : DiEdge[S]) {
  @inline def by(m : Method) =
    new Transition[S](e.nodes, m) with EdgeIn[S,Transition]
}
