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

package object sm {

  import scalax.collection.Graph
  import scalax.collection.GraphPredef._
  import scalax.collection.GraphEdge._

  import scalax.collection.edge.LDiEdge

  implicit def edge2TransitionAssoc[S <: State](e : DiEdge[State]) =
    new TransitionAssoc(e)

  type StateGraph = Graph[State,Transition]

  def emptySM = StateMachine(
    Graph(State("S")),
    State("S"),
    Set(State("S"))
  )
}