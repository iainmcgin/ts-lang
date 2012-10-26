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

import uk.ac.gla.dcs.ts.Equivalence
import uk.ac.gla.dcs.ts.TypeVar
import uk.ac.gla.dcs.ts.StateNameEquiv
import uk.ac.gla.dcs.ts.Relation

object StateGraphUtils {

  /**
   * Creates a graph which represents the intersection of the paths
   * possible from all the provided states within the same graph,
   * along with a set that relates the states in the original graph
   * to their equivalents in the intersection graph.
   */
  def internalIntersection(
      g : StateGraph, 
      states : Set[String]) 
      : (StateGraph, String, StateNameEquiv) = {
    // TODO: built equivalence relation is garbage
    if(states.isEmpty) throw new IllegalArgumentException()

    if(states.size == 1) {
      return (g, states.head, Relation.identity[String])
    }

    (states.tail.foldLeft
      ((g, states.head, Relation.empty[String,String]))
      ((result, state) => {
        val (lastGraph, lastGraphIn, _) = result
        val (nextGraph, _, equiv) = 
          StateGraphUtils.intersection(
            lastGraph, lastGraphIn, 
            g, state)

        (nextGraph, equiv.findUniqueRightEquivOrFail(state), equiv)
      })
    )
  }

  /**
   * Creates a graph which represents the intersection of the two
   * provided graphs from their respective chosen starting points,
   * along with two sets that relate the states
   * from each graph to their equivalents in the intersection graph.
   */
  def intersection(
      g1 : StateGraph,
      g1start : String,
      g2 : StateGraph,
      g2start : String) 
      : (StateGraph, StateNameEquiv, StateNameEquiv) = {

    // TODO
    (g1, Relation.empty, Relation.empty)
  }

  case class CannotOverlayException() extends Exception

  /**
   * Creates a new graph by overlaying the second provided graph over the
   * first at their respective chosen states. The new graph will allow
   * all paths that either graph would allow from this point in the new
   * graph.
   * 
   * Where the return types differ on a method that occurs on a
   * shared path (say, type T1 on the method in g1 and T2
   * on the method in g2, where T1 != T2), it must be the case that 
   * T1 <: T2, and the return type of the method on the combined graph will 
   * be T1. If for any method T2 <: T1, a CannotOverlayException will be
   * thrown.
   */
  @throws(classOf[CannotOverlayException])
  def overlay(
      g1 : StateGraph, 
      overlayStates : Set[String], 
      g2 : StateGraph, 
      g2start : String)
      : (StateGraph, StateNameEquiv, StateNameEquiv) = {

    // TODO
    (g1, Relation.empty, Relation.empty)
  }

  case class CannotConnectException() extends Exception

  /**
   * Modifies the graph such that all paths possible from the states in
   * toStates will also be possible from all states in fromStates, and
   * vice versa. Where necessary, return types of methods that occur
   * on shared paths will be joined. If no join exists of any return type
   * pair on a shared path, a CannotConnectException will be thrown.
   *
   * In addition to the modified graph, a set of state names which are
   * equivalent to the original states in the new graph are returned.
   */
  @throws(classOf[CannotConnectException])
  def connect(
      g : StateGraph, 
      fromStates : Set[String], 
      toStates : Set[String])
      : (StateGraph, Set[String]) = {

    (g, Set.empty)
  }

  @throws(classOf[CannotConnectException])
  def connectOpt(
      o1Opt : Option[(StateGraph, Option[Set[String]])],
      o2Opt : Option[(StateGraph, Option[Set[String]])]
      ) : Option[(StateGraph, Option[Set[String]])] = {

    o1Opt.flatMap({ case (g1, st1Opt) => {
      o2Opt.map({ case (g2, st2Opt) => {
        val (combinedGraph, g2Equiv) = includeInto(g1, g2)

        val st2RelabeledOpt = 
          st2Opt.map(_.map(g2Equiv.findUniqueRightEquivOrFail(_)))

        connectStatesOpt(combinedGraph, st1Opt, st2RelabeledOpt)
      }}) orElse (o1Opt)
    }}) orElse (o2Opt)
  }

  @throws(classOf[CannotConnectException])
  def connectStatesOpt(
      g : StateGraph, 
      st1Opt : Option[Set[String]], 
      st2Opt : Option[Set[String]]) 
      : (StateGraph, Option[Set[String]]) =
    st1Opt.map(st1 => {
      st2Opt.map(st2 => {
        val (connectedGraph, connectedStates) =
          StateGraphUtils.connect(g, st1, st2)
        (connectedGraph, Some(connectedStates))
      }) getOrElse((g, st1Opt))
    }) getOrElse((g, st2Opt))

  /**
   * Trims the provided graph such that any states or transitions that are 
   * not visited along a potential path between the provided initial state and 
   * one of the provided end states is removed.
   */
  def trimToPath(
      g : StateGraph,
      fromState : String,
      toStates : Set[String]) 
      : StateGraph = {

    // TODO
    g
  }

  /**
   * Copies graph g2 into g1, relabelling all states in g2 which have names
   * that clash with those in g1. The returned bijective equivalence relation
   * provides a means for relating the state names of g2 to the relabelled
   * equivalents in the combined graph.
   */
  def includeInto(
      g1 : StateGraph, 
      g2 : StateGraph) 
      : (StateGraph, StateNameEquiv) = {

    // if g1 and g2 are the same graph, no-op
    // TODO
    (g1, Relation.empty)
  }

  /**
   * Inspects the two provided graphs for alpha equivalence, using the
   * provided states as a starting point. If the graphs are alpha equivalent,
   * an equivalence relation between the states is returned, otherwise a
   * string describing their inequality is returned.
   */
  def findInconsistency(
      g1 : StateGraph,
      g1start : State,
      g2 : StateGraph, 
      g2start : State,
      varEquiv : Equivalence[TypeVar,TypeVar] = new Equivalence(Map.empty)) 
      : Either[String,Equivalence[State,State]] = {

    val stateEquiv = new Equivalence(Map.empty[State,State])

    var leftNotVisited = g1.nodes.toNodeInSet
    var rightNotVisited = g2.nodes.toNodeInSet

    def checkEdges(a : State, b : State) : Either[String, Set[StatePair]] = {
      val aEdges = ((g1 get a outgoing) toSeq) sortBy (_.m.name)
      val bEdges = ((g2 get b outgoing) toSeq) sortBy (_.m.name)

      if(aEdges.size != bEdges.size)
        return Left("States " + a + " and " + b + 
          ", which should be equivalent, have differing edge sets: " +
          aEdges + " vs " + bEdges)

      val zipEdges = aEdges zip bEdges

      (zipEdges.foldLeft
        (Right(Set.empty) : Either[String, Set[StatePair]])
        ((r, p) => {
          r.right flatMap (successors => {
            val (aEdge, bEdge) = p
            val successor : StatePair = (aEdge.to.value, bEdge.to.value)
            if(aEdge.m.name != bEdge.m.name)
              Left("States " + a + " and " + b + 
                ", which should be equivalent, have differing edge sets: " + 
                aEdges + " vs " + bEdges)
            else if(!aEdge.m.retType.isomorphic(bEdge.m.retType, varEquiv))
              Left("States " + a + " and " + b +
                ", which should be equivalent, have method " + aEdge.m.name +
                " with differing return types: " + aEdge.m.retType +
                " and " + bEdge.m.retType)
            else 
              Right(successors + Pair(aEdge.to.value, bEdge.to.value))
          })
        })
      )
    }

    val noSuccessors = Right(Set.empty[StatePair])

    val mismatch = visit2(g1start, g2start)((statePair) => {
      val (aSource, bSource) = (statePair._1, statePair._2)
      leftNotVisited -= aSource
      rightNotVisited -= bSource

      (stateEquiv.checkEquivalent(aSource, bSource) map 
        (if (_) noSuccessors
         else Left("States " + aSource + " and " + bSource + 
                   " are not equivalent"))
        getOrElse {
          stateEquiv.addEquivalence(aSource, bSource)
          checkEdges(aSource, bSource)
        }
      )
    })

    if(mismatch.isDefined) 
      return Left(mismatch.get)
    if(!leftNotVisited.isEmpty) 
      return Left("States " + leftNotVisited.mkString(", ") + " have no equivalent")
    if(!rightNotVisited.isEmpty)
      return Left("States " + rightNotVisited.mkString(", ") + " have no equivalent")
    
    return Right(stateEquiv)
  }

  /**
   * Performs a guided traversal over two state graphs.
   */
  def visit2[X](
      entry1 : State, 
      entry2 : State)
      (f : (StatePair) => Either[X, collection.Set[StatePair]])
      : Option[X] = {

    var initialPair = (entry1, entry2)
    var visited = Set.empty[StatePair]
    var visitList = Set[StatePair](initialPair)

    while(!visitList.isEmpty) {
      val entry = visitList.head
      visitList -= entry
      visited += entry

      f(entry) match {
        case Left(x) => 
          return Some(x)
        case Right(successors) => 
          visitList ++= successors filterNot (visited.contains(_))
      }
    }

    None
  }

}