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

import uk.ac.gla.dcs.ts.TypeExpr
import uk.ac.gla.dcs.ts.VarTE
import uk.ac.gla.dcs.ts.TypeVar

import scala.math.max

import scala.collection.{Set => CSet}
import scalax.collection.GraphPredef._
import scalax.collection.Graph
import scalax.collection.GraphTraversal._
import scalax.collection.GraphTraversal.VisitorReturn._
import scalax.collection.GraphEdge._

import scalax.collection.edge.Implicits._

/**
 * A representation of finite state machines, which have the following
 * properties:
 *
 * - There is a single entry state (determinism)
 * - For each state, there are no two outgoing edges which have the same
 *   method label (determinism)
 * - There is a path from the entry state to every state (connected)
 * - There is a path from every state to an exit state (co-connected)
 */
class StateMachine(
  val graph : StateGraph, 
  val entry : State, 
  val exitSet : Set[State], 
  stateGenOpt : Option[StateGenerator] = None) {

  /** commonly used type aliases */
  type SMNode = StateGraph#NodeT
  type SMEdge = StateGraph#EdgeT
  type EdgePair = Pair[SMEdge, SMEdge]
  type EdgeSet = CSet[_ <: SMEdge]
  case class EdgePartition(
    leftOnly : EdgeSet, 
    shared : CSet[EdgePair],
    rightOnly : EdgeSet)

  val stateGen = stateGenOpt getOrElse(new StateGenerator(this))

  /*********************** invariant checking code ****************************/
  def checkInvariants() = {
    if(graph find entry isEmpty)
      throw new IllegalArgumentException(
        "entry state " + entry + " not in graph")

    if(exitSet.isEmpty)
      throw new IllegalArgumentException("no exit states specified")

    val missingExits = exitSet filter (graph find _ isEmpty)
    if(missingExits.size > 0)
      throw new IllegalArgumentException(
        "exit states not in graph: " + missingExits)

    val unconnected = StateGraphUtils.findUnconnected(graph, entry)
    if(unconnected.size > 0)
      throw new IllegalArgumentException(
        "no path exists from entry state " + entry + 
        " to states: " + unconnected.mkString("{ ", ", ", " }"))

    val unCoConnected = StateGraphUtils.findUnCoConnected(graph, exitSet, stateGen.copy())
    if(unCoConnected.size > 0)
      throw new IllegalArgumentException(
        "states " + unCoConnected.mkString("{ ", ", ", " }") + 
        " have no path to an exit state " + exitSet.mkString("{ ", ", ", " }") +
        " in graph " + graph)
  }
  checkInvariants()
  /******************* end of invariant checking code *************************/

  /**
   * A standard form state machine is one which contains no transitions
   * directed towards its initial state.
   */
  def isStandardized : Boolean = (graph get entry incoming) isEmpty

  /**
   * Transforms a state machine such that it is standardized.
   */
  def standardize() : StateMachine = {
    if(isStandardized) return this
    
    val sg = stateGen.copy()
    val newEntryState = sg()

    val entryEdges = (graph get entry outgoing)

    val newEntryEdges = entryEdges map (e => {
      val target = e.to.value
      val method = e.m
      newEntryState ~> target by method
    })

    val newExitSet = 
      if(exitSet contains entry) exitSet + newEntryState else exitSet

    new StateMachine(
      graph + newEntryState ++ newEntryEdges, 
      newEntryState, 
      newExitSet,
      Some(sg))
  }

  /**
   * Computes the intersection of this state machine and the provided
   * state machine. The resulting state machine will allow any trace
   * that is allowed by both state machines, and no others.
   */
  def intersection(other : StateMachine, label : String = "") : StateMachine = {
    if(this eq other) return this

    val (intersectionGraph, thisEquiv, otherEquiv) = 
      StateGraphUtils.intersection(
        this.graph, this.entry.name, 
        other.graph, other.entry.name)

    val intersectionEquiv = thisEquiv.rightIntersection(otherEquiv)

    val intersectionEntry = 
      State(intersectionEquiv.findUniqueRightEquivOrFail(
        (this.entry.name, other.entry.name)))

    val exitPairs = this.exitSet.flatMap(e => 
      other.exitSet.map(e2 => (e.name,e2.name)))

    val intersectionExitSet = exitPairs.flatMap(p =>
      intersectionEquiv.findRightEquivs(p).map(State(_)))

    val (trimmedGraph, trimmedExitSet) =
      trim(intersectionGraph, intersectionEntry, intersectionExitSet)

    StateMachine(trimmedGraph, intersectionEntry, trimmedExitSet)
  }

  /**
   * Computes the union of this state machine with the provided
   * state machine. The resulting state machine will allow any
   * trace that is allowed by either state machine, and no others.
   */
  def union(other : StateMachine) : StateMachine = {
    if(this eq other) return this

    val leftStandard = this.standardize()
    val leftGraph = leftStandard.graph
    val leftStates = leftGraph.nodes.toNodeInSet
    
    val rightStandard = other.relabel(leftStates).standardize()
    val rightStates = rightStandard.graph.nodes.toNodeInSet

    val leftWithoutEntry = (leftStandard.graph - leftStandard.entry)
    val rightWithoutEntry = (rightStandard.graph - rightStandard.entry)

    var unionGraph = leftWithoutEntry ++ rightWithoutEntry

    val sg = new StateGenerator(unionGraph.nodes.toNodeInSet)
    val newEntry = sg()
    var newExitSet = leftStandard.exitSet ++ rightStandard.exitSet
    var newStates = Map((leftStandard.entry, rightStandard.entry) -> newEntry)

    leftStandard.visit2(rightStandard)(statePair => {
      val (left, right) = statePair
      val newSource = newStates(statePair)

      val partition = 
        partitionEdges(
          leftStandard.graph get left, 
          rightStandard.graph get right)

      unionGraph ++= 
        partition.leftOnly map (e => (newSource ~> e.edge.to.value by e.edge.m))
      unionGraph ++= 
        partition.rightOnly map (e => (newSource ~> e.edge.to.value by e.edge.m))

      // for each shared edge, "meet" the method and produce a new target
      val visitList = partition.shared map (edgePair => {
        val (leftEdge, rightEdge) = (edgePair._1.edge, edgePair._2.edge)
        val newTarget = sg()
        val mergedMethod = leftEdge.m meet rightEdge.m
        newStates += (leftEdge.to.value, rightEdge.to.value) -> newTarget
        unionGraph += newSource ~> newTarget by mergedMethod

        if((leftStandard.exitSet contains leftEdge.to.value) ||
           (rightStandard.exitSet contains rightEdge.to.value)) {
          newExitSet += newTarget
        }

        (leftEdge.to.value, rightEdge.to.value)
      }) toSet

      Right(visitList)
    })

    val (trimUnionGraph, trimExitSet) = trim(unionGraph, newEntry, newExitSet)

    StateMachine(trimUnionGraph, newEntry, trimExitSet)
  }

  /**
   * Partitions the edges of s1 and s2 based on method name into sets
   * consisting of:
   * - those which are found in s1 only
   * - those which are found in both s1 and s2
   * - those which are found in s2 only
   */
  private def partitionEdges(s1 : SMNode, s2 : SMNode) 
    : EdgePartition = {

    val s1Edges : EdgeSet = s1 outgoing
    val s2Edges : EdgeSet = s2 outgoing

    val sharedEdges : CSet[EdgePair] = s1Edges.flatMap(s1e => {
        val s2eOpt : Option[SMEdge] = 
          s2Edges.toSeq.find(s2e => {
            s2e.edge.m.name == s1e.edge.m.name
          })
        s2eOpt.map(Pair(s1e, _)).toList
      })

    val s1Only = s1Edges.filter(s1e => sharedEdges find (_._1 eq s1e) isEmpty)
    val s2Only = s2Edges.filter(s2e => sharedEdges find (_._2 eq s2e) isEmpty)

    EdgePartition(s1Only, sharedEdges, s2Only)
  }

  /**
   * Removes all states from the specified graph which are not connected
   * to the specified entry state, or are not co-connected to any of the 
   * specified exit states, and all edges associated to these states.
   * If the resulting graph has no path from the entry state to an exit
   * state, the resulting graph will be equivalent to the "empty"
   * state machine's graph.
   */
  private def trim(
    graph : StateGraph, 
    entry : State, 
    exitSet : Set[State]) 
    : (StateGraph, Set[State]) = {

    val sg = new StateGenerator(graph.nodes.toNodeInSet)
    val entryInner = graph get entry
    var unconnected = StateGraphUtils.findUnconnected(graph, entry)
    val unCoConnected = StateGraphUtils.findUnCoConnected(graph, exitSet, sg)

    val trimmedGraph = graph -- unconnected -- unCoConnected
    val trimmedExitSet = exitSet -- unconnected.toNodeInSet

    if(trimmedExitSet.isEmpty)
      (Graph(entry), Set(entry))
    else
      (trimmedGraph, trimmedExitSet)
  }

  def relabel(exclusions : CSet[State]) : StateMachine = {
    val sg = new StateGenerator(exclusions)
    val substitution : Map[State, State] = 
      graph.nodes.toNodeInSet map(Pair(_, sg())) toMap
    val subEdges = graph.edges map(e => 
      substitution(e.from.value) ~> substitution(e.to.value) by e.m)

    val newGraph : StateGraph = Graph.from(substitution.values, subEdges)
    val newEntry = substitution(entry)
    val newExitSet = exitSet map (substitution(_))

    StateMachine(newGraph, newEntry, newExitSet)
  }

  def overlay(
    g1 : StateGraph, 
    s1 : State,
    s2 : State) 
    : (StateGraph, Set[StatePair]) = {

    var equivPairs = Set.empty[StatePair]
    var overlaidGraph = g1
    StateGraphUtils.visit2(s1, s2)(statePair => {
      val (left, right) = statePair
      equivPairs += statePair

      val partition = 
        partitionEdges(overlaidGraph get left, overlaidGraph get right)

      overlaidGraph ++= 
        partition.rightOnly map (e => (left ~> e.edge.to.value by e.edge.m))

      // for each shared edge, "meet" the method and produce a new target
      val visitList = partition.shared map (edgePair => {
        val (leftEdge, rightEdge) = (edgePair._1.edge, edgePair._2.edge)
        val mergedMethod = leftEdge.m meet rightEdge.m
        overlaidGraph -= (left ~> leftEdge.to.value) by leftEdge.m
        overlaidGraph += (left ~> leftEdge.to.value) by mergedMethod

        (leftEdge.to.value, rightEdge.to.value)
      }) toSet

      Right(visitList)
    })

    (overlaidGraph, equivPairs)
  }

  /**
   * Given the language L accepted by 
   * this state machine and the language L' accepted by the provided
   * state machine, the state machine produced by this method will
   * accept any trace in the language L.L'
   */
  def then(other : StateMachine) : StateMachine = {
    val otherStandard = other.relabel(this.graph.nodes.toNodeInSet).standardize

    // apply this.unionAt(exit, otherStandard)
    // for each exit

    val otherEntryInner = otherStandard.graph get otherStandard.entry
    val otherEntryEdges = otherEntryInner outgoing

    val (combinedGraph, equivStates) = 
      (this.exitSet.foldLeft
        (Pair((this.graph ++ otherStandard.graph), Set.empty[StatePair]))
        ((p, e) => {
          val (g, equivStates) = p
          val (g2, equivStates2) = overlay(g, e, otherStandard.entry)
          (g2, equivStates ++ equivStates2)
        })
      )

    val newExits = equivStates.flatMap(p => {
      val (left, right) = p
      if((otherStandard.exitSet contains right)) Set(left)
      else Set.empty[State]
    })

    val allExits = otherStandard.exitSet ++ newExits

    val (trimmedGraph, trimmedExits) = trim(combinedGraph, this.entry, allExits)

    StateMachine(trimmedGraph, this.entry, trimmedExits)
  }

  def alphaEquivalent(other : StateMachine) : Boolean =
    findInconsistency(other : StateMachine) isEmpty

  /**
   * Determines whether the two state machines have the same structure,
   * up to alpha equivalence of state labels.
   */
  def findInconsistency(other : StateMachine) : Option[String] = {

    if(this.exitSet.size != other.exitSet.size)
      return Some("state machines have exit sets of different sizes")

    val equivResult = StateGraphUtils.findInconsistency(
      this.graph, this.entry,
      other.graph, other.entry)

    equivResult match {
      case Left(mismatch) => Some(mismatch)
      case Right(stateEquiv) => {
        val exitSetEquiv = this.exitSet.forall(exit => {
          val equivOpt = stateEquiv.getRightEquivalent(exit)
          equivOpt.map(other.exitSet contains _).getOrElse(false)
        })

        if(!exitSetEquiv) Some("Exit sets are not equivalent") else None
      }
    }
  }

  /**
   * Performs a traversal of both this state machine and the specified
   * state machine, starting from the entry states of both.
   * The supplied function is used to determine whether to continue the
   * traversal, and if so to which states. If the function returns
   * Left(x) at any point then the traversal halts and Some(x) is returned.
   * Otherwise, traversal will continue until all successor pairs generated
   * by repeated application of the function have all been visited exactly once.
   */
  def visit2[X](other : StateMachine)
    (f : (StatePair) => Either[X, collection.Set[StatePair]])
    : Option[X] = 
    StateGraphUtils.visit2(this.entry, other.entry)(f)


  override def toString =
    "<" + graph.toString + 
    ", entry: " + entry + 
    ", exits: " + exitSet.mkString(", ") +
    ">"
}

object StateMachine {
  def apply(graph : StateGraph, entry : State, exitSet : Set[State]) =
    new StateMachine(graph, entry, exitSet, None)
}


case class Method(name : String, retType : TypeExpr) {

  def join(other : Method) : Method = {
    if(other.name != this.name) throw new IllegalArgumentException()
    this
  }

  def meet(other : Method) : Method = {
    if(other.name != this.name) throw new IllegalArgumentException()
    this
  }
}


final class StateGenerator(
  private var last : Int = 0,
  private var exclusions : Set[String] = Set.empty) {

  def this(stateExclusions : CSet[State]) = 
    this(0, stateExclusions map(_.name) toSet)

  def this(sm : StateMachine) = this(sm.graph.nodes.toNodeInSet)

  private def gen() : String = {
    last += 1
    "S" + last
  }

  def replace(name : String) : String = {
    if(exclusions contains name) next() else name
  }

  def next() : String = {
    var desc = gen()
    while(exclusions contains desc) desc = gen()
    desc
  }

  def apply() = {
    State(next())
  }

  def copy() = new StateGenerator(last, exclusions)
}