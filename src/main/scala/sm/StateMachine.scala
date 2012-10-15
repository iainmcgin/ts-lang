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
  private type StatePair = Pair[State, State]
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

    val unconnected = StateMachine.findUnconnected(graph, entry)
    if(unconnected.size > 0)
      throw new IllegalArgumentException(
        "no path exists from entry state " + entry + 
        " to states: " + unconnected.mkString("{ ", ", ", " }"))

    val unCoConnected = StateMachine.findUnCoConnected(graph, exitSet, stateGen.copy())
    if(unCoConnected.size > 0)
      throw new IllegalArgumentException(
        "states {" + unCoConnected.mkString("{ ", ", ", " }") + 
        "} have no path to an exit state " + exitSet)
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

    val sg = new StateGenerator()
    val initialPair = (this.entry, other.entry)
    val initialState = sg()
    var stateMapping = Map(initialPair -> initialState)
    var intersectionGraph : StateGraph = Graph(initialState)

    visit2(other)((statePair) => {
      val (aSource, bSource) = statePair
      val source = stateMapping((aSource, bSource))
      val aEdges = (this.graph get aSource outgoing)
      val bEdges = (other.graph get bSource outgoing)

      val successors = aEdges flatMap (aEdge => {
        bEdges find (_.m == aEdge.m) map (bEdge => {
          val targetPair = (aEdge.to.value, bEdge.to.value)
          val target = stateMapping.getOrElse(targetPair, sg())
          stateMapping = stateMapping.updated(targetPair, target)
          intersectionGraph += (source ~> target by aEdge.m)

          Seq(targetPair)
        }) getOrElse (Seq.empty[StatePair])
      })

      Right(successors)
    })

    val exitMap = stateMapping filter (mapping => {
      val (statePair, _) = mapping
      val (left, right) = statePair
      (this.exitSet contains left) && (other.exitSet contains right)
    })

    val exitSet = Set(exitMap.values toSeq :_*)

    val (trimmedGraph, trimmedExitSet) = 
      trim(intersectionGraph, initialState, exitSet)

    StateMachine(trimmedGraph, initialState, trimmedExitSet)
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
    var unconnected = StateMachine.findUnconnected(graph, entry)
    val unCoConnected = StateMachine.findUnCoConnected(graph, exitSet, sg)

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
    graphVisit2(s1, s2)(statePair => {
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

    var equivStates = Map.empty[(Boolean, State), State]
    var leftNotVisited = this.graph.nodes.toNodeInSet
    var rightNotVisited = other.graph.nodes.toNodeInSet

    def areEquivalent(a : State, b : State) : Option[Boolean] = (
      equivStates get((true, a)) map (_ == b) 
      orElse 
      (equivStates get (false, b) map (_ == a))
    )

    def addEquivalence(a : State, b : State) = {
      equivStates += (true, a) -> b
      equivStates += (false, b) -> a
    }

    def checkEdges(a : State, b : State) : Either[String, Set[StatePair]] = {
      val aEdges = ((this.graph get a outgoing) toSeq) sortBy (_.m.name)
      val bEdges = ((other.graph get b outgoing) toSeq) sortBy (_.m.name)

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
            if(aEdge.m != bEdge.m)
              Left("States " + a + " and " + b + 
                ", which should be equivalent, have differing edge sets: " + 
                aEdges + " vs " + bEdges)
            else Right(successors + Pair(aEdge.to.value, bEdge.to.value))
          })
        })
      )
    }

    val noSuccessors = Right(Set.empty[StatePair])

    val mismatch = visit2(other)((statePair) => {
      val (aSource, bSource) = (statePair._1, statePair._2)
      leftNotVisited -= aSource
      rightNotVisited -= bSource
      (areEquivalent(aSource, bSource) map 
        (if (_) noSuccessors
         else Left("States " + aSource + " and " + bSource + 
                   " are not equivalent"))
        getOrElse {
          addEquivalence(aSource, bSource)
          checkEdges(aSource, bSource)
        }
      )
    })

    if(mismatch.isDefined) 
      return mismatch
    if(!leftNotVisited.isEmpty) 
      return Some("States " + leftNotVisited.mkString(", ") + " have no equivalent")
    if(!rightNotVisited.isEmpty)
      return Some("States " + rightNotVisited.mkString(", ") + " have no equivalent")
    if(!(this.exitSet.forall(other.exitSet contains equivStates(true,_))))
      return Some("Exit sets are not equivalent")
    
    return None
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
    graphVisit2(this.entry, other.entry)(f)

  def graphVisit2[X](
    entry1 : State, 
    entry2 : State)(
    f : (StatePair) => Either[X, collection.Set[StatePair]])
    : Option[X] = {

    // find equivalent transitions, offer to f
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

  override def toString =
    "<" + graph.toString + 
    ", entry: " + entry + 
    ", exits: " + exitSet.mkString(", ") +
    ">"
}

object StateMachine {
  def apply(graph : StateGraph, entry : State, exitSet : Set[State]) =
    new StateMachine(graph, entry, exitSet, None)

  private def findUnconnected(g : StateGraph, from : State) 
    : StateGraph#NodeSetT = {

    var unconnected = g.nodes
    (g get from).traverse()(n => {
      unconnected -= n
      Continue
    })
    unconnected
  }

  private def findUnCoConnected(g : StateGraph, exitSet : Set[State], sg : StateGenerator) 
    : StateGraph#NodeSetT = {

    // create a new fake state that is connected to all the known exit
    // states, and start the reverse traversal from there
    val exitJoinState = sg()
    val extraExitTransitions : Set[GraphParam[State,Transition]] = 
      exitSet map (exit => exit ~> exitJoinState by Method("$$FAKE$$"))
    val graphExitJoined = g + exitJoinState ++ extraExitTransitions

    var unCoConnected = graphExitJoined.nodes

    (graphExitJoined get exitJoinState).
      traverse(direction=Predecessors)(n => {
        unCoConnected -= n
        Continue
      })

    unCoConnected
  }
}


case class Method(name : String) {

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