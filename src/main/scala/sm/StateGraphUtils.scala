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

import scala.collection.{Set => CSet}

import scalax.collection.GraphPredef._
import scalax.collection.Graph
import scalax.collection.GraphTraversal.VisitorReturn._
import scalax.collection.GraphTraversal._
import scalax.collection.GraphEdge._

import uk.ac.gla.dcs.ts._

object StateGraphUtils {

  def getInnerStatesFromNames(
      g : StateGraph, 
      stateNames : Set[String]) 
      : Set[StateGraph#NodeT] =
    getInnerStates(g, stateNames map (State(_)))


  def getInnerStates(
      g : StateGraph,
      states : Set[State])
      : Set[StateGraph#NodeT] =
    states map (getInnerState(g, _))

  def getInnerState(
      g : StateGraph,
      state : State) : StateGraph#NodeT = { 
    if(!(g contains state)) {
        throw new IllegalArgumentException(
          "State " + state.name + " does not exist in " + g)
      }

    g get state
  }


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

    if(states.isEmpty) throw new IllegalArgumentException()

    val sg = new StateGenerator()

    val innerStates = getInnerStatesFromNames(g, states)

    val initialState = sg()
    var stateMapping : Map[Set[StateGraph#NodeT], State] = 
      Map(innerStates -> initialState)
    var intersectionGraph : StateGraph = Graph(initialState)
    var stateEquiv : Set[(String, String)] = states.map((_, initialState.name))

    visit(innerStates)((stateSet) => {
      val source = stateMapping(stateSet)

      // we are only interested in methods that are available on all the
      // associated states.
      // TODO: there is a cheaper way to do this - as we are interested only
      // in methods which are available in all states, we can do a single pass
      // over the first state's method and check for existence in all other
      // states. This would produce some on-average savings compared to the
      // full set of work that partitionEdges has to do.
      val edgePartition = partitionEdges(stateSet)
      val sharedEdges = 
        edgePartition.shared.filter(_._2.size == stateSet.size)

      val successors = 
        (sharedEdges map { case (methodName, edgeSet) => {
        
          val newReturnType = edgeSet.map(_.edge.m.retType).reduce(JoinTE(_, _))
          val targetSet = edgeSet.map(_.edge.to)
          val newTarget = stateMapping.getOrElse(targetSet, sg())
          stateMapping += targetSet -> newTarget

          targetSet.foreach(s => stateEquiv += s.value.name -> newTarget.name)

          intersectionGraph += 
            source ~> newTarget by Method(methodName, newReturnType)

          targetSet
        }}).toSet

      Right(successors)
    })

    (intersectionGraph, initialState.name, Relation(stateEquiv))
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

    val (combinedGraph, includeEquiv) = includeInto(g1, g2)
    val g2startRelabeled = includeEquiv.findUniqueRightEquivOrFail(g2start)

    val states = Set(g1start, g2startRelabeled)

    val (intersectionGraph, _, intersectionEquiv) = 
      internalIntersection(combinedGraph, states)

    val g1Equiv = intersectionEquiv.subset(g1.nodes.map(_.value.name).toSet)

    val g2statesRelabeled = 
      g2.nodes.
      map(n => includeEquiv.findUniqueRightEquivOrFail(n.value.name)).
      toSet

    val g2Equiv = 
      intersectionEquiv.subset(g2statesRelabeled)


    (intersectionGraph, g1Equiv, g2Equiv)
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

  case class EdgePartition(
    disjoint : Set[StateGraph#EdgeT], 
    shared : Map[String,Set[StateGraph#EdgeT]])

  def partitionEdges(states : Set[_ <: StateGraph#NodeT]) 
    : EdgePartition = {

    val allEdges = states.flatMap(_.outgoing.toSeq)
    val methodMap = 
      (allEdges.foldLeft
        (Map.empty[String,Set[StateGraph#EdgeT]])
        ((m, e) => {
          val methodName = e.edge.m.name
          val edgeSet = m.getOrElse(methodName, Set.empty[StateGraph#EdgeT])
          m.updated(methodName, (edgeSet + e))
        })
      )

    val (sharedMap, disjointMap) = 
      methodMap.partition { case (methodName, edges) => edges.size > 1 }

    val disjointEdges = 
      disjointMap.values.reduceOption(_ ++ _).getOrElse(Set.empty)

    EdgePartition(disjointEdges, sharedMap)
  }

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
      states : Set[State])
      : (StateGraph, State, StateNameEquiv) = {

    val innerStates : Set[StateGraph#NodeT] = getInnerStates(g, states)
    val sg = new StateGenerator(g.nodes.toNodeInSet)

    // 1. clone the graph, removing all the states to be connected

    var connectedGraph = g -- innerStates

    // add all the unchanged states to the state equivalence relation
    var stateEquiv : Set[(String, String)] = 
      connectedGraph.nodes.map((n : StateGraph#NodeT) => 
        n.value.name -> n.value.name).toSet

    // 2. replace with a single new state that is the union of all the
    //    states.

    val connectedState = sg()
    connectedGraph += connectedState
    val connectedStateInner = connectedGraph get connectedState
    
    var newStateMap : Map[Set[_ <: StateGraph#NodeT], State] = 
      Map(innerStates -> connectedState)

    // all the states to be connected are equivalent to the newly created
    // state, so add this to the equivalence relation
    stateEquiv ++= innerStates.map(is => (is.value.name, connectedState.name))

    def replaceState(s : State) = if(states contains s) connectedState else s

    // 2a. derive the union of all the states to be connected
    visit(innerStates)((stateSet) => {
      val newSource = newStateMap(stateSet)

      val edgePartition = partitionEdges(stateSet)

      // add all disjoint edges, directed to their original targets
      connectedGraph ++= 
        edgePartition.disjoint.map(e => {
          newSource ~> replaceState(e.edge.to.value) by e.edge.m
        })

      // for each shared edge set, join the method return types 
      // and produce a new target
      val visitList = edgePartition.shared.map(methodEdgeSet => {
        val (methodName, edgeSet) = methodEdgeSet

        val newReturnType = edgeSet.map(_.edge.m.retType).reduce(JoinTE(_, _))
        val targetSet = edgeSet.map(_.edge.to)
        val newTarget = newStateMap.getOrElse(targetSet, sg())
        newStateMap += targetSet -> newTarget

        targetSet.foreach(s => stateEquiv += s.value.name -> newTarget.name)

        connectedGraph += 
          newSource ~> newTarget by Method(methodName, newReturnType)

        targetSet
      }).toSet

      Right(visitList)
    })

    // 3. All transitions directed into the set of states to be connected
    //    should now all be directed to the single replacement state

    val edges : Set[StateGraph#EdgeT] = innerStates.flatMap(_.incoming.toSeq)
    edges.foreach(e => {
      val source = replaceState(e.edge.from.value)
      val target = replaceState(e.edge.to.value)
      connectedGraph += source ~> target by e.edge.m
    })

    (connectedGraph, connectedState, Relation(stateEquiv))
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
        val (connectedGraph, connectedState, _) =
          StateGraphUtils.connect(g, (st1 ++ st2).map(State(_)))
        (connectedGraph, Some(Set(connectedState.name)))
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
    
    var nodesOnPath = Set.empty[g.NodeT]

    val start : g.NodeT = g get State(fromState)
    val ends : Set[g.NodeT] = toStates.map(g get State(_))

    start.traverseDownUp()(
      nodeDown = (n : g.NodeT) => {
        if((ends contains n) || ends.exists(n.diSuccessors contains _)) {
          nodesOnPath += n
        }
        Continue
      },
      nodeUp = (n : g.NodeT) => {
        if(n.diSuccessors.exists(nodesOnPath contains _)) {
          nodesOnPath += n
        }
      })

    val nodesToTrim = g.nodes -- nodesOnPath
    g -- nodesToTrim
  }

  def findUnconnected(
      graph : StateGraph, 
      from : State) 
      : StateGraph#NodeSetT = {
    var unconnected = graph.nodes
    (graph get from).traverse()(n => {
      unconnected -= n
      Continue
    })
    unconnected
  }

  def findUnCoConnected(
      graph : StateGraph, 
      exitSet : Set[State], 
      sg : StateGenerator) 
      : StateGraph#NodeSetT = {

    var unCoConnected = graph.nodes

    val edgeFilter = (e : graph.EdgeT) =>
      (unCoConnected contains e.from) ||
      (unCoConnected contains e.to)

    exitSet.foreach(n => (graph get n).traverse
      (direction = Predecessors, 
        edgeFilter = edgeFilter)
      ((n2 : graph.NodeT) => {
        unCoConnected -= n2
        Continue
      })
    )

    
    unCoConnected
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

    val stateGen = new StateGenerator(g1.nodes.toNodeInSet)
    val relabelRelation = Relation(g2.nodes.map(n => {
      val name = n.value.name
      (name, stateGen.replace(name))
    }).toSet)

    val relabeledStates : CSet[State] = g2.nodes.map(n => 
      State(relabelRelation.findUniqueRightEquivOrFail(n.value.name)))

    val relabeledEdges : CSet[Transition[State]] = g2.edges.map(e => {
      val newFromName = 
        relabelRelation.findUniqueRightEquivOrFail(e.from.value.name)
      val newToName =
        relabelRelation.findUniqueRightEquivOrFail(e.to.value.name)

      Transition(State(newFromName), State(newToName), e.m)
    })

    val g3 : StateGraph = relabeledStates.foldLeft(g1)(_ + _)
    val g4 : StateGraph = relabeledEdges.foldLeft(g3)(_ + _)
    
    (g4, relabelRelation)
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

    if(!(g1 contains g1start) || !(g2 contains g2start))
      throw new IllegalArgumentException()

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

  def visit[X, Y](start : X)(f : X => Either[Y, Set[X]]) : Option[Y] = {
    var visited = Set.empty[X]
    var visitList = Set(start)

    while(!visitList.isEmpty) {
      val next = visitList.head
      visitList -= next
      visited += next

      f(next) match {
        case Left(y) => return Some(y)
        case Right(successors) =>
          visitList ++= successors filterNot (visited contains _)
      }
    }

    None
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