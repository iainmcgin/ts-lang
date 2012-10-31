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

import sm._

import scalax.collection.Graph
import scalax.collection.GraphPredef._
import scalax.collection.GraphEdge._
import uk.ac.gla.dcs.ts.sm.StateGraph

class ObjectConstraintSolver(private[ts] val constraints : Seq[TypeConstraint]) {

  private[ts] var objects = new VarSolutionSet[StateGraph]()
  private[ts] var states = new VarSolutionSet[Set[String]]()

  // solving cases:
  // 1. solve subtype constraint where upper bound solved
  // 2. solve remap where effect is solved
  // 3. solve equality
  // 4. solve join / meet

  // we assume all constraints have been type-normalised
  // so that wherever a type is referred to it is always
  // of form O@S. Specifically, don't want
  // a = O@S join O'@S'
  // instead want
  // O@S = O'@S' join O''@S''

  def solve() {
    val partition = partitionConstraints()
    resolveDirectObjectEqualities(partition.objectEqualities)
    resolveDirectStateEqualities(partition.stateEqualities)

    partition.definitions.foreach(solveDefinition(_))
  }

  def getSolutionFor(o : ObjectTE) : Option[SolvedObjectTE] = {
    val objGraphOpt = objects.getSolution(o.objVar)
    val statesOpt = states.getSolution(o.stateVar)

    objGraphOpt.flatMap(graph => statesOpt.map(states => 
      SolvedObjectTE(graph, states)
    ))
  }

  type DirectEquality = Pair[TypeVar, TypeVar]
  type Definition = Pair[ObjectTE, TypeExpr]

  case class ConstraintPartition(
    objectEqualities : Seq[DirectEquality],
    stateEqualities : Seq[DirectEquality],
    subtypes : Seq[SubtypeConstraint],
    definitions : Seq[Definition]
  )

  private[ts] def partitionConstraints() : ConstraintPartition =
    (constraints.foldLeft
      (ConstraintPartition(Seq.empty, Seq.empty, Seq.empty, Seq.empty))
      ((result, constraint) => {
        constraint match {
          case ec @ EqualityConstraint(a,b) => {
            (a, b) match {
              case (ObjectTE(o1,s1), ObjectTE(o2,s2)) =>
                // direct equality of object and state variables
                result.copy(
                  objectEqualities = (o1,o2) +: result.objectEqualities,
                  stateEqualities = (s1,s2) +: result.stateEqualities)

              case (o @ ObjectTE(o1,s1), other) =>
                // a definition of some sort
                other match {
                  case RemapTE(ObjectTE(o2,_), _) =>
                    // remap implies the input object variable and
                    // the result object variable are equal
                    result.copy(
                      objectEqualities = (o1,o2) +: result.objectEqualities,
                      definitions = (o, other) +: result.definitions)
                  case _ =>
                    result.copy(definitions = (o, other) +: result.definitions)
                }
              case _ =>
                throw new IllegalArgumentException()
            }
          }
          case sc @ SubtypeConstraint(_,_) => {
            result.copy(subtypes = sc +: result.subtypes)
          }
        }
      })
    )
  
  private[ts] def resolveDirectObjectEqualities(
      equalities : Seq[DirectEquality]) {
    equalities.foreach { case Pair(o1, o2) => {
      objects.makeEquivalent(o1, o2)
    }}
  }

  private[ts] def resolveDirectStateEqualities(
      equalities : Seq[DirectEquality]) {
    equalities.foreach { case Pair(s1, s2) => { 
      states.makeEquivalent(s1, s2) 
    }}
  }

  def solveSubtype(child : TypeExpr, parent : TypeExpr) {
    // patch parent into child
  }

  def solveDefinition(defn : Definition) {
    val (obj, objDefn) = defn
    objDefn match {
      case SolvedObjectTE(states, state) => {
        // how literally do we interpret equality here?
      }
      case JoinTE(left @ ObjectTE(_,_), right @ ObjectTE(_,_)) => {
        solveJoin(obj, left, right)
      }
      case MeetTE(left @ ObjectTE(_,_), right @ ObjectTE(_,_)) => {
        val meetObj = solveMeet(left, right)

      }
      case RemapTE(input @ ObjectTE(_,_), 
                   effect @ EffectTE(_,_)) => {
        solveRemap(obj, input, effect)
      }
      case _ =>
        throw new IllegalArgumentException()
    }
  }

  def solveRemap(
    result : ObjectTE, 
    param : ObjectTE, 
    effect : EffectTE) {

    val (paramGraph, paramStates, afterEffectStates) = 
      refineParamSolutionWithEffect(param, effect)

    val existingResultGraphOpt = objects.getSolution(result.objVar)
    val existingResultStatesOpt = states.getSolution(result.stateVar)

    val paramAfterEffectSolution = Some(paramGraph, Some(afterEffectStates))
    val existingResultSolution = 
      existingResultGraphOpt.map(rg => (rg, existingResultStatesOpt))

    val (connectedGraph, resultStatesOpt) = 
      StateGraphUtils.connectOpt(
        paramAfterEffectSolution, 
        existingResultSolution).
      get

    val resultStates = resultStatesOpt.get

    objects.makeEquivalent(param.objVar, result.objVar, connectedGraph)
    states.updateSolution(param.stateVar, paramStates)
    states.updateSolution(result.stateVar, resultStates)
  }

  def refineParamSolutionWithEffect(param : ObjectTE, effect : EffectTE) 
      : (StateGraph, Set[String], Set[String]) = {

    val (effectGraph, effectInState, effectOutStates) = 
      normaliseEffect(effect).getOrElse { throw new IllegalStateException() }
    
    val paramObjectGraphOpt = objects.getSolution(param.objVar)
    val paramStatesOpt = states.getSolution(param.stateVar)

    paramObjectGraphOpt.map(graph => {
      paramStatesOpt.map(states => {
        // both param graph and param state set have solutions, so
        // overlay the effect into the param graph, and use this combined 
        // graph to determine the output state set
        val (newGraph, _, effectStateEquiv) = 
          StateGraphUtils.overlay(graph, states, effectGraph, effectInState)

        val outStates = 
          effectOutStates.flatMap(effectStateEquiv.findRightEquivs(_))

        (newGraph, states, outStates)
      }) getOrElse {
        // the param graph is known, but the input state is not, so
        // copy the effect graph directly into the param graph, using
        // the effect input state as the solution for the param state set
        val (newGraph, effectStateEquiv) = 
          StateGraphUtils.includeInto(graph, effectGraph)
        val inState = 
          effectStateEquiv.findUniqueRightEquivOrFail(effectInState)
        val outStates = 
          effectOutStates.map(effectStateEquiv.findUniqueRightEquivOrFail(_))

        (newGraph, Set(inState), outStates)
      }
    }) getOrElse {
      // nothing is known of the param graph
      // use the effect graph as the solution for the param graph and
      // the state set
      (effectGraph, Set(effectInState), effectOutStates)
    }
  }
  
  /**
   * If a known solution exists for the object variable and input/output state
   * variables for the provided effect, this solution is transformed 
   * to an equivalent one with the following properties:
   * - There is a single input state
   * - Every state in the graph is connected and co-connected
   */
  def normaliseEffect(effect : EffectTE) 
      : Option[(StateGraph, String, Set[String])] = {

    val effectPathOpt = (effect.in, effect.out) match {
      case (SolvedObjectTE(g1, s1), SolvedObjectTE(g2, s2)) => {
        if(g1 != g2) throw new IllegalArgumentException()
        Some((g1, s1, s2))
      }
      case (ObjectTE(o1, s1), ObjectTE(o2, s2)) => {
        if(!objects.areEquivalent(o1, o2)) throw new IllegalArgumentException()
        
        val objectGraphOpt = objects.getSolution(o1)
        val inStatesOpt = states.getSolution(s1)
        val outStatesOpt = states.getSolution(s2)

        objectGraphOpt.flatMap(g => 
          inStatesOpt.flatMap(in => 
            outStatesOpt.map(out => (g, in, out))
          )
        )
      }
      case _ => throw new IllegalArgumentException("invalid effect")
    }

    effectPathOpt.map({ case (graph, inStates, outStates) => {

      val (intersectionGraph, intersectionInState, stateEquiv) = 
        StateGraphUtils.internalIntersection(graph, inStates)

      val intersectionOutStates = 
        outStates.flatMap(stateEquiv.findRightEquivsOrFail(_))

      val trimGraph = StateGraphUtils.trimToPath(intersectionGraph, 
        intersectionInState, 
        intersectionOutStates)

      (trimGraph, intersectionInState, intersectionOutStates)
    }})
  }

  def solveEquality(left : ObjectTE, right : ObjectTE) {
    // union of two graphs, but with respect to minimality of
    // respective paths. Clean way to split into pre / post sections
    // of each graph, perform union of post parts and direct pre to
    // union part?

    val leftObjOpt = objects.getSolution(left.objVar)
    val leftSolnOpt = 
      leftObjOpt.map(o => (o, states.getSolution(left.stateVar)))

    val rightObjOpt = objects.getSolution(right.objVar)
    val rightSolnOpt = 
      rightObjOpt.map(o => (o, states.getSolution(right.stateVar)))

    val solnOpt = StateGraphUtils.connectOpt(leftSolnOpt, rightSolnOpt)

    objects.makeEquivalent(left.objVar, right.objVar)
    states.makeEquivalent(left.stateVar, right.stateVar)

    solnOpt.map(soln => {
      val (obj, statesOpt) = soln
      objects.makeEquivalent(left.objVar, right.objVar, obj)
      statesOpt.map(states.makeEquivalent(left.stateVar, right.stateVar, _))
    })
  }

  def solveJoin(result : ObjectTE, left : ObjectTE, right : ObjectTE) {
    // union of graphs, if they are different objects
    // otherwise, state set union
  }

  def solveMeet(left : ObjectTE, right : ObjectTE) : SolvedObjectTE = {
    // intersection of graphs, irrespective of whether they
    // are the same object or not?
    throw new IllegalArgumentException()
  }
}