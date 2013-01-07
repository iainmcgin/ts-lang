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

  def getCurrentSolution(o : ObjectTE) 
      : Option[(StateGraph, Option[Set[String]])] =
    objects.
      getSolution(o.objVar).
      map(os => (os, states.getSolution(o.stateVar)))

  def getSolutionFor(o : ObjectTE) : Option[SolvedObjectTE] = {
    val objGraphOpt = objects.getSolution(o.objVar)
    val statesOpt = states.getSolution(o.stateVar)

    objGraphOpt.flatMap(graph => statesOpt.map(states => 
      SolvedObjectTE(graph, states)
    ))
  }

  def solve() : Boolean = {
    val (objectEqualities, stateEqualities, otherConstraints) = 
      extractEqualities()

    resolveDirectObjectEqualities(objectEqualities)
    resolveDirectStateEqualities(stateEqualities)

    val constraintsByObject = partitionConstraintsByObject(otherConstraints)

    val solveOrder = deriveSolveOrder(constraintsByObject)

    if(solveOrder.isEmpty) return false;

    solveOrder.get.foreach(o => solveConstraints(constraintsByObject(o)))

    return true;
  }

  type DirectEquality = Pair[TypeVar, TypeVar]

  /**
   * Extracts direct equalities between object variables and state variables
   * from the constraint set, where the equality is either explicitly stated
   * or implied as part of some more complex constraint.
   */
  def extractEqualities() 
      : (Set[DirectEquality], Set[DirectEquality], Seq[TypeConstraint]) = {
    (constraints.foldLeft 
      ((Set.empty[DirectEquality], Set.empty[DirectEquality], Seq.empty[TypeConstraint]))
      { case ((objectEqualities, stateEqualities, others), constraint) =>
        constraint match {
          case EqualityConstraint(ObjectTE(o1,s1), other) => other match {
            case ObjectTE(o2, s2) =>
              (objectEqualities + (o1 -> o2),
               stateEqualities + (s1 -> s2),
               others)
            case RemapTE(
              ObjectTE(o2,_), 
              EffectTE(ObjectTE(o3,s3),ObjectTE(o4,s4))) =>
              (objectEqualities + (o1 -> o2) + (o3 -> o4), 
               stateEqualities,
               constraint +: others)
            case _ => (objectEqualities, stateEqualities, constraint +: others)
          }
          case _ => (objectEqualities, stateEqualities, constraint +: others)
        }
      }
    )
  }

  private[ts] def resolveDirectObjectEqualities(
      equalities : Set[DirectEquality]) {
    equalities.foreach { case Pair(o1, o2) => {
      objects.makeEquivalent(o1, o2)
    }}
  }

  private[ts] def resolveDirectStateEqualities(
      equalities : Set[DirectEquality]) {
    equalities.foreach { case Pair(s1, s2) => { 
      states.makeEquivalent(s1, s2) 
    }}
  }

  type ConstraintsByObject = Map[TypeVar, Seq[TypeConstraint]]

  def partitionConstraintsByObject(constraints : Seq[TypeConstraint])
      : ConstraintsByObject = {

    (constraints.foldLeft
      (Map.empty[TypeVar, Seq[TypeConstraint]].withDefaultValue(Seq.empty))
      ((map, constraint) => constraint match {
        case EqualityConstraint(ObjectTE(o1,_), other) => {
          val canonical = objects.getCanonicalEquiv(o1)
          map + (canonical -> (constraint +: map(canonical)))
        }
        case SubtypeConstraint(ObjectTE(o1,_), _) => {
          val canonical = objects.getCanonicalEquiv(o1)
          map + (canonical -> (constraint +: map(canonical)))
        }
        case _ => map
      })
    )
  }

  def deriveSolveOrder(constraints : ConstraintsByObject) : Option[Seq[TypeVar]] = {

    type DependentsMap = Map[TypeVar, Set[TypeVar]]
    type DependencyCount = Map[TypeVar, Int]
    type DependencyInfo = (DependentsMap, DependencyCount)

    def addDependency(dep : (TypeVar, TypeVar), depInfo : DependencyInfo)
        : DependencyInfo = {
      val dependent = objects.getCanonicalEquiv(dep._1)
      val dependee = objects.getCanonicalEquiv(dep._2)
      val (dependents, dependencyCount) = depInfo
      val oldDeps = dependents.getOrElse(dependee, Set.empty)
      val oldDepCount = dependencyCount.getOrElse(dependent, 0)

      if(!oldDeps.contains(dependent)) {
        val newDependents = dependents + (dependee -> (oldDeps + dependent))
        val newDependencyCount = dependencyCount + (dependent -> (oldDepCount + 1))
        (newDependents, newDependencyCount)
      } else {
        depInfo
      }
    }

    val emptyDepInfo = 
      (Map.empty[TypeVar, Set[TypeVar]].withDefaultValue(Set.empty), 
       objects.getCanonicalVars().map(v => (v,0)).toMap)

    val (dependents, dependencyCount) = 
      (constraints.foldLeft
        (emptyDepInfo)
        { case (depInfo, (o1, objConstraints)) =>
          (objConstraints.foldLeft
            (depInfo)
            ((depInfo, constraint) => constraint match {
              case EqualityConstraint(ObjectTE(o1,_), other) => other match {
                // internal join implies no inter-object dependencies
                case JoinTE(_, _) => depInfo
                case SeparateJoinTE(ObjectTE(o2, _), ObjectTE(o3, _)) =>
                  addDependency((o1 -> o2), addDependency((o1 -> o3), depInfo))
                case MeetTE(ObjectTE(o2, _), ObjectTE(o3, _)) =>
                  addDependency((o1 -> o2), addDependency((o1 -> o3), depInfo))
                case RemapTE(_, EffectTE(ObjectTE(o2, _), _)) => {
                  addDependency((o1 -> o2), depInfo)
                }
                case _ => depInfo
              }
            })
          )
        }
      )

    var solveOrder = Vector.empty[TypeVar]
    var depCounts = dependencyCount
    while(!depCounts.isEmpty && depCounts.exists(_._2 == 0)) {
      depCounts.filter(_._2 == 0).foreach { case (o,_) => 
        val canonical = objects.getCanonicalEquiv(o)
        solveOrder :+= canonical
        depCounts -= canonical
        dependents.getOrElse(canonical, Set.empty).foreach { dep =>
          val depCount = math.max(depCounts.getOrElse(dep, 0) - 1, 0)
          depCounts += (dep -> depCount)
        }
      }

    }

    Some(solveOrder)
  }

  def solveConstraints(objConstraints : Seq[TypeConstraint]) = {
    var internalJoins = Seq.empty[(ObjectTE, ObjectTE, ObjectTE)]

    objConstraints.foreach(_ match { 
      case EqualityConstraint(o @ ObjectTE(_,_), other) => other match {
        case SolvedObjectTE(objGraph, objStates) => {
          objects.updateSolution(o.objVar, objGraph)
          states.updateSolution(o.stateVar, objStates)
        }
        case j @ JoinTE(left @ ObjectTE(_,_), right @ ObjectTE(_,_)) =>
          internalJoins +:= (o, left, right)
        case SeparateJoinTE(left @ ObjectTE(_,_), right @ ObjectTE(_,_)) =>
          solveSeparateJoin(o, left, right)
        case MeetTE(left @ ObjectTE(_,_), right @ ObjectTE(_,_)) =>
          solveMeet(o, left, right)
        case RemapTE(input @ ObjectTE(_,_), effect @ EffectTE(_,_)) =>
          solveRemap(o, input, effect)
        case _ =>
          throw new IllegalArgumentException()
      }
    })

    internalJoins.foreach { case (result, left, right) => 
      solveJoin(result, left, right) 
    }
  }

  def solveSubtype(child : TypeExpr, parent : TypeExpr) {
    // patch parent into child
  }

  def solveRemap(
    result : ObjectTE, 
    param : ObjectTE, 
    effect : EffectTE) {

    println(result + " = remap(" + param + ", " + effect + ")")

    val (paramGraph, paramStates, afterEffectStates) = 
      refineParamSolutionWithEffect(param, effect)

    val existingResultGraphOpt = objects.getSolution(result.objVar)
    val existingResultStatesOpt = states.getSolution(result.stateVar)

    println("param solution: " + paramGraph + "@" + paramStates + " >> " + afterEffectStates)
    println("existing result: " + existingResultGraphOpt + "@" + existingResultStatesOpt)

    val paramAfterEffectSolution = Some(paramGraph, Some(afterEffectStates))
    val existingResultSolution = 
      existingResultGraphOpt.map(rg => (rg, existingResultStatesOpt))

    val (connectedGraph, resultStatesOpt) = 
      StateGraphUtils.connectOpt(
        paramAfterEffectSolution, 
        existingResultSolution).
      get

    val resultStates = resultStatesOpt.get

    println("final param/result graph: " + connectedGraph)
    println("final param states: " + paramStates)
    println("final result states: " + resultStates)

    objects.makeEquivalent(param.objVar, result.objVar, connectedGraph)
    states.updateSolution(param.stateVar, paramStates)
    states.updateSolution(result.stateVar, resultStates)
  }

  def refineParamSolutionWithEffect(param : ObjectTE, effect : EffectTE) 
      : (StateGraph, Set[String], Set[String]) = {

    println("refining " + param + " with " + effect)

    val (effectGraph, effectInState, effectOutStates) = 
      normaliseEffect(effect).getOrElse { throw new IllegalStateException() }
    
    println("effect is " + effectGraph + "@" + effectInState + " >> " + effectOutStates)

    val paramObjectGraphOpt = objects.getSolution(param.objVar)
    val paramStatesOpt = states.getSolution(param.stateVar)

    val (paramGraph, paramStates, paramAfterEffectStates) = 
      paramObjectGraphOpt.map(graph => {
        paramStatesOpt.map(states => {
          // both param graph and param state set have solutions, so
          // overlay the effect into the param graph, and use this combined 
          // graph to determine the output state set

          println("existing solution for param: " + graph + "@" + states)
          val (newGraph, effectStateEquiv) = 
            StateGraphUtils.overlay(graph, states, effectGraph, effectInState)

          println("equiv: " + effectStateEquiv)
          println("effect out: " + effectOutStates)

          val outStates = 
            effectOutStates.flatMap(effectStateEquiv.findRightEquivs(_))

          (newGraph, states, outStates)
        }) getOrElse {
          // the param graph is known, but the input state is not, so
          // copy the effect graph directly into the param graph, using
          // the effect input state as the solution for the param state set
          println("graph exists for param: " + graph)
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
        println("nothing known of param")
        (effectGraph, Set(effectInState), effectOutStates)
      }

    objects.updateSolution(param.objVar, paramGraph)
    states.updateSolution(param.stateVar, paramStates)

    (paramGraph, paramStates, paramAfterEffectStates)
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
      println("effect before normalisation: " + graph + "@" + inStates + " >> " + outStates)
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

    val leftSolnOpt = getCurrentSolution(left)
    val rightSolnOpt = getCurrentSolution(right)

    val solnOpt = StateGraphUtils.connectOpt(leftSolnOpt, rightSolnOpt)

    objects.makeEquivalent(left.objVar, right.objVar)
    states.makeEquivalent(left.stateVar, right.stateVar)

    solnOpt.map(soln => {
      val (obj, statesOpt) = soln
      objects.makeEquivalent(left.objVar, right.objVar, obj)
      statesOpt.map(states.makeEquivalent(left.stateVar, right.stateVar, _))
      println("equality solution: " + obj + "@" + statesOpt)
    })
  }

  def solveJoin(result : ObjectTE, left : ObjectTE, right : ObjectTE) {
    // the object variables must be equal,
    // solution to state set is union of left and right state sets
  }

  def solveSeparateJoin(result : ObjectTE, left : ObjectTE, right : ObjectTE) {
    // the left and right objects are not equal
    // compute intersection of the two solutions, this is then
    // the result

    val leftSolnOpt = getSolutionFor(left)
    val rightSolnOpt = getSolutionFor(right)

    if(leftSolnOpt.isEmpty || rightSolnOpt.isEmpty) {
      throw new IllegalArgumentException("no solution for join components")
    }

    val leftSoln = leftSolnOpt.get
    val rightSoln = rightSolnOpt.get

    val (leftGraph, leftStart, _) = 
      StateGraphUtils.internalIntersection(leftSoln.graph, leftSoln.states)
    val (rightGraph, rightStart, _) =
      StateGraphUtils.internalIntersection(rightSoln.graph, rightSoln.states)

    val (intersectionGraph, leftEquiv, _) =
      StateGraphUtils.intersection(
        leftGraph, leftStart, 
        rightGraph, rightStart)

    val intersectionStart = leftEquiv.findUniqueRightEquivOrFail(leftStart)


    val joinSolution = (intersectionGraph, Option(Set(intersectionStart)))

    val resultSolnOpt = getCurrentSolution(result)

    val (resultGraph, resultStatesOpt) = 
      StateGraphUtils.connectRightOpt(joinSolution, resultSolnOpt)

    objects.updateSolution(result.objVar, resultGraph)
    resultStatesOpt.foreach(states.updateSolution(result.stateVar, _))
  }

  def solveMeet(result : ObjectTE, left : ObjectTE, right : ObjectTE) : SolvedObjectTE = {
    // intersection of graphs, irrespective of whether they
    // are the same object or not?
    throw new IllegalArgumentException()
  }
}