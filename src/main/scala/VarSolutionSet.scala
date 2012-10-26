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

class VarSolutionSet[T] {

  type SolutionProxy = Proxy[(TypeVar,Option[T])]

  private var solutions = Map.empty[TypeVar, SolutionProxy]

  private def getProxy(v : TypeVar) : SolutionProxy = {
    if(!solutions.contains(v))
      solutions += (v -> Proxy.toValue((v, None)))

    solutions(v)
  }

  def getCanonicalEquiv(v : TypeVar) =
    getProxy(v).get()._1

  def getSolution(v : TypeVar) : Option[T] =
    getProxy(v).get()._2

  def getSolutionOrFail(v : TypeVar) : T = getSolution(v).get

  def areEquivalent(v1 : TypeVar, v2 : TypeVar) =
    getProxy(v1).get()._1 == getProxy(v2).get()._2

  def makeEquivalent
      (v1 : TypeVar, v2 : TypeVar) {
    
    val (canonical, linked) = if(v1 < v2) (v1, v2) else (v2, v1)
    getProxy(linked).linkTo(getProxy(canonical))
  }

  def makeEquivalent(v1 : TypeVar, v2 : TypeVar, solution : T) {
    val canonicalVar = if(v1 < v2) v1 else v2
    val newProxy = Proxy.toValue((canonicalVar, Option(solution)))
    getProxy(v1).linkTo(newProxy)
    getProxy(v2).linkTo(newProxy)
  }

  def updateSolution(v : TypeVar, solution : T) {
    val proxy = 
      solutions.get(v).map(proxy => {
        val canonicalVar = proxy.get()._1
        proxy.linkTo(Proxy.toValue(canonicalVar, Option(solution)))
        proxy
      }).getOrElse(Proxy.toValue((v, Option(solution))))

    solutions += (v -> proxy)
  }

}