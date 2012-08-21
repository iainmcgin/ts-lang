/*
 * This file is part of TS0.
 * 
 * TS0 - Copyright (c) 2012, Iain McGinniss
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted under the terms of the 2-clause BSD license:
 * http://opensource.org/licenses/BSD-2-Clause
 */

package uk.ac.gla.dcs

package object ts0 {

  case class TypeVar(v : Int) {
    override def toString = "α" + asSubscript(v)
  }

  case class ContextVar(v : Int) {
    override def toString = "ɣ" + asSubscript(v)
  }

  def asSubscript(num : Int) : String = 
    num.toString.map(c => (c - '0' + 0x2080).toChar)

  /** A typing context, which consists of variable names mapped to types */
  type Context = Map[String,Type]

  /** A typing context, where variables are mapped to type expressions
   *  rather than concrete types, i.e. type variables may be involved
   */
  type PolyContext = Map[String,TypeExpr]

  /** an empty context, which maps all variable names to ErrorType */
  val emptyContext : Context = Map.empty.withDefaultValue(ErrorType())

  val unitTy = UnitType()
  def funTy(ret : Type, params : EffectType*) = FunType(params, ret)

  def funTe(ret : TypeExpr, params : EffectTE*) = FunTE(params, ret)

  /**
   * Simple class for allocation of unique variable identifiers.
   */
  abstract class Counter[X] {
    private var last : Int = 0
    def step() = {
      last += 1
      last
    }
    def reset() = { last = 0 }

    def next() : X
  }

  class TypeVarGenerator extends Counter[TypeVar] {
    def next() = TypeVar(step())
  }

  class ContextVarGenerator extends Counter[ContextVar] {
    def next() = ContextVar(step())
  }
}