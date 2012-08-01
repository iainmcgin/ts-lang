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

  type TypeVar = Int
  type ContextVar = Int
  type ObjectVar = Int
  type StateVar = Int

  case class TypeVarSupport(typeVar : TypeVar) {
    def =^=(equivTo : Type) = TypeVarConstraint(typeVar, equivTo)
    def =^=(otherVar : TypeVar) = TypeVarConstraint(typeVar, Hole(otherVar))
  }
  implicit def toTypeVarSupport(typeVar : TypeVar) = TypeVarSupport(typeVar)

  def asSubscript(num : Int) : String = 
    num.toString.map(c => (c - '0' + 0x2080).toChar)

  /** A typing context, which consists of variable names mapped to types */
  type Context = Map[String,Type]

  /** an empty context, which maps all variable names to ErrorType */
  val emptyContext : Context = Map.empty.withDefaultValue(ErrorType())

  val unitTy = UnitType()
  def funTy(ret : Type, params : EffectType*) = FunType(params, ret)

  
}