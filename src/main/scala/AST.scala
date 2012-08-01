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

package uk.ac.gla.dcs.ts0

import org.kiama.attribution.Attributable
import org.kiama.util.Positioned

trait SourceElement extends Attributable with Positioned

/* terms */

abstract class Term extends SourceElement
abstract class Value extends Term

case class UnitValue() extends Value
case class ObjValue(states : Seq[StateDef], state : String) extends Value
case class FunValue(params : Seq[ParamDef], body : Term) extends Value

case class LetBind(varName : String, value : Term, body : Term) extends Term
case class Update(varName : String, body : Term) extends Term
case class MethCall(objVarName : String, methName : String) extends Term
case class Sequence(left : Term, right : Term) extends Term
case class FunCall(funName : String, paramNames : Seq[String]) extends Term

/* term fragments */

case class StateDef(name : String, methods : Seq[MethodDef])
  extends SourceElement
case class MethodDef(name : String, ret : Value, nextState : String)
  extends SourceElement
case class ParamDef(name : String, typeInfo : Option[EffectType]) 
  extends SourceElement

/* special error values */

case class ErrorValue() extends Value

/* types */

abstract class Type extends Attributable {
  def >>(outType : Type) = EffectType(this, outType)
}

case class UnitType() extends Type {
  override def toString = "Unit"
}

case class FunType(params : Seq[EffectType], ret : Type) extends Type {
  override def toString = "(" + params.mkString(",") + ") → " + ret
}

case class ErrorType() extends Type

case class ObjType(states : Seq[StateSpec], state : String) extends Type {
  val stateMap : Map[String,StateSpec] =
    (states.foldLeft
      (Map.empty[String,StateSpec])
      ((map,state) => map + Pair(state.name, state)))

  val currentState = stateMap get state
    
  def retType(method : String) = 
    currentState flatMap (s => s.retType(method)) getOrElse ErrorType()

  override def toString = "{ " + states.mkString(" ") + "}@" + state
}

/** represents a type variable, used in type inference. */
case class Hole(typeVarNum : Int) extends Type {
  override def toString = "α" + asSubscript(typeVarNum)
}

/** represents an object type of unknown structure, used in type inference */
case class ObjectHole(objVar : Int, stateVar : Int) extends Type {
  override def toString = 
    "ω" + asSubscript(objVar) + "@" + "σ" + asSubscript(stateVar)
}

/* type fragments */

case class StateSpec(name : String, methods : Seq[MethodSpec]) {
  val methodMap : Map[String,MethodSpec] =
    methods.foldLeft(
      Map.empty[String,MethodSpec])(
      (map,meth) => map + Pair(meth.name, meth))

  def hasMethod(method : String) = methodMap contains method
  def nextState(method : String) = 
    (methodMap get method) map ((ms : MethodSpec) => ms.nextState)
  def retType(method : String) = (methodMap get method) map (_.ret)
}

case class MethodSpec(name : String, ret : Type, nextState : String)

case class EffectType(before : Type, after : Type) {
  override def toString = before + " ≫ " + after
}