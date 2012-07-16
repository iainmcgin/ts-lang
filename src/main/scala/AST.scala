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

/* terms */

abstract class Term extends Attributable
abstract class Value extends Term

case object UnitValue extends Value
case class ObjValue(states : Seq[StateDef], state : String) extends Value
case class FunValue(params : Seq[ParamDef], body : Term) extends Value

case class LetBind(varName : String, valTerm : Term, bodyTerm : Term) extends Term
case class Update(varName : String, body : Term) extends Term
case class MethCall(objVarName : String, methName : String) extends Term
case class Sequence(left : Term, right : Term) extends Term
case class FunCall(funName : String, paramNames : Seq[String]) extends Term

case class StateDef(name : String, methods : Seq[MethodDef])
case class MethodDef(name : String, ret : Value, nextState : String)
case class ParamDef(name : String, typeInfo : Option[EffectType])

/* types */

abstract class Type extends Attributable
case object UnitType extends Type
case class ObjType(states : Seq[StateSpec], state : String) extends Type
case class FunType(params : Seq[EffectType], ret : Type) extends Type

case class StateSpec(name : String, methods : Seq[MethodSpec])
case class MethodSpec(name : String, ret : Type, nextState : String)

case class EffectType(before : Type, after : Type)
