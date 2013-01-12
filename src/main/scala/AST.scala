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

import org.kiama.attribution.Attributable
import org.kiama.util.Positioned

/** standard trait for anything that appears in source code */
trait SourceElement extends Attributable with Positioned

/* terms */

sealed abstract class Term extends SourceElement
sealed abstract class Value extends Term

case class UnitValue() extends Value { override def toString = "unit" }
case class TrueValue() extends Value { override def toString = "true" }
case class FalseValue() extends Value { override def toString = "false" }
case class ObjValue(states : Seq[StateDef], state : String) extends Value {
  val stateMap =
    (states.foldLeft
      (Map.empty[String,StateDef])
      ((m, s) => m + (s.name -> s))
    )

  def validate() : Seq[ObjValidationError] = {
    var errors = Seq.empty[ObjValidationError]
    def checkExists(s : String, from : SourceElement) = {
      if(!stateMap.contains(s)) errors +:= MissingState(s)(Some(from))
    }

    states.groupBy(_.name).foreach { case (state,dups) =>
      if(dups.size > 1) errors +:= DuplicateState(state)(Some(dups.head))
    }

    checkExists(state, this)
    states.foreach(state => {
      
      state.methods.groupBy(_.name).foreach { case (method, dups) =>
        if(dups.size > 1) 
          errors +:= DuplicateMethod(state.name, method)(Some(dups.head))
      }

      state.methods.foreach(method => checkExists(method.nextState, method))
    })
    errors
  }

  override def toString = states.mkString("{", " ", "}") + "@" + state
}

case class FunValue(params : Seq[ParamDef], body : Term) extends Value {
  override def toString = params.mkString("\\(", ", ", ").") + "(" + body + ")"
}

case class LetBind(varName : String, value : Term, body : Term) extends Term {
  override def toString = 
    "let " + varName + " = (" + value + ") in (" + body + ")"
}

case class MethCall(objVarName : String, methName : String) extends Term {
  override def toString = objVarName + "." + methName
}

case class Sequence(left : Term, right : Term) extends Term {
  override def toString = left + " ; " + right
}

case class FunCall(funName : String, paramNames : Seq[String]) extends Term {
  override def toString = funName + paramNames.mkString("(", ", ", ")")
}

case class If(condition : Term, whenTrue : Term, whenFalse : Term) extends Term {
  override def toString = 
    "if (" + condition + ") then (" + whenTrue + ") else (" + whenFalse + ")"
}

/* term fragments */

case class StateDef(name : String, methods : Seq[MethodDef])
    extends SourceElement {
  override def toString = name + methods.mkString(" {", ", ", "}")
}

case class MethodDef(name : String, ret : Value, nextState : String)
    extends SourceElement {
  override def toString = name + " = (" + ret + ", " + nextState + ")"
}

case class ParamDef(name : String, typeInfo : Option[EffectType]) 
  extends SourceElement {

  override def toString = name + typeInfo.map(" : " + _).getOrElse("")  
}

/* object validation errors */
sealed abstract class ObjValidationError {
  val refPoint : Option[SourceElement]
}

case class DuplicateState(state : String)
                         (val refPoint : Option[SourceElement] = None) 
                         extends ObjValidationError

case class MissingState(state : String)
                       (val refPoint : Option[SourceElement] = None) 
                       extends ObjValidationError

case class DuplicateMethod(state : String, method : String)
                          (val refPoint : Option[SourceElement] = None) 
                          extends ObjValidationError


/* types */

sealed abstract class Type extends SourceElement {
  def >>(outType : Type) = EffectType(this, outType)

  /**
   * Calculates the join of two types. This is always defined, as the type
   * Top (⊤) is a supertype of everything.
   */
  def join(other : Type) : Type = (this, other) match {
    case (TopType(), _) => TopType()
    case (_, TopType()) => TopType()
    case (UnitType(), UnitType()) => UnitType()
    case (BoolType(), BoolType()) => BoolType()
    case (a @ FunType(_, _), b @ FunType(_, _)) => a.joinFun(b)
    case (a @ ObjType(_, _), b @ ObjType(_, _)) => a.joinObj(b)
    case _ => TopType()
  }

  /**
   * Calculates the meet of two types, if this is defined.
   */
  def meet(other : Type) : Option[Type] = (this, other) match {
    case (TopType(), x) => Some(x)
    case (x, TopType()) => Some(x)
    case (UnitType(), UnitType()) => Some(UnitType())
    case (BoolType(), BoolType()) => Some(BoolType())
    case (a @ FunType(_,_), b @ FunType(_,_)) => a.meetFun(b)
    case (a @ ObjType(_,_), b @ ObjType(_,_)) => a.meetObj(b)
    case _ => None
  }
}

object Type {
  def joinOpt(aOpt : Option[Type], bOpt : Option[Type]) : Option[Type] =
    aOpt.flatMap(a => bOpt.map(a join _))

  def joinSeq(types : Seq[Type]) : Type =
    types.reduce(_ join _)

  def joinSeqOpt(typeOpts : Seq[Option[Type]]) : Option[Type] =
    typeOpts.reduce(joinOpt(_, _))

  def meetOpt(aOpt : Option[Type], bOpt : Option[Type]) : Option[Type] =
    aOpt.flatMap(t1 => bOpt.flatMap(_ meet t1))

  def meetSeq(types : Seq[Type]) : Option[Type] =
    reduceSeq(types)(_ meet _)

  def meetSeqOpt(typeOpts : Seq[Option[Type]]) : Option[Type] =
    reduceSeqOpt[Type,Type](typeOpts)((_ : Type) meet (_ : Type))
}

case class TopType() extends Type {
  override def toString = "⊤"
}

case class UnitType() extends Type {
  override def toString = "Unit"
}

case class BoolType() extends Type {
  override def toString = "Bool"
}

case class FunType(params : Seq[EffectType], ret : Type) extends Type {

  def joinFun(other : FunType) : Type = {
    if(this.params.size != other.params.size) return TopType()
    
    val retType = this.ret join other.ret
    val paramTypesOpt = 
      (this.params.zip(other.params).foldRight
        (Option(Seq.empty[EffectType]))
        ((paramPair, resOpt) => resOpt.flatMap(res => {
          val (eff1, eff2) = paramPair
          (eff1 join eff2) map (_ +: res)
        }))
      )

    paramTypesOpt.map(FunType(_, retType)).getOrElse(TopType())
  }

  def meetFun(other : FunType) : Option[Type] = {
    if(this.params.size != other.params.size) return None

    val retTypeOpt = this.ret meet other.ret
    val paramTypesOpt = (this.params.zip(other.params).foldRight
      (Option(Seq.empty[EffectType]))
      ((paramPair, resOpt) => resOpt.flatMap(res => {
        val (eff1, eff2) = paramPair
        (eff1 meet eff2) map (_ +: res)
      }))
    )

    paramTypesOpt.flatMap(p => retTypeOpt.map(r => FunType(p, r)))
  }

  override def toString = "(" + params.mkString(",") + ") → " + ret
}


/**
 * Object types, which are composed of a finite set of states with
 * deterministic transitions, and a current state set. A real object value
 * of this type will have precisely one current state; the state set is used
 * to capture runtime non-determinism in the type system.
 */
case class ObjType(states : Seq[StateSpec], currentStateSet : Set[String]) extends Type {

  lazy val stateMap : Map[String,StateSpec] =
    (states.foldLeft
      (Map.empty[String,StateSpec])
      ((map,state) => map + Pair(state.name, state)))
  
  /**
   * Checks that the object type is free of the following errors:
   * - duplicate state specifications
   * - duplicate methods within state specifications
   * - references to missing state specifications
   */
  def validate() : Seq[ObjValidationError] = {
    var errors = Seq.empty[ObjValidationError]
    def checkExists(s : String, from : SourceElement) = {
      if(!stateMap.contains(s)) errors +:= MissingState(s)(Some(from))
    }

    states.groupBy(_.name).foreach { case (state,dups) =>
      if(dups.size > 1) errors +:= DuplicateState(state)(Some(dups.head))
    }

    currentStateSet.foreach(checkExists(_, this))
    states.foreach(state => {
      
      state.methods.groupBy(_.name).foreach { case (method, dups) =>
        if(dups.size > 1) 
          errors +:= DuplicateMethod(state.name, method)(Some(dups.head))
      }

      state.methods.foreach(method => checkExists(method.nextState, method))
    })
    errors
  }

  /**
   * Determines the effective return type of the specified method if it
   * were to be called with the current state set. If one or more of the
   * current states does not allow the specified method, None is
   * returned.
   */
  def retType(method : String) : Option[Type] = {
    val retTypeOpts = currentStateSet.map { stateName =>
      stateMap.get(stateName).flatMap(_.retType(method))
    }

    Type.joinSeqOpt(retTypeOpts.toSeq)
  }

  /**
   * Determines the successor state set of the specified method were to be
   * called. If one or more of the states in the current state set does not
   * allow the specified method, None is returned.
   */
  def nextStateSet(method : String) : Option[Set[String]] =
    (currentStateSet.foldLeft
      (Option(Set.empty[String]))
      { (res, stateName) =>
        val stateOpt = stateMap.get(stateName)
        val methodNextOpt = stateOpt.flatMap(_.nextState(method))

        methodNextOpt.flatMap(next => res.map(_ + next))
      }
    )

  def joinObj(other : ObjType) : ObjType = {
    // TODO: implement properly
    if(this == other) this
    else ObjType(Seq(StateSpec("S", Seq.empty)), "S")
  }

  def meetObj(other : ObjType) : Option[ObjType] = {
    // TODO: implement properly
    if(this == other) Some(this)
    else None
  }

  override def toString = {
    val body = states.mkString("{ ", " ", " }@")
    if(currentStateSet.size == 1)
      body + currentStateSet.head
    else 
      body + currentStateSet.mkString("{ ", ", ", " }")
  }
}

object ObjType {
  /**
   * alternative "constructor" for ObjType where the object is known to be
   * in a single state.
   */
  def apply(states : Seq[StateSpec], currentState : String) : ObjType =
    ObjType(states, Set(currentState))
}

/* type fragments */

case class StateSpec(name : String, methods : Seq[MethodSpec]) extends SourceElement {
  val methodMap : Map[String,MethodSpec] =
    methods.foldLeft(
      Map.empty[String,MethodSpec])(
      (map,meth) => map + Pair(meth.name, meth))

  def hasMethod(method : String) = methodMap contains method
  
  def nextState(method : String) : Option[String] = 
    (methodMap get method) map ((ms : MethodSpec) => ms.nextState)

  def retType(method : String) : Option[Type] = 
    (methodMap get method) map (_.ret)

  override def toString = name + methods.mkString(" { ", "; ", " }")
}

case class MethodSpec(name : String, ret : Type, nextState : String) extends SourceElement {
  override def toString = name + " : " + ret + " ⇒ " + nextState
}

case class EffectType(before : Type, after : Type) extends SourceElement {
  override def toString = before + " ≫ " + after

  def join(other : EffectType) : Option[EffectType] = {
    val beforeOpt = this.before meet other.before
    val after = this.after join other.after
    beforeOpt.map(EffectType(_, after))
  }

  def meet(other : EffectType) : Option[EffectType] = {
    val before = this.before join other.before
    val afterOpt = this.after meet other.after
    afterOpt.map(EffectType(before, _))
  }
}