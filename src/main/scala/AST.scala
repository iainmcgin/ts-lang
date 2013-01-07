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

/* special error values */

case class ErrorValue() extends Value

/* validation errors */
sealed abstract class ObjValidationError {
  val refPoint : Option[SourceElement]
}
case class DuplicateState(state : String)(val refPoint : Option[SourceElement] = None) extends ObjValidationError
case class MissingState(state : String)(val refPoint : Option[SourceElement] = None) extends ObjValidationError
case class DuplicateMethod(state : String, method : String)(val refPoint : Option[SourceElement] = None) extends ObjValidationError


/* types */

sealed abstract class Type extends SourceElement {
  def >>(outType : Type) = EffectType(this, outType)
  def join(other : Type) : Type = (this, other) match {
    case (UnitType(), UnitType()) => UnitType()
    case (BoolType(), BoolType()) => BoolType()
    case (FunType(f1p, f1r), FunType(f2p, f2r)) => {
      if(f1p.size != f2p.size) TopType()
      else {
        val retType = f1r join f2r
        val paramTypesOpt = 
          (f1p.zip(f2p).foldRight
            (Option(Seq.empty[EffectType]))
            ((paramPair, resOpt) => resOpt.flatMap(res => {
              val (eff1, eff2) = paramPair
              (eff1 join eff2) map (_ +: res)
            }))
          )

        val typeOpt = 
          paramTypesOpt.map(p => FunType(p, retType))

        typeOpt.getOrElse(TopType())
      }
    }
    case (a @ ObjType(_, _), b @ ObjType(_, _)) =>
      a.joinObj(b)
    case (ErrorType(),_) => ErrorType()
    case (_, ErrorType()) => ErrorType()
    case _ => TopType()
  }

  def meet(other : Type) : Option[Type] = (this, other) match {
    case (UnitType(), UnitType()) => Some(UnitType())
    case (BoolType(), BoolType()) => Some(BoolType())
    case (FunType(f1p, f1r), FunType(f2p, f2r)) => {
      if(f1p.size != f2p.size) None
      else {
        val retTypeOpt = f1r meet f2r
        val paramTypesOpt = (f1p.zip(f2p).foldRight
          (Option(Seq.empty[EffectType]))
          ((paramPair, resOpt) => resOpt.flatMap(res => {
            val (eff1, eff2) = paramPair
            (eff1 meet eff2) map (_ +: res)
          }))
        )

        paramTypesOpt.flatMap(p => retTypeOpt.map(r => FunType(p, r)))
      }
    }

    case (a @ ObjType(_,_), b @ ObjType(_,_)) => {
      a.meetObj(b)
    }

    case (ErrorType(),_) => Some(ErrorType())
    case (_,ErrorType()) => Some(ErrorType())
    case _ => None
  }
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
  override def toString = "(" + params.mkString(",") + ") → " + ret
}

case class ErrorType() extends Type

case class ObjType(states : Seq[StateSpec], state : String) extends Type {
  lazy val stateMap : Map[String,StateSpec] =
    (states.foldLeft
      (Map.empty[String,StateSpec])
      ((map,state) => map + Pair(state.name, state)))

  lazy val currentState = stateMap get state
    
  def retType(method : String) = 
    currentState flatMap (s => s.retType(method)) getOrElse ErrorType()

  def joinObj(other : ObjType) : ObjType = {
    // TODO: implement properly
    if(this == other) this
    else ObjType(Seq(StateSpec("S", Seq.empty)), "S")
  }

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

  def meetObj(other : ObjType) : Option[ObjType] = {
    // TODO
    None
  }

  override def toString = states.mkString("{ ", " ", " }@") + state
}

/* type fragments */

case class StateSpec(name : String, methods : Seq[MethodSpec]) extends SourceElement {
  val methodMap : Map[String,MethodSpec] =
    methods.foldLeft(
      Map.empty[String,MethodSpec])(
      (map,meth) => map + Pair(meth.name, meth))

  def hasMethod(method : String) = methodMap contains method
  def nextState(method : String) = 
    (methodMap get method) map ((ms : MethodSpec) => ms.nextState)
  def retType(method : String) = (methodMap get method) map (_.ret)

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