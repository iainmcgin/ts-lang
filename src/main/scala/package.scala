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

package uk.ac.gla.dcs

package object ts {

  case class TypeVar(v : Int) extends Ordered[TypeVar] {
    override def compare(other : TypeVar) = this.v.compare(other.v)
    override def toString = "α" + asSubscript(v)
  }

  case class ContextVar(v : Int) extends Ordered[ContextVar] {
    override def compare(other : ContextVar) = this.v.compare(other.v)
    override def toString = "ɣ" + asSubscript(v)
  }

  type StateNameEquiv = Relation[String,String]

  def asSubscript(num : Int) : String = 
    num.toString.map(c => (c - '0' + 0x2080).toChar)

  /** A typing context, which consists of variable names mapped to types */
  type Context = Map[String,Type]

  sealed abstract class JoinError
  case class DifferentDomains(leftDiff : Set[String], rightDiff : Set[String])
    extends JoinError
  case class MismatchedTypes(varName : String, t1 : Type, t2 : Type)
    extends JoinError

  def joinContexts(c1 : Context, c2 : Context) : Either[Seq[JoinError],Context] = {
    if(c1.keySet != c2.keySet) {
      val c1Extra = c1.keySet -- c2.keySet
      val c2Extra = c2.keySet -- c1.keySet
      return Left(Seq(DifferentDomains(c1Extra, c2Extra)))
    }

    val (errors, ctx) = (c1.foldLeft
      (Pair(Seq.empty[JoinError], emptyContext))
      ((res, p) => {
        val errors = res._1
        val ctx = res._2
        val varName = p._1
        val varType = p._2
        val otherType = c2(varName)

        (varType.join(otherType).
          map(joinedType => Pair(errors, ctx + (varName -> joinedType))).
          getOrElse(Pair(MismatchedTypes(varName, varType, otherType) +: errors, 
            ctx))
        )
      })
    )

    if(errors.isEmpty) Right(ctx) else Left(errors)
  }

  /** A typing context, where variables are mapped to type expressions
   *  rather than concrete types, i.e. type variables may be involved
   */
  type PolyContext = Map[String,TypeExpr]

  def joinPolyContexts(c1 : PolyContext, 
    c2 : PolyContext, 
    tvGen : TypeVarGenerator)
    : Option[Pair[PolyContext, Seq[EqualityConstraint]]] = {
    // TODO
    if(c1.keySet != c2.keySet) {
      return None
    }

    Some(
      c1.foldLeft
        (Pair(c1.empty, Seq.empty[EqualityConstraint]))
        ((res, p) => {
          var tv = VarTE(tvGen.next())
          (res._1 + (p._1 -> tv), 
            EqualityConstraint(tv, JoinTE(p._2, c2(p._1))) +: res._2
          )
        })
    )
  }

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