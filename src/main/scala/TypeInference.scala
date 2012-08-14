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

import org.kiama._
import org.kiama.attribution.Attribution._

import scala.collection.mutable.Queue

object MapUtil {
  def sortedStr(changes : Map[String,TypeExpr], pairSep : String) =
    (changes.toList
      .sortBy(_._1)
      .map(p => p._1 + pairSep + p._2)
      .mkString(",")
    )
}

/* Type expressions */

abstract class TypeExpr {
  def >>(te : TypeExpr) = EffectTE(this, te)
}

case object UnitTE extends TypeExpr {
  override def toString = "Unit"
}

case class FunTE(params : Seq[EffectTE], ret : TypeExpr) extends TypeExpr {
  override def toString = "(" + params.mkString(",") + ") → " + ret
}

case class ObjectTE(objVar : TypeVar, stateVar : TypeVar) extends TypeExpr {
  override def toString = objVar + "@" + stateVar
}

case class VarTE(typeVar : TypeVar) extends TypeExpr {
  override def toString = typeVar.toString

  def =^=(equivTo : TypeExpr) = TypeExprConstraint(this, equivTo)
}

case class EffectTE(in : TypeExpr, out : TypeExpr) {
  override def toString = in + " ≫ "
}

/* constraints */

abstract class Constraint

/** 
 * Represents evidence that the specified type variable must be equal
 * to the specified type (which may itself be a type variable or contain
 * type variables in its structure).
 */
case class TypeExprConstraint(a : TypeExpr, b : TypeExpr) extends Constraint {
  override def toString = a + " = " + b
}

/** 
 * Represents evidence that the specified context variable must be
 * composed of some other context and some explicit modifications,
 * as specified by a ContextDefinition.
 */
case class ContextConstraint(
  context : ContextVar, 
  definedAs : ContextDefinition) extends Constraint {
  override def toString = context + " = " + definedAs
}

/**
 * Represents evidence that the specified variable must have the
 * specified type in the specified context.
 */
case class ContextVarConstraint(
  context : ContextVar,
  varName : String,
  typeExpr : TypeExpr) extends Constraint {

  override def toString = varName + " : " + typeExpr + " ∈ " + context
}

/**
 * Represents evidence that an object in the specified type and state
 * must support a call to the named method with the specified return
 * type and state transition.
 */
case class MethodConstraint(
  objVar : TypeVar,
  stateVar : TypeVar,
  method : String,
  retType : TypeExpr,
  nextState : TypeVar) extends Constraint {

  override def toString = method + " : " + retType + " ⇒ " + nextState + 
    " ∈ " + objVar + "@" + stateVar
}

abstract class ContextDefinition

trait ContextWithDependency extends ContextDefinition {
  val base : ContextVar
}

/**
 * Specifies a new context based on some other known context, with
 * variables that existed in that context mapped to
 * potentially new types.
 */
case class ModifiedContext(
  base : ContextVar, 
  changedVars : Map[String,TypeExpr])
  extends ContextWithDependency {

  override def toString = {
    base + " [ " + MapUtil.sortedStr(changedVars, " → ") + " ] "
  }
}

/**
 * Specifies a new context based on some other known context, with
 * a new variable mapping added.
 */
case class ContextAddition(
  base : ContextVar, 
  newVars : Map[String,TypeExpr]) 
extends ContextWithDependency {

  override def toString = base + ", " + MapUtil.sortedStr(newVars, " : ")
}

/**
 * Specifies a new context based on some other known context, with
 * a variable mapping removed.
 */
case class ContextRemoval(base : ContextVar, removedVar : String)
  extends ContextWithDependency {

  override def toString = base + " - { " + removedVar + " }"
}

/**
 * Specifies a context explicitly, with all known variable mappings
 * for that context. Used as the input context for a function body.
 */
case class BaseContext(vars : Map[String,TypeExpr]) extends ContextDefinition {
  override def toString = "<FIXED>" + MapUtil.sortedStr(vars, " : ")
}

/**
 * The input context for a top-level term. Can be arbitrarily extended
 * by discovered free variables.
 */
case class FreeContext(vars : Map[String,TypeExpr]) extends ContextDefinition {
  override def toString = "<FREE> " + MapUtil.sortedStr(vars, " : ")
}

case class ConstraintSet(
    ccs : Seq[ContextConstraint],
    cvcs : Seq[ContextVarConstraint],
    tecs : Seq[TypeExprConstraint],
    mcs : Seq[MethodConstraint]) {

  def +(cc : ContextConstraint) = ConstraintSet(cc +: ccs, cvcs, tecs, mcs)
  def +(cvc : ContextVarConstraint) = ConstraintSet(ccs, cvc +: cvcs, tecs, mcs)
  def +(tec : TypeExprConstraint) = ConstraintSet(ccs, cvcs, tec +: tecs, mcs)
  def +(mc : MethodConstraint) = ConstraintSet(ccs, cvcs, tecs, mc +: mcs)

  def ++(others : ConstraintSet) =
    ConstraintSet(
      ccs ++ others.ccs, 
      cvcs ++ others.cvcs,
      tecs ++ others.tecs,
      mcs ++ others.mcs)
}


object ConstraintGenerator {

  val empty = ConstraintSet(Seq.empty, Seq.empty, Seq.empty, Seq.empty)
  
  def sameAs(base : ContextVar) = ModifiedContext(base, Map.empty)
  def removeFrom(base : ContextVar, removedVar : String) =
    ContextRemoval(base, removedVar)
  def addTo(base : ContextVar, varName : String, varType : TypeExpr) = 
    ContextAddition(base, Map(varName -> varType))

  val typeVars = new TypeVarGenerator()
  val contextVars = new ContextVarGenerator()

  val typeVar : Term => TypeVar =
    attr {
      case _ : Term => typeVars.next()
    }

  val inContextVar : Term => ContextVar =
    attr {
      case _ : Term => contextVars.next()
    }

  val outContextVar : Term => ContextVar =
    attr {
      case _ : Term => contextVars.next()
    }

  val objVar : ObjValue => TypeVar =
    attr {
      case _ : ObjValue => typeVars.next()
    }

  val objInitStateVar : ObjValue => TypeVar =
    attr {
      case o : ObjValue => (o.stateMap(o.state))->stateVar
    }

  val stateVar : StateDef => TypeVar =
    attr {
      case _ : StateDef => typeVars.next()
    }

  def allConstraints(t : Term) : ConstraintSet =
    (empty +
    ContextConstraint(t->inContextVar, FreeContext(Map.empty)) ++
    (t->constraints) ++ 
    (t match {
      case UnitValue() => empty
      case o @ ObjValue(states,_) => methodConstraints(o)
      case FunValue(_,body) => allConstraints(body)
      case LetBind(_,value,body) => 
        allConstraints(value) ++ allConstraints(body)
      case Update(_, body) => allConstraints(body)
      case MethCall(_,_) => empty
      case Sequence(left, right) => 
        allConstraints(left) ++ allConstraints(right)
      case FunCall(_,_) => empty
    }))

  def methodConstraints(o : ObjValue) =
    (o.states.foldLeft
      (empty)
      ((cs, state) => {
        val sv = state->stateVar
        (state.methods.foldLeft
          (cs)
          ((cs, m) => (cs ++
              ((m.ret)->constraints) +
              MethodConstraint(
                o->objVar, 
                sv, 
                m.name, 
                VarTE((m.ret)->typeVar), 
                (o.stateMap(m.nextState))->stateVar) +
              ContextConstraint(
                (m.ret)->inContextVar, 
                sameAs(o->inContextVar)) +
              ContextConstraint(
                (m.ret)->outContextVar, 
                sameAs((m.ret)->inContextVar))
            )
          )
        )
      })
    )

  val constraints : Term => ConstraintSet =
    attr {
      case t : UnitValue => unitValueConstraints(t)
      case t : ObjValue  => objectValueConstraints(t)
      case t : FunValue  => funValueConstraints(t)
      case t : LetBind   => letBindConstraints(t)
      case t : Update    => updateConstraints(t)
      case t : Sequence  => sequenceConstraints(t)
      case t : FunCall   => funCallConstraint(t)
      case t : MethCall  => methCallConstraint(t)
    }

  def unitValueConstraints(t : UnitValue) =
    (empty +
      TypeExprConstraint(VarTE(t->typeVar), UnitTE) +
      ContextConstraint(t->outContextVar, sameAs(t->inContextVar)))
    

  def objectValueConstraints(t : ObjValue) = {
    (empty +
      ContextConstraint(t->outContextVar, sameAs(t->inContextVar)) +
      TypeExprConstraint(
        VarTE(t->typeVar), 
        ObjectTE(t->objVar, t->objInitStateVar))
    )
  }

  def funValueConstraints(t : FunValue) = {
    val inTypeVars = t.params.map(paramToTypeExpr)
    val outTypeVars = t.params.map(paramToTypeExpr)
    val effects : Seq[EffectTE] = buildEffects(inTypeVars, outTypeVars)
    val funType = FunTE(effects, VarTE(t.body->typeVar))

    val outTypeConstraints =
      (outTypeVars.foldLeft
        (empty)
        ((c,p) => 
          c + ContextVarConstraint(t.body->outContextVar, p._1, p._2)))

    outTypeConstraints ++ (empty +
      ContextConstraint(t->outContextVar, sameAs(t->inContextVar)) +
      ContextConstraint(t.body->inContextVar, 
        BaseContext(Map(inTypeVars: _*))) +
      TypeExprConstraint(VarTE(t->typeVar), funType))
  }

  def letBindConstraints(t : LetBind) =
    (empty +
      ContextConstraint(t.value->inContextVar, sameAs(t->inContextVar)) +
      ContextConstraint(t.body->inContextVar, 
        addTo(t.value->outContextVar, t.varName, VarTE(t.value->typeVar))) +
      ContextConstraint(t->outContextVar, 
        ContextRemoval(t.body->outContextVar, t.varName)) +
      TypeExprConstraint(VarTE(t->typeVar), VarTE(t.body->typeVar))
    )

  def updateConstraints(t : Update) = {
    val bodyType = VarTE(t.body->typeVar)
    (empty +
      ContextConstraint(t.body->inContextVar, 
        removeFrom(t->inContextVar, t.varName)) +
      ContextConstraint(t->outContextVar, 
        addTo(t.body->outContextVar, t.varName, bodyType)) +
      TypeExprConstraint(VarTE(t->typeVar), UnitTE)
    )
  }

  def sequenceConstraints(t : Sequence) =
    (empty +
      ContextConstraint(t.left->inContextVar, sameAs(t->inContextVar)) +
      ContextConstraint(t.right->inContextVar, sameAs(t.left->outContextVar)) +
      TypeExprConstraint(VarTE(t->typeVar), VarTE(t.right->typeVar))
    )

  def funCallConstraint(t : FunCall) = {
    val paramTypeVars = 
      t.paramNames.map(p => Tuple3(p, typeVars.next(), typeVars.next()))
    val funEffects = paramTypeVars.map(t => EffectTE(VarTE(t._2), VarTE(t._3)))
    val funRetTypeVar = typeVars.next()
    val funType = FunTE(funEffects, VarTE(funRetTypeVar))

    val paramConstraints = 
      (paramTypeVars.foldLeft
        (empty)
        ((c, p) => c + ContextVarConstraint(t->inContextVar, p._1, VarTE(p._2)))
      )

    val contextChangedVars =
      (paramTypeVars.foldLeft
        (Map.empty[String,TypeExpr])
        ((m,p) => m + (p._1 -> VarTE(p._3))))

    (paramConstraints ++
      (empty +
        ContextVarConstraint(t->inContextVar, t.funName, funType) +
        ContextConstraint(t->outContextVar, 
          ModifiedContext(t->inContextVar, contextChangedVars)) +
        TypeExprConstraint(VarTE(t->typeVar), VarTE(funRetTypeVar)))
    )
  }

  def methCallConstraint(t : MethCall) = {
    val objectVar = typeVars.next()
    val inStateVar = typeVars.next()
    val outStateVar = typeVars.next()
    val inObjectType = ObjectTE(objectVar, inStateVar)
    val outObjectType = ObjectTE(objectVar, outStateVar)
    val methType = VarTE(t->typeVar)
    (empty +
      ContextVarConstraint(t->inContextVar, t.objVarName, inObjectType) +
      MethodConstraint(objectVar, inStateVar, t.methName, 
        methType, outStateVar) +
      ContextConstraint(t->outContextVar, 
        ModifiedContext(t->inContextVar, Map(t.objVarName -> outObjectType)))
    )
  }

  def buildEffects(in : Seq[(String,TypeExpr)], out : Seq[(String,TypeExpr)]) =
    in.zip(out).map(x => EffectTE(x._1._2, x._2._2))

  val paramToTypeExpr = (pdef : ParamDef) => Pair(pdef.name, VarTE(typeVars.next()))

}

case class BadRootContextDef(contextDef : ContextDefinition) extends Exception
case class UnresolvedDependency(contextDef : ContextDefinition) extends Exception
case class MissingVariable(base : ContextVar, varName : String) extends Exception
case class DuplicateDefinition(base : ContextVar, varName : String) extends Exception
case class CannotUnifyTypes(t1 : Type, t2 : Type) extends Exception

object ConstraintSolver {

  import ConstraintGenerator.typeVar
  import ConstraintGenerator.inContextVar
  import ConstraintGenerator.outContextVar

  type InferredContext = Map[String, TypeExpr]

  def solve(constraints : ConstraintSet, t : Term) : Tuple3[Context, Type, Context] = {
    val contexts = expandContexts(constraints.ccs)
    val extraTypeConstraints = matchTypes(contexts, constraints.cvcs)
    val allTypeConstraints = constraints.tecs ++ extraTypeConstraints
    val varsToTypeExprs = unifyTypes(allTypeConstraints)

    val contextConverter = (cv : ContextVar) => (
      contexts(cv).mapValues(makeTypeExplicit(_, varsToTypeExprs))
    )
    val inCtx = contextConverter(t->inContextVar)
    val outCtx = contextConverter(t->outContextVar)
    val termTy = makeTypeExplicit(varsToTypeExprs(t->typeVar), varsToTypeExprs)

    new Tuple3(inCtx, termTy, outCtx)
  }

  def expandContexts(constraints : Seq[ContextConstraint]) 
    : Map[ContextVar,Map[String,TypeExpr]] = {

    val constraintsById = 
      (constraints.foldLeft
        (Map.empty[ContextVar, ContextDefinition])
        ((m, c) => m + Pair(c.context, c.definedAs)))

    val dependents : Map[ContextVar, Set[ContextVar]] =
      (constraints.foldLeft
        (Map.empty[ContextVar, Set[ContextVar]])
        ((m, c) => c.definedAs match {
          case cwd : ContextWithDependency => 
            m.updated(cwd.base, m.getOrElse(cwd.base, Set.empty) + c.context)
          case bc : BaseContext => m
        })
      )

    // we are guaranteed from the way context constraints are constructed
    // that the dependency graph is a forest. Solve all constraints from
    // the roots to leaves

    val allDependents = 
      (dependents.values.foldLeft
        (Set.empty[ContextVar])
        ((s, cvs) => s ++ cvs)
      )

    var roots : Set[ContextVar] = constraintsById.keySet -- allDependents

    var contexts : Map[ContextVar, InferredContext] = 
      (roots.foldLeft
        (Map.empty[ContextVar, InferredContext])
        ((m, r) => 
          constraintsById(r) match {
            case bc : BaseContext => 
              m + Pair(r, solveContextConstraint(bc, Map.empty))
            case _ => 
              throw new BadRootContextDef(constraintsById(r))
          })
      )

    var available : Set[ContextVar] = roots.flatMap(r => dependents.getOrElse(r, Set.empty))
    while(!available.isEmpty) {
      val next = available.head
      contexts += 
        Pair(next, solveContextConstraint(constraintsById(next), contexts))
      available = dependents.getOrElse(next, Set.empty) ++ available.tail
    }

    contexts
  }

  def solveContextConstraint(
    cd : ContextDefinition, 
    contexts : Map[ContextVar, InferredContext]) : InferredContext = {

    cd match {
      case bc : BaseContext => bc.vars
      case fc : FreeContext => fc.vars
      case cwd : ContextWithDependency => {
        if(!contexts.contains(cwd.base)) throw new UnresolvedDependency(cwd)
        updateContext(cwd, cwd.base, contexts(cwd.base))
      }
    }
  }

  def updateContext(
    spec : ContextWithDependency, 
    baseVar : ContextVar,
    base : InferredContext) : InferredContext = {
    spec match {
      case ModifiedContext(_, changedVars) => {
        var context = base
        changedVars.keySet.foreach(v => {
          if(!context.contains(v)) throw new MissingVariable(baseVar, v)
          context = context.updated(v, changedVars(v))
        })

        context
      }
        
      case ContextAddition(_, additions) =>
        (additions.foldLeft
          (base)
          ((ctx, p) => {
            if(base.contains(p._1)) 
              throw new DuplicateDefinition(baseVar, p._1)
            ctx + p
          })
        )

      case ContextRemoval(_, removedVar) => {
        if(!base.contains(removedVar)) 
          throw MissingVariable(baseVar, removedVar)

        base - removedVar
      }
    }
  }

  /**
   * Generates additional TypeVarConstraints by comparing the list of
   * generated ContextVarConstraints to the known contents of all contexts.
   */
  def matchTypes(
    contexts : Map[ContextVar, InferredContext], 
    varConstraints : Seq[ContextVarConstraint]) : Seq[TypeExprConstraint] = {

    varConstraints.flatMap(v => {
      contexts(v.context).get(v.varName) match {
        // for terms where we allow free variables, the context var
        // constraint gives us information on something that should be
        // in the context. Where free variables are not allowed, it
        // indicates a type error as some piece of code is trying to use
        // an unbound variable.
        // TODO: handle this
        case None => Seq.empty
        case Some(typeExpr) => Seq(TypeExprConstraint(v.typeExpr, typeExpr))
      }
    })
  }

  // def compareTypeStructure(
  //   t1 : TypeExpr, 
  //   t2 : TypeExpr) 
  // : Seq[TypeExprConstraint] = {

  //   (t1,t2) match {
  //     case (VarTE(tv), t) => Seq(TypeExprConstraint(tv, t))
  //     case (t, VarTE(tv)) => Seq(TypeExprConstraint(tv, t))
  //     case (UnitTE, UnitTE) => Seq.empty
  //     case (f1 : FunTE, f2 : FunTE) => {
  //       if(f1.params.size != f2.params.size) throw new CannotUnifyTypes(f1, f2)
  //       val paramConstraints = f1.params.zip(f2.params).flatMap(effPair =>
  //         compareTypeStructure(effPair._1.before, effPair._2.before) ++
  //           compareTypeStructure(effPair._1.after, effPair._2.after)
  //       )
  //       val retConstraints = compareTypeStructure(f1.ret, f2.ret)
  //       paramConstraints ++ retConstraints
  //     }
  //     case (o1 : ObjTE, o2 : ObjTE) => {
  //       // TODO
  //       Seq.empty
  //     }
  //     case _ => throw CannotUnifyTypes(t1, t2)
  //   }
  // }

  // def filterTrivialConstraints(constraints : Seq[TypeExprConstraint]) =
  //   constraints.filter(c => (c.a, c.b) match {
  //     case (VarTE(tv1), VarTE(tv2)) if tv1 == tv2 => false
  //     case _ => true
  //   })

  def unifyTypes(constraints : Seq[TypeExprConstraint]) : Map[TypeVar, TypeExpr] = {
    val sys = UnificationProblemBuilder.build(constraints :_*)
    val solvedEqs : List[MultiEquation] = Unifier.unify(sys)
    SolutionExtractor.extract(solvedEqs)
  }

  def makeTypeExplicit(te : TypeExpr, typeVarMap : Map[TypeVar,TypeExpr]) : Type = {
    te match {
      case VarTE(tv) => makeTypeExplicit(typeVarMap(tv), typeVarMap)
      case UnitTE => UnitType()
      case FunTE(effects, ret) => {
        val explicitEffects = effects.map(e => 
          EffectType(
            makeTypeExplicit(e.in, typeVarMap), 
            makeTypeExplicit(e.out, typeVarMap)))
        FunType(explicitEffects, makeTypeExplicit(ret, typeVarMap))
      }
      case ObjectTE(objVar,stateVar) => {
        // TODO
        UnitType()
      }
    }
  }
}