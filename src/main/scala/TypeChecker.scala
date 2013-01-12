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

import org.kiama._
import org.kiama.attribution.Attribution._
import scala.collection.immutable.Map.WithDefault
import org.kiama.util.Messaging._
import ObjectValidator._

object TypeChecker {

  def mSpec(mdef : MethodDef) : Option[MethodSpec] = 
    (mdef.ret->ttype).map { retType => 
      MethodSpec(mdef.name, retType, mdef.nextState)
    }

  def sSpec(sdef : StateDef) : Option[StateSpec] = {
    val methodSpecsOpt = 
      mapAllOrNone(sdef.methods)(mSpec _)
      // (sdef.methods.foldLeft
      //   (Option(Seq.empty[MethodSpec]))
      //   { (resOpt, mdef) => 
      //     resOpt.flatMap(res => mSpec(mdef).map(res :+ _))
      //   }
      // )

    methodSpecsOpt.map(StateSpec(sdef.name, _))
  }

  val infer : Term => Option[Tuple3[Context, Type, Context]] =
    attr {
      case t => {
        val constraints = ConstraintGenerator.generateConstraints(t)
        ConstraintSolver.solve(constraints, t)
      }
    }

  def inferFunType(f : FunValue) : Option[FunType] = {
    (f->infer).map(soln => {
      val (inCtx, ty, outCtx) = soln
      ty match {
        case ft @ FunType(params, ret) =>
          ft
        case _ => throw new Error("constraint solving returned mismatched type?")
      }
    })
  }

  def inferredParamEffect(paramName : String) : FunValue => Option[EffectType] =
    attr {
      case t : FunValue => {
        val pNum = t.params.indexWhere(_.name == paramName)
        inferFunType(t).map(ft => {
          ft.params(pNum)
        })
      }
    }

  /** determines the effect type for a parameter */
  val pEffect : ParamDef => Option[EffectType] =
    childAttr {
      case p @ ParamDef(name, typeInfo) => {
        case f @ FunValue(params, body) => 
          typeInfo orElse (f->inferredParamEffect(name))
      }
    }

  val fBodyType : FunValue => Option[Type] =
    attr {
      case f @ FunValue(params, body) => {
        if(fullyTypedFunction(f)) body->ttype
        else inferFunType(f).map(ft => ft.ret)
      }
    }

  def fullyTypedFunction(f : FunValue) = {
    f.params.forall(_.typeInfo.isDefined)
  }

  /**
   * Determines the type for a given term.
   */
  val ttype : Term => Option[Type] =
    attr {
      /* values */
      case UnitValue() => Some(UnitType())
      case TrueValue() => Some(BoolType())
      case FalseValue() => Some(BoolType())
      case o @ ObjValue(states,state) => {
        val objErrors = o->objectErrors
        if(objErrors.isEmpty) {
          val stateSpecsOpt =
            mapAllOrNone(states)(sSpec(_))
            // (states.foldLeft
            //   (Option(Seq.empty[StateSpec]))
            //   { (resOpt, sdef) =>
            //     resOpt.flatMap(res => sSpec(sdef).map(res :+ _))
            //   }
            // )

          stateSpecsOpt.map(ObjType(_, state))
        } else {
          objErrors.foreach(err => {
            val msg = err match {
              case DuplicateState(state) => "duplicate state: " + state
              case MissingState(state) => "missing state: " + state
              case DuplicateMethod(state, method) =>
                "duplicate method in state " + state + ": " + method
            }

            message(err.refPoint.getOrElse(o), msg)
          })
          None
        }
      }
      case FunValue(params,body) => {
        val paramEffectsOpt = mapAllOrNone(params)(_->pEffect)
        paramEffectsOpt.flatMap(params => (body->ttype).map(FunType(params, _)))
      }

      /* terms */
      case LetBind(_,_,body) => body->ttype
      case Sequence(l,r) => r->ttype
      case t @ MethCall(o,m) => 
        ((t->input)(o)) match { 
          // TODO: error message for bad function calls?
          case Some(o @ ObjType(_,_)) => o.retType(m) 
          case _ => None
        }
      case t @ FunCall(name, params) =>
        ((t->input)(name)) match {
          // TODO: depends on whether enough params were passed, but
          // may be beneficial to just presuppose correct type anyway
          // to detect more errors
          case Some(FunType(_,retType)) => Some(retType)
          case _ => None
        }
      case t @ If(cond,thn,els) => {
        val t1Opt = thn->ttype
        val t2Opt = els->ttype
        Type.joinOpt(t1Opt, t2Opt)
      }
    }

  /** 
   * constructs an input context for a set of parameters defined on a function
   * literal.
   */
  def contextFromParams(params : Seq[ParamDef]) =
    (params.foldLeft
      (emptyContext)
      { (map,param) => 
        val pTypeOpt = (param->pEffect).map(_.before)
        map + (param.name -> pTypeOpt)
      }
    )
    
  /** determines the input context for a term */
  val input : Term => Context =
    childAttr {
      case t => {
        case FunValue(params,body) => 
          // t must be the body of the function
          contextFromParams(params)
        case p @ LetBind(name,value,body) => {
          if (t eq value) p->input
          else value->output + Pair(p.varName,p.value->ttype)
        }
        case p @ Sequence(left, right) => 
          (if (t eq left) p->input else p.left->output)
        case p @ If(cond, thn, els) => {
          if(t eq cond) p->input
          else cond->output
        }
        // return values for methods are typed with an empty context
        case p : MethodDef => emptyContext
        case p if p != null && p.isRoot => emptyContext
        // the root term always has an empty context
        case null if t.isRoot => emptyContext
        case p => {
          println("unmatched case " + p + " --- " + t)
          emptyContext
        }
      }
    }

  /**
   * using the derived input context for a term, determines the type of
   * a particular variable in that context if it is known.
   */
  def inputType(t : Term, varName : String) : Option[Option[Type]] = 
    (t->input) get varName

  /**
   * determines the output context for a term.
   */
  val output : Term => Context =
    attr {
      case t : Value => t->input
      case LetBind(varName,valTerm,bodyTerm) => bodyTerm->output - varName
      case t @ MethCall(objName,methName) => methCallOutput(t)
      case Sequence(l,r) => r->output
      case t : FunCall => funCallOutput(t)
      case t : If => ifOutput(t)
    } 

  def methCallOutput(t : MethCall) : Context = {
    val newType = inputType(t, t.objVarName) match {
      case None => {
        message(t, "attempt to use unknown variable %s as a method call receiver".format(t.objVarName))
        None
      }
      case Some(None) => None // variable with no type, due to prior type error
      case Some(Some(o @ ObjType(states,_))) => {
        val nextStateSetOpt = o.nextStateSet(t.methName)
        val nextTypeOpt = nextStateSetOpt.map { nextStateSet => 
          Some(ObjType(states, nextStateSet))
        }

        nextTypeOpt.getOrElse {
          message(t, "attempt to call unavailable method %s on receiver %s of type %s".format(t.methName, t.objVarName, o))
          None
        }
      }
      case Some(Some(x)) => {
        message(t, "attempt to call method on variable %s of type %s".format(t.objVarName, x))
        None
      }
    }

    (t->input).updated(t.objVarName, newType)
  }

  def funCallOutput(t : FunCall) : Context = {
    val newParamTypes : Seq[Option[Type]] = inputType(t, t.funName) match {
      case Some(Some(FunType(defParams,_))) => {
          val paramTypes = t.paramNames.map(param => {
            val tyOpt = inputType(t, param) match {
              case Some(None) => None
              case Some(Some(ty)) => Some(ty)
              case None => {
                message(t, "unknown parameter variable " + param)
                None
              }
            }

            (param, tyOpt)
          })

          defParams.zip(paramTypes).map { case (effectType, (paramName, paramTypeOpt)) =>
            paramTypeOpt.map { paramType =>
              // TODO: this does not respect subtyping or use remap
              if(effectType.before != paramType && paramType != None) {
                message(t, "parameter " + paramName 
                  + " is not of the required type for function " +
                  t.funName + ": expected " + effectType.before +
                  ", but found " + paramType)
              }
              // always just produce the output type as defined on the effect
              // as this may allow more errors to be found in the program
              effectType.after
            }
          }
        }
      case Some(Some(x)) => {
        message(t, "attempt to treat variable %s as a function when it is of type %s".format(t.funName, x))
        t.paramNames.map(_ => None)
      }
      case Some(None) => t.paramNames.map(_ => None)
      case None => {
        message(t, "attempt to use unknown variable %s as a function".format(t.funName))
        t.paramNames.map(_ => None)
      }
    }

    (t->input -- t.paramNames) ++ (t.paramNames zip newParamTypes)
  }

  def ifOutput(t : If) = {
    joinContexts(t.whenTrue->output, t.whenFalse->output) match {
      case Left(errors) => {
        errors.foreach(err => {
          message(t, err match {
            case DifferentDomains(_, _) =>
              "output domains differ"
          })
        })
        (t.whenTrue->output).mapValues(_ => None)
      }
      case Right(ctx) => ctx
    }
  }

  def check(t : Term) : Boolean = {
    org.kiama.attribution.Attribution.initTree(t)
    // force evaluation of the term's type and output context
    // this should elicit all type errors
    t->ttype
    t->output

    // success is then gauged on whether any error messages were
    // reported
    (messagecount == 0)
  }
}

import jline.Terminal
import jline.TerminalFactory

class FullTracePrinter(term : Terminal) extends org.kiama.output.PrettyPrinter {

  import TypeChecker._

  override val defaultIndent = 2

  var nextTermId = 0

  val termId : Term => Doc =
    attr {
      case _ : Term => {
        nextTermId += 1
        TID(nextTermId.toString())
      }
    }

  def resetTermIds = {
    nextTermId = 0
  }

  def pretty (t : Term) : String = super.pretty(show(t), term.getWidth())

  def show(t : Term) : Doc = {
    val tid = t->termId
    val children = Seq.empty[Doc]
    val (doc, terms) = t match {
      case UnitValue() => 
        Pair(UNIT, Seq.empty)
      case TrueValue() =>
        Pair(TRUE, Seq.empty)
      case FalseValue() =>
        Pair(FALSE, Seq.empty)
      case ObjValue(states, state) => {
        val sDocs = states map (showStateDef _)
        val objBody = nest(lsep(sDocs, space))
        val objDoc = brackets(objBody <> line) <> "@" <> state
        val subTerms = states flatMap (_.methods map (_.ret))
        Pair(objDoc, subTerms)
      }
      case FunValue(params, body) => {
        val pDocs = params map showParams
        val paramDoc = group("\\" <> parens(ssep(pDocs, ",")))
        val bodyTermId = body->termId
        val funDoc = paramDoc <> "." <> parens(bodyTermId)
        Pair(funDoc, Seq(body))
      }
      case LetBind(varName, value, body) => {
        val valueTermId = value->termId
        val bodyTermId = body->termId
        val termDoc = 
          LET <+> varName <+> "=" <+> valueTermId <+> IN <+> bodyTermId
        Pair(termDoc, Seq(value, body))
      }
      case MethCall(objVarName, methName) => 
        Pair(objVarName <> "." <> methName, Seq.empty)
      case Sequence(left, right) => {
        val leftTermId = left->termId
        val rightTermId = right->termId
        Pair(leftTermId <> ";" </> rightTermId, Seq(left, right))
      }
      case FunCall(funName, paramNames) => 
        Pair(funName <> parens(lsep(paramNames map (text _), ",")), Seq.empty)
      case If(cond, thn, els) =>
        val condId = cond->termId
        val thnTermId = thn->termId
        val elsTermId = els->termId
        Pair("if" <+> condId <+> "then" <+> thnTermId <+> "else" <+> elsTermId,
          Seq(cond, thn, els))
    }
    val termWithType = doc <+> ":" <+> TYPE(showTypeOpt(t->ttype))
    val tidDoc = tid <> ":"
    val (inContext, outContext) = showContexts(t->input, t->output)

    val docWithContexts = tidDoc <+> group(inContext </> termWithType </> outContext)

    docWithContexts </> nest(lsep(terms.map(show _), " "))
  }

  val showParams : ParamDef => Doc = (p => 
    p.name <+> ":" <+> 
      ((p.typeInfo map showEffect) getOrElse empty))

  val showEffect : EffectType => Doc =
    eff => showType(eff.before) <+> ">>" <+> showType(eff.after)

  def showStateDef(s : StateDef) : Doc = {
    val mDocs = s.methods map showMethodDef
    s.name <+> braces(space <> nest(lsep(mDocs, ",")) <> line)
  }

  val showMethodDef : MethodDef => Doc = m => {
    val tid = m.ret->termId
    (m.name <+> "=" <+> parens(tid <+> "," </> m.nextState))
  }
    
  def showTypeOpt(t : Option[Type]) : Doc =
    t match {
      case Some(x) => showType(x)
      case None => "BAD"
    }

  def showType(t : Type) : Doc =
    t match {
      case UnitType() => "Unit"
      case BoolType() => "Bool"
      case FunType(params, ret) => {
        val pDocs = params map showEffect
        parens(ssep(pDocs, ",")) <+> "->" <+> showType(ret)
      }
      case TopType() => "Top"
      case ObjType(states, currentStateSet) => {
        val sDocs = states map (showStateSpec _)
        (braces(space <> nest(fillsep(sDocs, space)) <> line) <> 
          "@" <> showStateSet(currentStateSet))
      }
    }

  def showStateSet(states : Set[String]) = {
    if(states.size == 1) text(states.head)
    else braces(lsep(states.map(text(_)).toSeq, ","))
  }

  def showStateSpec(s : StateSpec) = {
    val mDocs = s.methods map showMethodSpec
    s.name <+> braces(nest(lsep(mDocs, ";")) </> empty)
  }

  val showMethodSpec : MethodSpec => Doc =
    (m => m.name <+> ":" <+> showType(m.ret) <+> ">>" <+> m.nextState)

  def showContexts(in : Context, out : Context) : Pair[Doc, Doc] = {
    val commonVars = in.keySet.intersect(out.keySet)
    val (unchanged, changed) = commonVars.partition(v => in(v) == out(v))

    val deletedVars = in.filterKeys(in.keySet -- commonVars)
    val newVars = out.filterKeys(out.keySet -- commonVars)
    val unchangedVars = in.filterKeys(unchanged)
    val inChangedVars = in.filterKeys(changed)
    val outChangedVars = out.filterKeys(changed)

    val valFolder : String => (Seq[Doc],ContextEntry) => Seq[Doc] = 
      colorStr => (_ :+ showVarMapping(_, colorStr))
    val docFolder : (String,Context) => Seq[Doc] =
      (colorStr, doc) => doc.foldLeft(Seq.empty[Doc])(valFolder(colorStr))
    
    val unchangedDocs = docFolder(Console.BLACK, unchangedVars)
    val inChangedDocs = docFolder(Console.YELLOW, inChangedVars)
    val outChangedDocs = docFolder(Console.YELLOW, outChangedVars)

    val deletedDocs = docFolder(Console.RED, deletedVars)
    val newDocs = docFolder(Console.GREEN, newVars)

    val docProducer = 
      (docs : Seq[Doc]) => group(brackets(nest(fillsep(docs, ","))))

    val inDoc = docProducer(unchangedDocs ++ inChangedDocs ++ deletedDocs)
    val outDoc = docProducer(unchangedDocs ++ outChangedDocs ++ newDocs)

    Pair(inDoc, outDoc)
  }

  def showVarMapping(p : Pair[String,Option[Type]], colorStr : String) : Doc = 
    color(colorStr)(p._1 <+> ":" <+> showTypeOpt(p._2))

  val color : String => Doc => Doc =
    (if(term.isAnsiSupported())
      ((colorStr:String) => (d:Doc) => colorStr <> d <> Console.RESET)
    else (_ => (d:Doc) => d))
  
  val VALUE : String => Doc = color(Console.BLUE)(_)
  val KEYWORD : String => Doc = color(Console.MAGENTA)(_)
  val TID : String => Doc = color(Console.BOLD)(_)
  val TYPE : Doc => Doc = color(Console.CYAN)

  val UNIT = VALUE("unit")
  val TRUE = VALUE("true")
  val FALSE = VALUE("false")
  val ERROR = VALUE("error")
  val LET = KEYWORD("let")
  val IN = KEYWORD("in")
}

object FullTracePrinter extends FullTracePrinter(TerminalFactory.create())