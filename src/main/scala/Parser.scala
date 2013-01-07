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

trait Parser extends org.kiama.util.PositionedParserUtilities {

  lazy val term : PackratParser[Term] =
    (term <~ ";") ~ term                                  ^^ Sequence |
    ("let" ~> ident <~ "=") ~ (subterm <~ "in") ~ term    ^^ LetBind |
    subterm

  lazy val subterm : PackratParser[Term] =
    "(" ~> term <~ ")" |
    (ident <~ "(") ~ repsep(ident, ",") <~ ")"                    ^^ FunCall |
    (ident <~ ".") ~ ident                                        ^^ MethCall |
    ("if" ~> subterm) ~ ("then" ~> subterm) ~ ("else" ~> subterm) ^^ If |
    value

  lazy val value : PackratParser[Value] =
    "unit"                                            ^^ (_ => UnitValue()) |
    "true"                                            ^^ (_ => TrueValue()) |
    "false"                                          ^^ (_ => FalseValue()) |
    ("[" ~> rep1(statedef) <~ "]" <~ "@") ~ ident               ^^ ObjValue |
    ("\\" ~> "(" ~> repsep(paramdef, ",") <~ ")" <~ ".") ~ term ^^ FunValue

  lazy val statedef : PackratParser[StateDef] =
    (ident <~ "{") ~ repsep(methdef, ";") <~ "}" ^^ StateDef

  lazy val methdef : PackratParser[MethodDef] =
    (ident <~ "=" <~ "(") ~ (value <~ ",") ~ ident <~ ")" ^^ MethodDef

  lazy val paramdef : PackratParser[ParamDef] =
    ident ~ opt(":" ~> effectType) ^^ ParamDef

  lazy val effectType : PackratParser[EffectType] =
    (typespec <~ ">>") ~ typespec ^^ EffectType

  /* type parsers */

  lazy val typespec : PackratParser[Type] =
    "Unit" ^^ (_ => UnitType()) |
    "Bool" ^^ (_ => BoolType()) |
    ("{" ~> rep1(statespec) <~ "}" <~ "@") ~ ident ^^ ObjType |
    ("(" ~> repsep(effectType, ",") <~ "->") ~ typespec ^^ FunType |
    ("Top" | "⊤") ^^ (_ => TopType())

  lazy val statespec : PackratParser[StateSpec] =
    (ident <~ "{") ~ repsep(methodspec, ";") <~ "}" ^^ StateSpec

  lazy val methodspec : PackratParser[MethodSpec] =
    (ident <~ ":") ~ (typespec <~ "=>") ~ ident ^^ MethodSpec

  def ident: Parser[String] =
    """[a-zA-Z_]\w*""".r

  def checkObj(obj : ObjType) = {
    obj.validate
  }
}