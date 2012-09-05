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
    (ident <~ ":=") ~ subterm                             ^^ Update |
    subterm

  lazy val subterm : PackratParser[Term] =
    "(" ~> term <~ ")" |
    (ident <~ "(") ~ repsep(ident, ",") <~ ")"                  ^^ FunCall |
    (ident <~ ".") ~ ident                                      ^^ MethCall |
    ("if" ~> subterm) ~ ("then" ~> subterm) ~ ("else" ~> term)  ^^ If |
    value

  lazy val value : PackratParser[Value] =
    "unit" ^^ (_ => UnitValue()) |
    ("[" ~> rep1(statedef) <~ "]" <~ "@") ~ ident ^^ ObjValue |
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
    ("{" ~> rep1(statespec) <~ "}" <~ "@") ~ ident ^^ ObjType |
    ("(" ~> repsep(effectType, ",") <~ "->") ~ typespec ^^ FunType

  lazy val statespec : PackratParser[StateSpec] =
    (ident <~ "{") ~ rep(methodspec) <~ "}" ^^ StateSpec

  lazy val methodspec : PackratParser[MethodSpec] =
    (ident <~ ":") ~ (typespec <~ ">>") ~ ident ^^ MethodSpec

  def ident: Parser[String] =
    """[a-zA-Z_]\w*""".r
}