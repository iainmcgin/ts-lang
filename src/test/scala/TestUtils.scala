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

object TestUtils {

  val unitMT = MultiTerm(0, List.empty)

  def v(tv : TypeVar) = Variable(tv.v, null)
  def vset(tvs : TypeVar*) = Set(tvs.map(tv => v(tv)) :_*)

  implicit def intToVarTE(i : Int) = VarTE(TypeVar(i))
  implicit def intToTypeVar(i : Int) = TypeVar(i)

  object parse extends Parser {
    def apply(termStr : String) = parseString(term, termStr)
  }
}