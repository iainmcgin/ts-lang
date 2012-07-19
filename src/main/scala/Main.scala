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

import org.kiama.util.Console
import org.kiama.util.Emitter
import org.kiama.util.Messaging._
import org.kiama.util.ParsingREPL

object Driver extends ParsingREPL[Term] with Parser {

  override def main(args : Array[String]) {
    println("TS0 REPL - press CTRL+D to exit. Type single-line terms for type analysis")
    super.main(args)
  }

  override def start = phrase (term)

  override def process(t : Term) {
    resetmessages
    TypeChecker.check(t)

    if(messagecount > 0) {
      report()
      false
    } else {
      println(FullTracePrinter.pretty(t))
    }
  }
}