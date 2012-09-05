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

import org.kiama.util.Console
import org.kiama.util.Emitter
import org.kiama.util.Messaging._
import org.kiama.util.ParsingREPL

import org.slf4j.LoggerFactory
import ch.qos.logback.classic.Level
import ch.qos.logback.classic.Logger
import org.slf4j.{Logger => SLF4JLogger}


object Driver extends ParsingREPL[Term] with Parser {

  override def main(args : Array[String]) {
    if(!args.contains("-debug")) {
      disableLogging()
    }
    println("TS REPL - press CTRL+D to exit. Type single-line terms for type analysis")
    super.main(args)
  }

  def disableLogging() {
    val root = 
      LoggerFactory.getLogger(SLF4JLogger.ROOT_LOGGER_NAME).asInstanceOf[Logger]
    root.setLevel(Level.OFF)
  }

  override def start = phrase (term)

  override def process(t : Term) {
    FullTracePrinter.resetTermIds
    resetmessages
    TypeChecker.check(t)

    if(messagecount > 0) {
      report()
      false
    }

    println("full trace for term: ")
    println(FullTracePrinter.pretty(t))
  }
}