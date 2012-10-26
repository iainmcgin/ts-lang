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

abstract class Command
case class ShowTree(t : Term) extends Command
case class Infer(debug : Option[String], t : Term) extends Command
case class Exit() extends Command

trait REPLParser extends org.kiama.util.PositionedParserUtilities with Parser {

  lazy val command : PackratParser[Command] =
    opt("tree") ~> term                ^^ ShowTree |
    "infer" ~> opt("debug") ~ term     ^^ Infer |
    "exit"                             ^^ (_ => Exit())
}


object Driver extends ParsingREPL[Command] with REPLParser {

  override def main(args : Array[String]) {
    if(!args.contains("-debug")) {
      disableLogging()
    }
    println("TS REPL - press CTRL+D to exit. Type single-line terms to view " +
      "term tree with contexts, or type 'infer ...' to show type inference " +
      "trace")

    super.main(args)
  }

  def disableLogging() {
    val root = 
      LoggerFactory.getLogger(SLF4JLogger.ROOT_LOGGER_NAME).asInstanceOf[Logger]
    root.setLevel(Level.OFF)
  }

  def enableLogging() {
    val root = LoggerFactory.getLogger(SLF4JLogger.ROOT_LOGGER_NAME).asInstanceOf[Logger]
    root.setLevel(Level.DEBUG)
  }

  override def start = phrase (command)

  override def process(c : Command) {
    c match {
      case ShowTree(t) => checkAndTrace(t)
      case Infer(debug, t) => infer(debug.isDefined, t)
      case Exit() => java.lang.System.exit(0)
    }
  }

  def checkAndTrace(t : Term) {
    FullTracePrinter.resetTermIds
    resetmessages
    TypeChecker.check(t)

    if(messagecount > 0) report()

    println("full trace for term: ")
    println(FullTracePrinter.pretty(t))
  }

  def infer(debug : Boolean, t : Term) {
    resetmessages
    org.kiama.attribution.Attribution.initTree(t)
    val constraints = ConstraintGenerator.generateConstraints(t)

    println("term tree:")
    ConstraintGenerator.printInferenceTree(t)
    println("constraints:")
    println(constraints)
    val solver = new ConstraintSolver(t)
    val (contexts, eqConstraints, subConstraints) = 
      solver.reduceToTypeConstraints(constraints)
    
    println("contexts after normalisation:")
    contexts.keySet.toList.sortBy(_.v).foreach(cv => 
      println("\t" + cv + " = " + contexts(cv).mkString(", ")))

    println("full type constraint set:")
    println("\t" + eqConstraints.mkString("\n\t"))
    println("\t" + subConstraints.mkString("\n\t"))

    solver.solveTypeConstraints(contexts, 
      eqConstraints, 
      subConstraints)

    if(debug) enableLogging()
    val solutionOpt = ConstraintSolver.solvePolymorphic(constraints, t)
    if(debug) disableLogging()

    println("----------")

    if(messagecount > 0) report()

    solutionOpt match {
      case Some(soln) => {
        println("input context: " + soln._1)
        println("type: " + soln._3)
        println("output context: " + soln._4)
      }
      case None => {
        println("constraints have no solution - term is untypeable")
      }
    }
  }
}