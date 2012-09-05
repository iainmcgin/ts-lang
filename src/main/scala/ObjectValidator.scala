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
import org.kiama.attribution.Attributable

object ObjectValidator {

  val objectErrors : Attributable => List[MissingState] =
    attr {
      case o : ObjValue => {
        var errors = List.empty[MissingState]
        if (!o.stateMap.contains(o.state))
          errors = MissingState(o.state, o, o) :: errors

        o.states.flatMap(_.methods).foreach(m => {
          if (!o.stateMap.contains(m.nextState)) 
            errors = MissingState(m.nextState, o, m) :: errors
        })

        errors
      }
      case _ => List.empty[MissingState]
    }

  def allObjectErrors(a : Attributable) : List[MissingState] =
    (a.children.foldLeft
      (a->objectErrors)
      ((errs, child) => errs ++ allObjectErrors(child))
    )

}