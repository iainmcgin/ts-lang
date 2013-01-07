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

  val objectErrors : Attributable => Seq[ObjValidationError] =
    attr {
      case o : ObjValue => o.validate()
      case o : ObjType => o.validate()
      case _ => Seq.empty[ObjValidationError]
    }

  def allObjectErrors(a : Attributable) : Seq[ObjValidationError] =
    (a.children.foldLeft
      (a->objectErrors)
      ((errs, child) => errs ++ allObjectErrors(child))
    )
}