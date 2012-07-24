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

package uk.ac.gla.dcs

package object ts0 {

  type TypeVar = Int
  type ContextVar = Int
  type ObjectVar = Int
  type StateVar = Int

  /** A typing context, which consists of variable names mapped to types */
  type Context = Map[String,Type]

  /** an empty context, which maps all variable names to ErrorType */
  val emptyContext : Context = Map.empty.withDefaultValue(ErrorType())
}