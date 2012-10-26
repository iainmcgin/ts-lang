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

/**
 * Redirectable proxy to a value of type T.
 */
class Proxy[T](private var link : Either[Proxy[T], T])
 {

  /**
   * Returns a canonical proxy to the proxied value. Additionally,
   * this will perform path compression on all proxies found between
   * this proxy and the value.
   */
  def toCanonical() : Proxy[T] = {
    link.fold(
      p => { val canon = p.toCanonical(); link = Left(canon); canon },
      _ => this
    )
  }

  def isCanonical() : Boolean = link.isRight

  def linkTo(other : Proxy[T]) {
    val c1 = this.toCanonical()
    val c2 = other.toCanonical()

    if(!(c1 eq c2)) c1.link = Left(Proxy.toProxy(c2))
  }

  def get() : T = toCanonical().link.right.get
  def apply() : T = get()

  /**
   * FOR TESTING ONLY, extracts the current link within this proxy
   */
  private[ts] def currentLink = link

  override def equals(other : Any) = other match {
    case other : AnyRef if other eq this => true
    case other : Proxy[_] => 
      this.toCanonical().link == other.toCanonical().link
    case _ => false
  }

  override def hashCode() = toCanonical().link.hashCode()

  override def toString = link match {
    case Left(p) => "Proxy -> " + p.toString
    case Right(v) => "Canon " + v
  }
}

object Proxy {
  def toValue[T](v : T) : Proxy[T] = new Proxy(Right(v))
  def toProxy[T](p : Proxy[T]) : Proxy[T] = new Proxy(Left(p))
}