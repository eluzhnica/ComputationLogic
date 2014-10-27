package main.scala.FirstOrder

import scala.collection.immutable.{List, Nil}

/**
 * Created by enxhi on 10/25/14.
 */
case class Constant(name : String) extends Term {
  override def toString = name
  def freeVars = Nil
  def variables = Nil
  def constants = List(name)
  def wff(sig : Signature, con : Context) = true
  def replaceVar(cons : Term, name :String) = this
}
