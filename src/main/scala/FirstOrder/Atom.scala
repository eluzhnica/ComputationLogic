package main.scala.FirstOrder

import scala.collection.immutable.Nil

/**
 * Created by enxhi on 10/25/14.
 */
case class Atom(name : String) extends Formula {
  override def toString = name
  def freeVars = Nil
  def constants = Nil
  def wff(sig : Signature, con : Context) = true
  def translate = new Atom(name)
  def replaceVar(cons : Term, n : String) = Atom(name)
  def variables = Nil
}
