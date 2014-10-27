package main.scala.FirstOrder

import scala.collection.immutable.{List, Nil}

/**
 * Created by enxhi on 10/25/14.
 */
case class Variable(name : String) extends Term {
  override def toString =  "?" + name
  def freeVars = List(name)
  def variables = List(name)
  def constants = Nil
  def wff(sig : Signature, con : Context) = con.containsVar(name)
  def replaceVar(cons : Term, n:String) = if( n==name) cons else this
}
