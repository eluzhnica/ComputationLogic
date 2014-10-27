package main.scala.FirstOrder

import scala.collection.immutable.List

/**
 * Created by enxhi on 10/25/14.
 */
case class Impl(l : Formula, r : Formula) extends Connective(List(l,r)) {
  override def toString = "(" + l.toString + "=>’" + r.toString + ")"
  def wff(sig : Signature, con : Context) = l.wff(sig,con) && r.wff(sig, con)
  def translate = Disj(Neg(l),r).translate
  def replaceVar(cons : Term, name : String) = Impl(l.replaceVar(cons, name : String),r.replaceVar(cons, name : String))
}
