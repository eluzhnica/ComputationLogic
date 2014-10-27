package main.scala.FirstOrder

import scala.collection.immutable.List

/**
 * Created by enxhi on 10/25/14.
 */
case class Disj(l : Formula, r : Formula) extends Connective(List(l,r)) {
  override def toString = "(" + l.toString + "v" + r.toString + ")"
  def wff(sig : Signature, con : Context) = l.wff(sig,con) && r.wff(sig, con)
  def translate = Neg(Conj(Neg(l.translate),Neg(r.translate)))
  def replaceVar(cons : Term, name : String) = Disj(l.replaceVar(cons, name : String),r.replaceVar(cons, name : String))
}
