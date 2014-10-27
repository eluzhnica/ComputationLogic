package main.scala.FirstOrder

import scala.collection.immutable.List

/**
 * Created by enxhi on 10/25/14.
 */
case class Neg(form : Formula) extends Connective(List(form)) {
  override def toString = "!" + form.toString
  def wff(sig : Signature, con : Context ) = form.wff(sig,con)
  def translate = Neg(form.translate)
  def replaceVar(cons : Term, name : String) = Neg(form.replaceVar(cons, name : String))
}
