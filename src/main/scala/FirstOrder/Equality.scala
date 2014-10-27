package main.scala.FirstOrder

/**
 * Created by enxhi on 10/25/14.
 */
case class Equality(l : Term, r : Term) extends Formula {
  override def toString = "(" + l.toString + " = ”" + r.toString + ")"

  def wff(sig: Signature, con: Context) = l.wff(sig, con) && r.wff(sig, con)
  def constants = (l.constants ::: r.constants).distinct
  def freeVars = (l.freeVars ::: r.freeVars).distinct
  def variables = (l.variables ::: r.variables).distinct
  def translate = new Equality(l, r)

  def replaceVar(cons: Term, name: String) = Equality(l.replaceVar(cons, name: String), r.replaceVar(cons, name))
}
