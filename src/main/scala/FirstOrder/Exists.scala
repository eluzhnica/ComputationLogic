package main.scala.FirstOrder

/**
 * Created by enxhi on 10/25/14.
 */
case class Exists(context : Context, body : Formula) extends Formula {
  override def toString = "∃" + context.vars.mkString(",") + "." + body.toString
  def freeVars = body.freeVars.filterNot(context.containsVar)
  def variables = body.variables.distinct
  def constants = body.constants.distinct
  def wff(sig : Signature, con : Context) = body.wff(sig, con + context)
  def translate = Neg(Forall(context,Neg(body.translate)))
  def replaceVar(cons : Term, name : String) = Exists(context, body.replaceVar(cons, name : String))
}
