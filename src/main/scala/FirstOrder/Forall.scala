package main.scala.FirstOrder

/**
 * Created by enxhi on 10/25/14.
 */
case class Forall(context : Context, body : Formula) extends Formula {
  override def toString = "∀" + context.vars.mkString(",") + "." + body.toString
  def freeVars = body.freeVars.filterNot(context.containsVar)
  def variables = body.variables.distinct
  def constants = body.constants.distinct
  def wff(sig : Signature, con : Context) = body.wff(sig, con + context)
  def translate = Forall(context,body.translate)
  def replaceVar(cons : Term, name : String) = {
    cons match{
      case v : Variable =>{
        if(context.vars.contains(name)) {
          context.vars = context.vars.map { case v.name => name; case x => x}
        }
      }
      case _ =>
    }
    Forall(context, body.replaceVar(cons, name : String))
  }
}
