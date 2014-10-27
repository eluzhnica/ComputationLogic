package main.scala.FirstOrder

import scala.collection.immutable.List

/**
 * Created by enxhi on 10/25/14.
 */
case class Pred(p : String, args : List[Term]) extends Formula {
  override def toString = p + "(" + args.mkString(",") + ")"
  def freeVars = args.flatMap(_.freeVars).distinct
  def constants = args.flatMap(_.constants).distinct
  def variables = args.flatMap(_.variables).distinct
  def wff(sig : Signature, con : Context) = sig.hasPred(p,args.length)
  def translate = new Pred(p,args)
  def replaceVar(cons : Term, name :String) = Pred(p,args.map(_.replaceVar(cons,name)))
}
