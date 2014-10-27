package main.scala.FirstOrder

import scala.collection.immutable.List

/**
 * Created by enxhi on 10/25/14.
 */
case class Func(f : String, args : List[Term]) extends Term {
  override def toString = f + "(" + args.mkString(",") + ")"
  def freeVars = args.flatMap(_.freeVars).distinct
  def variables = args.flatMap(_.variables).distinct
  def constants = args.flatMap(_.constants).distinct
  def wff(sig : Signature, con : Context) = sig.hasFunc(f,args.length)
  def replaceVar(cons : Term, name : String) =  Func(f, args.map(_.replaceVar(cons,name)))
}
