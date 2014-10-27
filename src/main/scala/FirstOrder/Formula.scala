package main.scala.FirstOrder

import scala.collection.immutable.List

/**
 * Created by enxhi on 10/25/14.
 */
abstract class Formula {
  def freeVars : List[String]
  def variables : List[String]
  def constants : List[String]
  def wff(sig : Signature, con : Context) : Boolean
  def translate() : Formula
  def replaceVar(cons : Term, name : String) : Formula
}
