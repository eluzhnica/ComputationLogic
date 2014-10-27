package main.scala.FirstOrder

import scala.collection.immutable.List

/**
 * Created by enxhi on 10/25/14.
 */
 abstract class Connective(args : List[Formula]) extends Formula {
  def freeVars = args.flatMap(_.freeVars).distinct
  def variables = args.flatMap(_.variables).distinct
  def constants = args.flatMap(_.constants).distinct
  def wff(sig : Signature, con : Context) : Boolean
}
