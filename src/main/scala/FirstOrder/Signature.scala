package main.scala.FirstOrder

import scala.collection.immutable.Map

/**
 * Created by enxhi on 10/25/14.
 */
// Problem 4
//assumes open set of variables, atoms and constants names -- maybe not ideal but that's how the problem was given
class Signature(val funcs : Map[String,Int], val preds : Map[String, Int]){
  def hasFunc(name : String, arity : Int) = funcs.get(name) match {
    case None => false
    case Some(a) => a == arity
  }
  def hasPred(name : String, arity : Int) = preds.get(name) match {
    case None => false
    case Some(a) => a == arity
  }
}
