package main.scala.FirstOrder

import scala.collection.immutable.List

/**
 * Created by enxhi on 10/25/14.
 */
//Problem 3  -- Problem 7 interspersed (.freeVars method)
class Context(var vars : List[String]){
  def containsVar(p : String) : Boolean = vars.exists(_ == p)
  def +(con : Context) : Context = {
    vars ::: con.vars
    this
  }
}
