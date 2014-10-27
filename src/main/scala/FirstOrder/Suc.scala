package main.scala.FirstOrder

/**
 * Created by enxhi on 10/25/14.
 */
case class Suc(n : Nat) extends Nat {
  def toInt = n.toInt + 1
}
