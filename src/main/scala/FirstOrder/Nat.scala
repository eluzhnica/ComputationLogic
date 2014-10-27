package main.scala.FirstOrder

/**
 * Created by enxhi on 10/25/14.
 */
// Problem 2
object Nat {
  def sum(m : Nat, n : Nat) : Nat = m match {
    case Zero => n
    case Suc(m0) => Suc(sum(m0,n))
  }

  def mul(m : Nat, n : Nat) : Nat = m match {
    case Zero => Zero
    case Suc(m0) => sum(n, mul(m0,n))
  }

}

// Problems 1
abstract class Nat {
  def toInt : Int
}