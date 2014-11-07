
import main.scala.HigherOrder._
object Test	 {
  //Problem 3

  val list : List[(String,String)] = Nil
  list.exists({case(x,y) => x==y})

  val expr = Apply(Lambda(Var("e"), Arrow(E,Arrow(E,T)), Lambda(Var("y"), Arrow(E,E), Var("y"))), Var("k"))
  Functions.betanf(expr)
}