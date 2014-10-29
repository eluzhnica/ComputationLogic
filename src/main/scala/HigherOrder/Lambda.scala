package main.scala.HigherOrder

import scala.collection.mutable


/**
 * Created by enxhi on 10/25/14.
 */

abstract class Type{
  def ->:(to : Type) : Type
}

abstract class Base extends Type

object E extends Base{
  def ->:(to : Type) = Arrow(to,E)
  override def toString = "E"
}

object T extends Base{
  def ->:(to : Type) = Arrow(to,T)
  override def toString = "T"
}

case class Arrow(left: Type, right: Type) extends Type{
  def ->:(to : Type) = Arrow(to,this)
  override def toString = "("+left.toString + "->"+ right.toString +")"
}


abstract class Formula {
  //  def checkVariableTypeMatch(variable : Var) : Boolean
  def free: List[Var]

  def bound: List[Var]

  def rename(variable: Var, renamed: Var): Formula
}

case class Const(name: String, tp: Type) extends Formula {
  //  def checkVariableTypeMatch(variable : Var) = true
  def free = Nil

  def bound = Nil

  def rename(variable: Var, renamed: Var) = Const(name, tp)

  override def toString = "C(" + name +")"
}

case class Var(name: String) extends Formula {
  //inferred type
  var inftype: Type = null

  //  def checkVariableTypeMatch(variable : Var) = if(name == variable.name) tp == variable.tp else true
  def free = List(this)

  def bound = Nil

  def rename(variable: Var, renamed: Var) = if (variable == this) renamed else Var(name)

  override def toString = "V("+name+")"
}

case class Apply(pred: Formula, form: Formula) extends Formula {

  def free = form.free
  def bound = form.bound
  def rename(variable: Var, renamed: Var) = Apply(pred.rename(variable, renamed), form.rename(variable, renamed))
  override def toString = "("+pred.toString +")("+ form.toString +")"
}

//maybe removing the type from variable
case class Lambda(variable: Var, varTpe: Type, form: Formula) extends Formula {
  variable.inftype = varTpe
  variableBind(this)

  private def variableBind(form : Lambda) = {

    def bindVariable(form: Formula, vartype : Var): Unit = {
      form match {
        case Apply(pred, formula) => {
          bindVariable(pred, vartype)
          bindVariable(formula, vartype)
        }
        case Lambda(variable, tpe, body) => {
          if(variable.name != vartype.name) {
            bindVariable(body, vartype)
          }
        }
        case t: Var => {
          if (vartype.name == t.name) {
            t.inftype = vartype.inftype
          }
        }
        case c: Const =>
      }
    }

    bindVariable(form.form, form.variable)
  }

  def free = form.free
  def bound = variable :: form.bound
  def rename(variable: Var, renamed: Var) = if (variable == this.variable) Lambda(variable, varTpe, form.rename(variable, renamed)) else Lambda(this.variable, varTpe, form)
  override def toString = "(λ"+variable.toString+"."+form.toString +")"
}

object LambdaManipulations{

  def alphaVariants(left: Formula, right: Formula) = alphaVariantRoutine(left, right, Nil)

  def alphaVariantRoutine(form1: Formula, form2: Formula, renamings: List[(Var, Var)]): List[(Var, Var)] = {
    (form1, form2) match {
      case (Lambda(var1, type1, form1), Lambda(var2, type2, form2)) if (type1 == type2) => alphaVariantRoutine(form1, form2, (var1, var2) :: renamings)
      case (Apply(pred1, form1), Apply(pred2, form2)) => {
        if (pred1 != pred2) {
          alphaVariantRoutine(pred1, pred2, renamings)
          alphaVariantRoutine(form1, form2, renamings)
        } else {
          alphaVariantRoutine(form1, form2, renamings)
        }
      }
      case (a: Var, b: Var) => {
        if (a.name != b.name && !(getType(a) == getType(b) && renamings.exists({ case (x, y) => (a.name == x.name) && (a.name == y.name)}))) {
          Nil
        } else {
          renamings
        }
      }
      case (Const(name1, type1), Const(name2, type2)) => {
        if (name1 == name2 && type1 == type2) {
          renamings
        } else {
          Nil
        }
      }
      case (_, _) => Nil
    }
  }

  def areAlphaVariants(left: Formula, right: Formula) = alphaVariants(left, right).size > 0


  def substitute(sub : Formula, tosub : Var, formula : Formula) = {

    def subst(sub: Formula, tobesub: Var, form: Formula, bound: List[Var]): Formula = {
      form match {
        case Const(name, tp) => Const(name, tp)
        case variable : Var => {
          if (bound.exists(x => x.name == variable.name )) {
            variable
          } else if (tobesub.name == variable.name && variable.inftype == tobesub.inftype) {
            sub
          } else {
            variable
          }
        }
        case Apply(pred, formula) => {
          Apply(subst(sub, tobesub, pred, bound), subst(sub, tobesub, formula, bound))
        }
        case Lambda(variable, tpe, body) => {
          Lambda(variable, tpe, subst(sub, tobesub, body, bound))
        }
      }
    }

    var counter = 0
    def substituteRoutine(subs: Formula, toBeSub: Var, form: Formula): Formula = {
      if (subs.free.contains(toBeSub)) {
        val generated = Var("gen_" + counter)
        counter += 1
        val formula = form.rename(toBeSub, generated)
        subst(subs, generated, formula, formula.bound)
      } else
        subst(subs, toBeSub, form, form.bound)
    }

    substituteRoutine(sub, tosub, formula)
  }



  def getType(form: Formula): Type = {
    //returns the type of one formula
    def get(form: Formula): Type = {
      form match {
        case Lambda(variable, tpe, body) => {
          val bodyType = getType(body)
          Arrow(tpe,bodyType)
        }
        case v: Var  => {
          if(v.inftype == null){
            throw new Exception("Free Variables are not allowed!")
          }else{
            v.inftype
          }
        }
        case Const(name, tp) => tp
        case Apply(pred, body) => {
          val predType = getType(pred)
          val bodyType = getType(body)
          predType match {
            case Arrow(alpha, beta) if(alpha == bodyType) => beta
            case _ => throw new Exception("Ill-typed expression at "+ Apply(pred,body))
          }
        }
      }
    }

    get(form)
  }

  def betanf(form: Formula): Formula = {

    def betanfRoutine(form : Formula) : Formula = {
      //val formulaType = getType(form)

      form match {
        case Apply(predicate: Lambda, formula) => {
          betanfRoutine(substitute(formula, predicate.variable, predicate.form))
        }
        case Lambda(Var(x), tp, form) => {
          Lambda(Var(x), tp, betanfRoutine(form))
        }
        case t: Const => t
        case v: Var => v
      }
    }

    betanfRoutine(form)
  }

  def main(args : Array[String]) = {

//    in case you didn't go through all the code:
//    you can construct types of Arrow(E,Arrow(E,T)) by simply typing E->E->T, it takes care of right associativity
//    right associativity in scala is denoted by the symbol : in the end of the operator (->:)

    val lam1 = Lambda(Var("w"), E->: T->: E ,Lambda(Var("F"), E->: T, Lambda(Var("z"), E->:T->:E->:E, Var("w"))))
    val lam2 = Lambda(Var("x"), E, Lambda(Var("y"), T, Var("x"))) //E
    val expr = Apply(lam1,lam2)

    println(lam1.variable.inftype)
    println(expr)
    println(betanf(expr))
  }

}



