package main.scala.HigherOrder

import scala.collection.mutable


/**
 * Created by enxhi on 10/25/14.
 */

abstract class Type

abstract class Base extends Type

object E extends Base

object T extends Base

case class Arrow(left: Type, right: Type) extends Type


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
  var inftype: Type = null

  //  def checkVariableTypeMatch(variable : Var) = if(name == variable.name) tp == variable.tp else true
  def free = List(this)

  def bound = Nil

  def rename(variable: Var, renamed: Var) = if (variable == this) renamed else Var(name)

  override def toString = "V("+name+")"
}

case class Predicate(name: String, tpe: Type) {
  def checkVariableTypeMatch(variable: Var) = true

  def free = Nil

  def bound = Nil

  def rename(variable: Var, renamed: Var) = Predicate(name, tpe)

  override def toString = "P("+name+")"
}

case class Apply(pred: Formula, form: Formula) extends Formula {

  //  def checkVariableTypeMatch(variable : Var) = pred.checkVariableTypeMatch(variable) && form.checkVariableTypeMatch(variable)
  def free = form.free

  def bound = form.bound

  def rename(variable: Var, renamed: Var) = Apply(pred.rename(variable, renamed), form.rename(variable, renamed))

  override def toString = "("+pred.toString +")("+ form.toString +")"
}

//maybe removing the type from variable
case class Lambda(variable: Var, varTpe: Type, form: Formula) extends Formula {
  //  def checkVariableTypeMatch(vark : Var)= {
  //    if(variable.name == vark.name) (variable.tc == vark.tc) && form.checkVariableTypeMatch(vark) else form.checkVariableTypeMatch(vark)
  //  }
  def free = form.free

  def bound = variable :: form.bound

  def rename(variable: Var, renamed: Var) = if (variable == this.variable) Lambda(variable, varTpe, form.rename(variable, renamed)) else Lambda(this.variable, varTpe, form)

  override def toString = "(λ"+variable.toString+"."+form.toString +")"
}

object Functions {

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
        subst(subs, generated, formula, formula.bound diff List(toBeSub))
      } else
        subst(subs, toBeSub, form, form.bound diff List(toBeSub))
    }

    substituteRoutine(sub, tosub, formula)
  }


  def bindVariableType(form: Formula, types: mutable.HashMap[Var, Type]): Unit = {
    form match {
      case Apply(pred, formula) => {
        bindVariableType(pred, types)
        bindVariableType(formula, types)
      }
      case Lambda(variable, tpe, body) => {
        types(variable) = tpe
        bindVariableType(body, types)
      }
      case t: Var => {
        if (types contains t) {
          t.inftype = types(t)
        }
      }
      case _ =>
    }
  }

  def getType(form: Formula): Type = {
    bindVariableType(form, new mutable.HashMap[Var, Type]())

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
            case _ => throw new Exception("Ill-typed expression")
          }
        }
      }
    }

    get(form)
  }

  def betanf(form: Formula): Formula = {
    val formulaType = getType(form)
    form match {
      case Apply(predicate: Lambda, formula) => {
        betanf(substitute(formula, predicate.variable, predicate.form))
      }
      case e => e
    }
  }

}

object Main{
  def main(args : Array[String]) = {
    val expr = Apply(Lambda(Var("e"), Arrow(E, Arrow(T, E)), Lambda(Var("y"), Arrow(T, E), Apply(Var("y"),Apply(Const("e", Arrow(E,T)),Const("f", E))))), Const("k", Arrow(E, Arrow(T, E))))
    println(expr)
    println(Functions.betanf(expr))
  }
}



