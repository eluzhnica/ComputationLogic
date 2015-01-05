package main.scala.HigherOrder

import scala.collection.immutable
import scala.util.control.Breaks._
/**
 * Created by enxhi on 10/25/14.
 * This IS the version you should submit, not the GIT one
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
  def replace(variable : Var, formula : Formula) : Formula
  def bound: List[Var]
  def constants : List[Const]
  def rename(variable: Var, renamed: Var): Formula
}

case class Const(name: String, tp: Type) extends Formula {
  //  def checkVariableTypeMatch(variable : Var) = true
  def free = Nil
  def constants = List(this)
  def bound = Nil
  def replace(variable : Var, formula : Formula) = Const(name,tp)
  def rename(variable: Var, renamed: Var) = Const(name, tp)

  override def toString = "C(" + name +")"
}

case class Var(name: String, tpe : Type = null) extends Formula {

  //inferred type
  var inftype: Type = tpe
  def constants = Nil
  //  def checkVariableTypeMatch(variable : Var) = if(name == variable.name) tp == variable.tp else true
  def free = List(this)
  def getType = inftype
  def bound = Nil
  def replace(variable : Var, formula : Formula) = if(variable == this) formula else Var(name)
  def rename(variable: Var, renamed: Var) = if (variable == this) renamed else Var(name)

  override def toString = "V("+name+")"
}

case class Apply(pred: Formula, form: Formula) extends Formula {
  def constants = (pred.constants ::: form.constants).distinct
  def free = (form.free ::: pred.free).distinct
  def bound = (pred.bound ::: form.bound).distinct
  def replace(variable : Var, formula : Formula) = Apply(pred.replace(variable,formula), form.replace(variable,formula))
  def rename(variable: Var, renamed: Var) = Apply(pred.rename(variable, renamed), form.rename(variable, renamed))
  override def toString = "(" + pred.toString+"("+ form.toString + "))"
}

//maybe removing the type from variable
case class Lambda(variable: Var, varTpe: Type, form: Formula) extends Formula {
  variable.inftype = varTpe
  variableBind(this)

  //binds the head variable type
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
        case _ =>
      }
    }

    bindVariable(form.form, form.variable)
  }

  def constants = form.constants
  def free = form.free diff List(variable)
  def bound = variable :: form.bound
  def replace(variable : Var, formula : Formula) = Lambda(this.variable, varTpe, form.replace(variable,formula))
  def rename(variable: Var, renamed: Var) = {
    if (variable == this.variable)
      Lambda(renamed, varTpe, form.rename(variable, renamed))
    else
      Lambda(this.variable, varTpe, form.rename(variable,renamed))
  }
  override def toString = "λ"+variable.toString+"."+form.toString
}

case class Forall( form : Lambda) extends Formula{
  def constants = form.constants
  def free = form.free
  def bound = form.bound
  def replace(variable : Var, formula : Formula) = Forall(form.replace(variable, formula) match {case a : Lambda => a})
  def rename(variable: Var, renamed: Var) = Forall(form.rename(variable,renamed) match {case a: Lambda => a})
}
case class Exists(form : Lambda) extends Formula{
  def constants = form.constants
  def free = form.free
  def bound = form.bound
  def replace(variable : Var, formula : Formula) = Exists(form.replace(variable, formula) match {case a : Lambda => a})
  def rename(variable: Var, renamed: Var) = Exists(form.rename(variable,renamed) match {case a: Lambda => a})
}

case class Disj(l : Formula, r : Formula) extends Formula{
  def constants = l.constants ::: r.constants
  def free = l.free ::: r.free
  def bound = l.bound ::: r.bound
  def replace(variable : Var, formula : Formula) = Disj(l.replace(variable, formula), r.replace(variable, formula))
  def rename(variable: Var, renamed: Var) = Disj(l.rename(variable,renamed),r.rename(variable,renamed))
}

case class Conj(l : Formula, r : Formula) extends Formula{
  def constants = l.constants ::: r.constants
  def free = l.free ::: r.free
  def bound = l.bound ::: r.bound
  def replace(variable : Var, formula : Formula) = Conj(l.replace(variable, formula), r.replace(variable, formula))
  def rename(variable: Var, renamed: Var) = Conj(l.rename(variable,renamed),r.rename(variable,renamed))
}

case class Equal(l : Formula, r : Formula) extends Formula{
  def constants = l.constants ::: r.constants
  def free = l.free ::: r.free
  def bound = l.bound ::: r.bound
  def replace(variable : Var, formula : Formula) = Equal(l.replace(variable, formula), r.replace(variable, formula))
  def rename(variable: Var, renamed: Var) = Equal(l.rename(variable,renamed),r.rename(variable,renamed))
}

case class Neg(form : Formula) extends Formula{
  def constants = form.constants
  def free = form.free
  def bound = form.bound
  def replace(variable : Var, formula : Formula) = Neg(form.replace(variable, formula))
  def rename(variable: Var, renamed: Var) = Neg(form.rename(variable,renamed))
}



object LambdaManipulations {

  val rand = new scala.util.Random(System.currentTimeMillis())
  var generated: List[String] = Nil

  def alphaVariants(left: Formula, right: Formula) = alphaVariantRoutine(left, right, Nil)

  def alphaVariantRoutine(form1: Formula, form2: Formula, renamings: List[(Var, Var)]): List[(Var, Var)] = {
    (form1, form2) match {
      case (Lambda(var1, type1, form1), Lambda(var2, type2, form2)) if (type1 == type2) => {
        alphaVariantRoutine(form1, form2, (var1, var2) :: renamings)
      }
      case (Apply(pred1, form1), Apply(pred2, form2)) => {
        if (pred1 != pred2) {
          val renam = alphaVariantRoutine(pred1, pred2, renamings)

          if (renam != Nil) alphaVariantRoutine(form1, form2, renam)
          else Nil

        } else {
          alphaVariantRoutine(form1, form2, renamings)
        }
      }
      case (a: Var, b: Var) => {
        val alreadyRenamed = renamings.exists({
          case (x, y) => {
            val inOrder = ((a.name == x.name) && (b.name != y.name)) || ((a.name != x.name && b.name == y.name))
            val reversed = ((b.name == x.name) && (a.name != y.name)) || ((b.name != x.name && a.name == y.name))
            inOrder || reversed
          }
        })
        if (a.inftype != b.inftype || (a.name != b.name && alreadyRenamed)) {
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

  def areAlphaVariants(left: Formula, right: Formula) = alphaVariants(left, right) != Nil


  //note: I allow substitution of variables with a formula of different type. This is done on purpose
  // to allow this i can easily uncomment out condition check in the if clauses
  def substitute(sub: Formula, tosub: Var, formula: Formula) = {

    var counter = 0
    def subst(sub: Formula, tobesub: Var, form: Formula, bound: List[Var]): Formula = {
      form match {
        case Const(name, tp) => Const(name, tp)
        case variable: Var => {
          if (bound.exists(x => x.name == variable.name)) {
            variable
          } else if (tobesub.name == variable.name /*&& variable.inftype == tobesub.inftype*/ ) {
            sub
          } else {
            variable
          }
        }
        case Apply(pred, formula) => {
          Apply(subst(sub, tobesub, pred, bound), subst(sub, tobesub, formula, bound))
        }
        case Equal(left,right) =>{
          Equal(subst(sub,tobesub,left,bound), subst(sub,tobesub,right,bound))
        }
        case Forall(form) => {
          Forall(subst(sub,tobesub,form,bound) match {case a : Lambda => a})
        }
        case Exists(form) => {
          Exists(subst(sub,tobesub,form,bound) match {case a : Lambda => a})
        }
        case Lambda(variable, tpe, body) => {
          if (tobesub.name == variable.name /*&& variable.inftype == tobesub.inftype*/ ) {
            body //this was described in the hint of the problem
          } else if (sub.free.exists(v => variable.name == v.name /*&& v.inftype == variable.inftype*/)) {
            val newvar = Var(generateString(2) + counter)
            counter += 1
            newvar.inftype = variable.inftype
            val renamed = Lambda(variable, tpe, body).rename(variable, newvar)
            subst(sub, tobesub, renamed, newvar :: bound diff List(variable))
          } else {
            Lambda(variable, tpe, subst(sub, tobesub, body, bound))
          }
        }
        case Neg(form) =>{
          Neg(subst(sub,tobesub,form,bound))
        }
        case Conj(left,right) =>{
          Conj(subst(sub,tobesub,left,bound), subst(sub,tobesub,right,bound))
        }
        case Disj(left,right) =>{
          Disj(subst(sub,tobesub,left,bound), subst(sub,tobesub,right,bound))
        }
      }
    }



    def substituteRoutine(subs: Formula, toBeSub: Var, form: Formula): Formula = {
      subst(subs, toBeSub, form, Nil)
    }

    substituteRoutine(sub, tosub, formula)
  }


  def generateString(n: Int): String = {
    var res = rand.nextString(n)
    while (generated.contains(res)) {
      res = rand.nextString(n)
    }
    generated ::= res
    generated = generated.distinct
    res
  }


  //the TC function, I renamed it for readability issues
  def getType(form: Formula): Type = {
    //returns the type of one formula
    def get(form: Formula): Type = {
      form match {
        case Lambda(variable, tpe, body) => {
          val bodyType = getType(body)
          Arrow(tpe, bodyType)
        }
        case v: Var => {
          if (v.inftype == null) {
            throw new Exception("Free Variables are not allowed!")
          } else {
            v.inftype
          }
        }
        case Const(name, tp) => tp
        case Apply(pred, body) => {
          val predType = getType(pred)
          val bodyType = getType(body)
          predType match {
            case Arrow(alpha, beta) if (alpha == bodyType) => beta
            case _ => throw new Exception("Ill-typed expression at " + Apply(pred, body))
          }
        }
      }
    }

    get(form)
  }

  def betanf(form: Formula): Formula = {

    def betanfRoutine(form: Formula): Formula = {
      //val formulaType = getType(form)

      form match {
        case Apply(predicate: Lambda, formula) => {
          betanfRoutine(substitute(formula, predicate.variable, predicate.form))
        }
        case Apply(predicate, formula) => {
          Apply(betanfRoutine(predicate), betanfRoutine(formula))
        }
        case Lambda(v, tp, form1) => {
          Lambda(v, tp, betanfRoutine(form1))
        }
        case t: Const => t
        case v: Var => v
        case Forall(form) => {
          Forall(betanfRoutine(form) match { case a : Lambda => a})
        }
        case Exists(form) => {
          Exists(betanfRoutine(form) match { case a : Lambda => a})
        }
        case Equal(left,right) => {
          Equal(betanfRoutine(left), betanfRoutine(right))
        }
        case Neg(form) =>{
          Neg(betanfRoutine(form))
        }
        case Conj(left,right) =>{
          Conj(betanfRoutine(left), betanfRoutine(right))
        }
        case Disj(left,right) =>{
          Disj(betanfRoutine(left), betanfRoutine(right))
        }
      }
    }

    betanfRoutine(form)
  }

  def getDecomposeMatch(left: Formula, right: Formula): List[(Formula, Formula)] = (left, right) match {
    case (l: Var, r: Var) => {
      if (l.name == r.name) {
        Nil
      } else {
        null
      }
    }
    case (l: Const, r: Const) => {
      if (l == r) {
        Nil
      } else {
        null
      }
    }
    case (Apply(l1, r1), Apply(l2, r2)) => {
      val dec = getDecomposeMatch(l1, l2)
      if (dec == null) {
        return null
      } else {
        (r1, r2) :: dec
      }
    }
    case _ => null
  }

  /**
   *
   * @param left - left formula
   * @param right - right formula
   * @return last SIM step
   */
  def Simplification(left: Formula, right: Formula): List[(Formula, Formula)] = {

    var skolems: List[Const] = Nil

    def containsSkolems(tuples: List[(Formula, Formula)], consts: List[Const]): Boolean = {
      val constants = tuples.map({ case (left, right) => {
        (left.constants ::: right.constants).distinct
      }
      })

      constants.intersect(consts) != Nil
    }

    /**
     *
     * @param tobeUni - pairs to be unified (simplifed)
     * @param areWeDone - counts the number of circulations because of no case match
     * @return - the simplified pairs
     */
    def SIM(tobeUni: List[(Formula, Formula)], areWeDone: Integer): List[(Formula, Formula)] = {
      //if we circulated all the pairs without doing work then we're done
      if (areWeDone > tobeUni.size) {
        return tobeUni
      }

      tobeUni match {
        //make the substitutions in both pairs and recurse
        case (left: Lambda, right: Lambda) :: rest => {
          val skol = Const("sk_" + skolems.size, left.varTpe)
          skolems ::= skol
          val l = substitute(skol, left.variable, left.form)
          val r = substitute(skol, right.variable, right.form)

          SIM((r, l) :: rest, 0)
        }
        //use the eta rule
        case (left: Lambda, right: Formula) :: rest => {
          val skol = Const("sk_" + skolems.size, left.varTpe)
          skolems ::= skol
          val l = substitute(skol, left.variable, left.form)
          val r = Apply(right, skol)
          SIM((r, l) :: rest, 0)
        }
        //reuse the previous case
        case (left: Formula, right: Lambda) :: rest => {
          SIM((right, left) :: rest, 0)
        }
        //if the head of the applications match use the decompose case
        case (left: Apply, right: Apply) :: rest => {
          if (left.pred == right.pred) {
            SIM((left.form, right.form) :: rest, 0)
          } else {
            val matchingPairs = getDecomposeMatch(left, right)
            if (matchingPairs != null) {
              SIM(matchingPairs ::: rest, 0)
            } else {
              SIM(rest :+(left, right), areWeDone + 1)
            }
          }
        }
        case (left: Var, right) :: rest if (!right.free.exists(x => (x.name == left.name))) => {
          //do we have the case X = something (X) ?
          var modified = false

          //check the individual pairs
          val newrest = rest.map({
            case (x, y) => {

              if (!containsSkolems(List((x, y)), skolems) //do the contains skolem constants?
                && (x.free ::: y.free)
                .distinct
                .exists(x => (x.name == left.name)) // is there anything we can substitute, (is X in free(E))
              ) {
                modified = true
                (substitute(right, left, x), substitute(right, left, y))
              } else {
                (x, y)
              }

            }
          })

          // if nothing was substituted then increase the counter
          if (modified)
            SIM(newrest :+(left, right), 0)
          else
            SIM(newrest :+(left, right), areWeDone + 1)

        }
        case Nil => {
          tobeUni
        }
        // if none of the cases worked out, try to apply the rules on the rest
        // but remember how many times we did no work
        case a :: b => SIM(b ::: List(a), areWeDone + 1)
      }

    }

    SIM(List((left, right)), 0)
  }


  /**
   *
   * @param t
   * @return the return type of a type
   */
  private def getReturnType(t: Type): Type = {
    t match {
      case arrow: Arrow => getReturnType(arrow.right)
      case E => E
      case T => T
    }
  }


  /**
   *
   * @param value - the type of the head
   * @param formula - the already generated lambda expression
   * @param vars - variables used in the lambda expression where this is going to be applied to
   * @param avoid - variable names to avoid
   * @return Formula - the application arguments that are going to be applied to lambda expression
   */
  def gApplication(value: Type, formula: Formula, vars: List[Var], avoid: List[Var]): Formula = {

    //generates the block that is used inside H1,H2,.. (for instance H1XY)
    def generateOne(vars: List[Var], formula: Formula): Formula = {
      vars match {
        case head :: tail => {
          generateOne(tail, Apply(formula, head))
        }
        case Nil => formula
      }
    }

    def generateType(vars: List[Var]) : Type = vars match{
      case h::t if(t!= Nil) => h.tpe ->: generateType(t)
      case end => end.head.tpe
    }

    //keeps track of the indexes, used to label H_1xy H_2xy and so on
    var h_counter = 0

    // this generates the actual application arguments to the lambda expression
    def generateApplications(value: Type, retType : Type, varName: String, formula: Formula): Formula = {
      h_counter += 1
      value match {
        case Arrow(a, b) => {
          //if we are not at the end (return type) then we can go on and recurse
          if (!(b == E || b == T)) {
            generateApplications(b, retType, varName, Apply(formula, generateOne(vars, Var(varName + h_counter, retType ->: a))))
          } else {
            Apply(formula, generateOne(vars, Var(varName + h_counter, retType ->: a)))
          }
        }
      }
    }

    //made in China

    var name = generateString(1)
    val avoiding = vars ::: avoid
    while (avoiding.exists(x => (x.name.contains(name) || name.contains(x.name)))) {
      name = generateString(2)
    }


    generateApplications(value, generateType(vars), name, formula)
  }

  /**
   *
   * @param value - the alpha type
   * @param vars - variables to avoid
   * @param application - application to be used, usually the given head of gBinding
   * @return lambdaExpression.head
   */
  def gLambda(value: Type, vars: List[Var], application: Formula): Formula = {

    var counter = 0

    def generateLambdas(value: Type, variableName: String, appl: Formula): Formula = {
      value match {
        case Arrow(a, b) => {
          counter += 1
          Lambda(Var(variableName + counter, a), a, generateLambdas(b, variableName, appl))
        }
        case E | T => {
          appl
        }
      }
    }


    //here we go Sir, expect something made in China
    var name = generateString(1)
    while (vars.exists(x => (x.name.contains(name)|| name.contains(x.name)))) {
      name = generateString(1)
    }

    generateLambdas(value, name, application)
  }

  /**
   *
   * @param formula - base lambda expression, instance Lambda(x,_,Lambda(y,_,Var(Head))
   * @param value - variable to be substituted instead of head
   * @return projection
   */
  def gProjections(formula: Formula, value: Var): Formula = {
    formula match {
      case Lambda(v, t, form) => {
        Lambda(v, t, gProjections(form, value))
      }
      case v: Var => value
      case _ => throw new Error("Malformed base lambda")
    }
  }

  def getHead(formula: Formula): Var = formula match {
    case Lambda(v, t, form) => {
      getHead(form)
    }
    case hd: Var => hd
    case _ => throw new Error("Not a proper lambda passed!")
  }

  /**
   *
   * @param head - the head of the general binder
   * @param tpe - the type of the to be generated general binder
   * @param avoid - variables to avoid
   * @return  general binder + projections
   */
  def gbinding(head: Var, tpe: Type, avoid: List[Var]): List[Formula] = {
    //if the return types don't match there is noway to generate anything correct or if the type is base type
    if (getReturnType(head.inftype) != getReturnType(tpe) || tpe == E || tpe == T) {
      return null
    }

    var application: Formula = head

    //avoid the head, don't capture it
    var formula: Formula = gLambda(tpe, head :: avoid, application)

    if (!(head.inftype == E || head.inftype == T)) {
      application = gApplication(head.inftype, head, formula.bound, head :: avoid)
    }

    formula = formula.replace(head, application)

    val headReturnType = getReturnType(head.inftype)

    //projections without the applications part
    //generate projections for which the variable type matches with the return type that head has

    var projections: List[Formula] = Nil
    formula.bound.foreach(variable => {
      if (variable.inftype != headReturnType) {}
      else if (variable.inftype == E || variable.inftype == T) {
        projections ::= formula.rename(head, variable)
      } else {
        val tempAppl = gApplication(head.inftype, variable, formula.bound, avoid)
        projections ::= formula.replace(variable, tempAppl)
      }
    }) //we don't need to avoid the head


    //if the head indicates that it takes parameters then we go and generate them


    formula :: projections
  }



  def betanfRecursive(formula: Formula): Formula = {
    var last = formula
    while (last != betanf(last)) {
      last = betanf(last)
    }
    last
  }

  def higherOrderUnification(left: Formula, right: Formula): List[(Var, Formula)] = {

      var skolems: List[Const] = Nil

      def containsSkolems(tuples: List[(Formula, Formula)], consts: List[Const]): Boolean = {
        val constants = tuples.map({ case (left, right) => {
          (left.constants ::: right.constants).distinct
        }
        })

        constants.intersect(consts) != Nil
      }


      def elimConditionCheck(tuples: List[(Formula, Formula)], skolems: List[Const]): Boolean = {
        tuples match {
          case (left: Var, right: Formula) :: rest => {
            return !right.free.contains(left) && !containsSkolems((Var("test"), right) :: Nil, skolems) && rest.flatMap({ case (x, y) => x.free ::: y.free}).contains(left)
          }
          case _ => false
        }
      }

      def getApplicationHead(apply: Formula): Formula = apply match {
        case Apply(l, r) => {
          getApplicationHead(l)
        }
        case t: Var => t
        case t: Const => t
        case _ => null
      }


      /**
       *
       * @param tobeUni - pairs to be unified (simplifed)
       * @param areWeDone - counts the number of circulations because of no case match
       * @return - the simplified pairs
       */
      def SIM(tobeUni: List[(Formula, Formula)], areWeDone: Integer, binderacc: List[(Var, Formula)]): List[(Var, Formula)] = {
        //if we circulated all the pairs without doing work then we're done, it's unified

        val newUni = tobeUni.filterNot({
          case (x: Var, y: Var) => (x == y)
          case _ => false
        })

        val vars = newUni.collect({
          case (x: Var, y) => x
          case (y, x: Var) => x
        })

        //are all the pairs distinct on variable part and are all the pairs x =? smth and smth doesnt contain skolems or x
        if (newUni == Nil || (vars.distinct.size == vars.size && newUni.forall({
          case (x: Var, y: Formula) => !y.free.contains(x) && y.constants.intersect(skolems) == Nil
          case (y: Formula, x: Var) => !y.free.contains(x) && y.constants.intersect(skolems) == Nil
          case (c1 : Const , c2 : Const ) => true
          case _ => false
        }))) {
          val newBinderacc: List[(Var, Formula)] = binderacc.flatMap({case(x,y) => newUni.collect({
            case(v : Var,s) => (x,substitute(s,v,y))
            case(s,v:Var) => (x,substitute(s,v,y))
          })})
          if(newUni == Nil){
            return binderacc
          }
          return newBinderacc
        }

        if (areWeDone - 2 > tobeUni.size) {

          //collect all the variables that unify to smth
          //        val varToVar : List[(Var,Formula)] = tobeUni.collect({
          //          case(x:Var,y:Var) => (x,y)
          //        })
//          println(binderacc)
//          println(newUni)
//          println()
          return /*varToVar :: binderacc*/ null
        }

        tobeUni match {
          //make the substitutions in both pairs and recurse
          case (left: Lambda, right: Lambda) :: rest => {
            val skol = Const("sk_" + skolems.size, left.varTpe)
            skolems ::= skol
            val l = substitute(skol, left.variable, left.form)
            val r = substitute(skol, right.variable, right.form)

            SIM((r, l) :: rest, 0, binderacc.distinct)
          }
          //use the eta rule
          case (left: Lambda, right: Formula) :: rest => {
            val skol = Const("sk_" + skolems.size, left.varTpe)
            skolems ::= skol
            val l = substitute(skol, left.variable, left.form)
            val r = Apply(right, skol)
            SIM((r, l) :: rest, 0, binderacc.distinct)
          }
          //reuse the previous case
          case (left: Formula, right: Lambda) :: rest => {
            SIM((right, left) :: rest, 0, binderacc)
          }
          //if the head of the applications match use the decompose case
          case (left: Apply, right: Apply) :: rest if (left.pred == right.pred) => {

            SIM((left.form, right.form) :: rest, 0, binderacc.distinct)

          }

          case (left: Var, right) :: rest if (elimConditionCheck((left, right) :: rest, skolems)) => {
            //x = x ? or the regular check
            if (left == right) {
              return SIM(rest, areWeDone + 1, binderacc) //note that this would return Nil if there is nothing there, which is not a FAIL return.
            }

            var modified = false

            //the rest is SIM stuff
            //check the individual pairs
            val newrest = rest.map({
              case (x, y) => {

                if (!containsSkolems(List((x, y)), skolems) //do they contains skolem constants?
                  && (x.free ::: y.free)
                  .distinct
                  .exists(x => (x.name == left.name)) // is there anything we can substitute, (is X in free(E))
                ) {
                  modified = true
                  (substitute(right, left, x), substitute(right, left, y))
                } else {
                  (x, y)
                }

              }
            })

            // if nothing was substituted then increase the counter
            if (modified)
              SIM(newrest :+(left, right), 0, binderacc.distinct)
            else
              SIM(newrest :+(left, right), areWeDone + 1, binderacc.distinct)

          }
          case (left: Apply, right) :: rest => {
            //check if the decomposition matches on head
            val matchingPairs = getDecomposeMatch(left, right)
            if (matchingPairs != null) {
              SIM(matchingPairs ::: rest, 0, binderacc)
            } else {

              val leftHead = getApplicationHead(left)
              val rightHead = getApplicationHead(right)

              //if there is no proper construction of nested applications I will get null
              if (leftHead != null && rightHead != null) {

                (leftHead, rightHead) match {
                  case (l: Var, r: Const) =>

                    if (l.inftype == null || r.tp == null) {
                      throw new Error("Variables have to be strongly typed!")
                    }
                    val binders = gbinding(Var(r.name, r.tp), l.inftype, Nil)
//                    println(binders)

                    //for each binder recursively get the substitutions (binders) in lower level
                    //apply the substitutions to the binder from which they were generated
                    //check if we HAVE TO unify other pairs, if not return the substitutions(binders) up in the tree
                    //the reason I am using a list of lists is that one binder can have multiple substitutions to be made in order to solve it
                    //in other words in that binder we generated more than one variable


                    //if there are no binders that can be generated then it can't be unified. return null for failure
                    // we don't care if there is something in the rest because if there is, it is an AND branch.


                    if (binders == null || binders.size == 0) {
                      null
                    } else {
                      var result: List[(Var, Formula)] = Nil

                      binders.foreach(binder => {
                        val newleft: Formula = betanfRecursive(substitute(binder, l, left))

                        var newBinderacc : List[(Var,Formula)] = Nil
                        if(binderacc != Nil) {
                          // NOTE THIS PART OF SUBSTITUTION AND BETA REDUCTION CAUSES THE PROBLEMS. 2 MORE hours and i can fix it
                          newBinderacc = binderacc.map({ case (v, f) => (v, betanfRecursive(substitute(binder, l, f)))})
                        }else{
                          newBinderacc = List(l -> binder)
                        }
                        //find the substitutions by replacing them recursively
                        val res: List[(Var, Formula)] = SIM(((newleft, right) :: rest).distinct, 0, newBinderacc.distinct)

                        //did it fail?
                        //we also need to check if it returned Nil
                        if (res != null) {
                          result :::= res
                        }
                      })

                      result.distinct
                    }
                  case (l: Var, r: Var) => {

                    if (l.inftype == null || r.inftype == null) {
                      throw new Error("Variables have to be strongly typed!")
                    }
                    val binders = gbinding(Var(r.name, r.inftype), l.inftype, Nil)

                    //for each binder recursively get the substitutions (binders) in lower level
                    //apply the substitutions to the binder from which they were generated
                    //check if we HAVE TO unify other pairs, if not return the substitutions(binders) up in the tree
                    //the reason I am using a list of lists is that one binder can have multiple substitutions to be made in order to solve it
                    //in other words in that binder we generated more than one variable


                    //if there are no binders that can be generated then it can't be unified. return null for failure
                    // we don't care if there is something in the rest because if there is, it is an AND branch.

//                    println(binders)

                    if (binders == null || binders.size == 0) {
                      null
                    } else {
                      var result: List[(Var, Formula)] = Nil

                      binders.foreach(binder => {
                        val newleft: Formula = betanfRecursive(substitute(binder, l, left))

                        var newBinderacc : List[(Var,Formula)] = Nil
                        if(binderacc != Nil) {

                          // NOTE THIS PART OF SUBSTITUTION AND BETA REDUCTION CAUSES THE PROBLEMS. 2 MORE hours and i can fix it
                          newBinderacc = binderacc.map({ case (v, f) => (v, betanfRecursive(substitute(binder, l, f)))})
                        }else{
                          newBinderacc = List(l -> binder)
                        }
                        //find the substitutions by replacing them recursively
                        val res: List[(Var, Formula)] = SIM(((newleft, right) :: rest).distinct, 0, newBinderacc.distinct)

                        //did it fail?
                        //we also need to check if it returned Nil
                        if (res != null) {
                          result :::= res
                        }
                      })

                      result.distinct
                    }
                  }
                  case _ => SIM((right, left) :: rest, areWeDone + 1, binderacc.distinct)
                }
              } else {
                SIM(rest :+(left, right), areWeDone + 1, binderacc.distinct)
              }
            }
          }
          case (left, right: Apply) :: rest => {
            SIM((right, left) :: rest, areWeDone, binderacc.distinct)
          }
          // if none of the cases worked out, try to apply the rules on the rest
          // but remember how many times we did no work
          case a :: b => SIM(b ::: List(a), areWeDone + 1, binderacc.distinct)
          case Nil => {
            Nil
          }
        }

      }


      SIM(List((left, right)), 0, Nil)
    }

  /**
   *
   * @param left
   * @param right
   * @return for now let it stay like this, return a pair of unifiers and the flexflex pairs. I'll see how i will need it and adopt it then.
   */
  def pre_unification(left: Formula, right: Formula): (List[(Var, Formula)],List[(Formula,Formula)]) = {

    var skolems: List[Const] = Nil

    def containsSkolems(tuples: List[(Formula, Formula)], consts: List[Const]): Boolean = {
      val constants = tuples.map({ case (left, right) => {
        (left.constants ::: right.constants).distinct
      }
      })

      constants.intersect(consts) != Nil
    }

    def elimConditionCheck(tuples: List[(Formula, Formula)], skolems: List[Const]): Boolean = {
      tuples match {
        case (left: Var, right: Formula) :: rest => {
          return !right.free.contains(left) && !containsSkolems((Var("test"), right) :: Nil, skolems) && rest.flatMap({ case (x, y) => x.free ::: y.free}).contains(left)
        }
        case _ => false
      }
    }

    def getApplicationHead(apply: Formula): Formula = apply match {
      case Apply(l, r) => {
        getApplicationHead(l)
      }
      case t: Var => t
      case t: Const => t
      case _ => null
    }


    /**
     *
     * @param tobeUni - pairs to be unified (simplifed)
     * @param areWeDone - counts the number of circulations because of no case match
     * @return - the simplified pairs
     */
    def SIM(tobeUni: List[(Formula, Formula)], areWeDone: Integer, binderacc: List[(Var, Formula)], ff : List[(Formula,Formula)]): (List[(Var, Formula)],List[(Formula,Formula)]) = {
      //if we circulated all the pairs without doing work then we're done, it's unified

      val newUni = tobeUni.filterNot({
        case (x: Var, y: Var) => (x == y)
        case _ => false
      })

      val vars = newUni.collect({
        case (x: Var, y) => x
        case (y, x: Var) => x
      })

      //are all the pairs distinct on variable part and are all the pairs x =? smth and smth doesnt contain skolems or x
      if (newUni == Nil || (vars.size == newUni.size && vars.distinct.size == vars.size && newUni.forall({
        case (x: Var, y: Formula) => !y.free.contains(x) && y.constants.intersect(skolems) == Nil
        case (y: Formula, x: Var) => !y.free.contains(x) && y.constants.intersect(skolems) == Nil
      }))) {
        return binderacc -> ff
      }

      if (areWeDone - 2 > tobeUni.size) {

        //collect all the variables that unify to smth
        //        val varToVar : List[(Var,Formula)] = tobeUni.collect({
        //          case(x:Var,y:Var) => (x,y)
        //        })
        return /*varToVar :: binderacc*/ null
      }

      tobeUni match {
        //make the substitutions in both pairs and recurse
        case (left: Lambda, right: Lambda) :: rest => {
          val skol = Const("sk_" + skolems.size, left.varTpe)
          skolems ::= skol
          val l = substitute(skol, left.variable, left.form)
          val r = substitute(skol, right.variable, right.form)

          SIM((r, l) :: rest, 0, binderacc,ff)
        }
        //use the eta rule
        case (left: Lambda, right: Formula) :: rest => {
          val skol = Const("sk_" + skolems.size, left.varTpe)
          skolems ::= skol
          val l = substitute(skol, left.variable, left.form)
          val r = Apply(right, skol)
          SIM((r, l) :: rest, 0, binderacc,ff)
        }
        //reuse the previous case
        case (left: Formula, right: Lambda) :: rest => {
          SIM((right, left) :: rest, 0, binderacc,ff)
        }
        //if the head of the applications match use the decompose case
        case (left: Apply, right: Apply) :: rest if (left.pred == right.pred) => {
          SIM((left.form, right.form) :: rest, 0, binderacc, ff)
        }

        case (left: Var, right) :: rest if (elimConditionCheck((left, right) :: rest, skolems)) => {
          //x = x ? or the regular check
          if (left == right) {
            return SIM(rest, areWeDone + 1, binderacc, ff) //note that this would return Nil if there is nothing there, which is not a FAIL return.
          }

          var modified = false

          //the rest is SIM stuff
          //check the individual pairs
          val newrest = rest.map({
            case (x, y) => {

              if (!containsSkolems(List((x, y)), skolems) //do they contains skolem constants?
                && (x.free ::: y.free)
                .distinct
                .exists(x => (x.name == left.name)) // is there anything we can substitute, (is X in free(E))
              ) {
                modified = true
                (substitute(right, left, x), substitute(right, left, y))
              } else {
                (x, y)
              }

            }
          })

          // if nothing was substituted then increase the counter
          if (modified)
            SIM(newrest :+(left, right), 0, binderacc, ff)
          else
            SIM(newrest :+(left, right), areWeDone + 1, binderacc, ff)

        }
        case (left: Apply, right) :: rest => {
          //check if the decomposition matches on head
          val matchingPairs = getDecomposeMatch(left, right)
          if (matchingPairs != null) {
            SIM(matchingPairs ::: rest, 0, binderacc, ff)
          } else {

            val leftHead = getApplicationHead(left)
            val rightHead = getApplicationHead(right)

            //if there is no proper construction of nested applications I will get null
            if (leftHead != null && rightHead != null) {

              (leftHead, rightHead) match {
                case (l: Var, r: Const) =>

                  if (l.inftype == null || r.tp == null) {
                    throw new Error("Variables have to be strongly typed!")
                  }
                  val binders = gbinding(Var(r.name, r.tp), l.inftype, Nil)

                  //for each binder recursively get the substitutions (binders) in lower level
                  //apply the substitutions to the binder from which they were generated
                  //check if we HAVE TO unify other pairs, if not return the substitutions(binders) up in the tree
                  //the reason I am using a list of lists is that one binder can have multiple substitutions to be made in order to solve it
                  //in other words in that binder we generated more than one variable


                  //if there are no binders that can be generated then it can't be unified. return null for failure
                  // we don't care if there is something in the rest because if there is, it is an AND branch.


                  if (binders == null || binders.size == 0) {
                    null
                  } else {
                    var result: (List[(Var, Formula)],List[(Formula,Formula)]) = Nil -> Nil

                    binders.foreach(binder => {
                      val newleft: Formula = betanfRecursive(substitute(binder, l, left))

                      var newBinderacc : List[(Var,Formula)] = Nil
                      if(binderacc != Nil) {
                        newBinderacc = binderacc.map({ case (v, f) => (v, betanfRecursive(substitute(binder, l, f)))})
                      }else{
                        newBinderacc = List(l -> binder)
                      }
                      //find the substitutions by replacing them recursively
                      val res = SIM((newleft, right) :: rest, 0, newBinderacc, ff)

                      //did it fail?
                      //we also need to check if it returned Nil
                      if (res != null) {
                        result = (result._1 ::: res._1, result._2 ::: res._2)
                      }
                    })

                    result
                  }
                case (l: Var, r: Var) => {
                  SIM(rest,0,binderacc,(left,right)::ff)
                }
                case _ => SIM((right, left) :: rest, areWeDone + 1, binderacc, ff)
              }
            } else {
              SIM(rest :+(left, right), areWeDone + 1, binderacc, ff)
            }
          }
        }
        case (left, right: Apply) :: rest => {
          SIM((right, left) :: rest, areWeDone, binderacc, ff)
        }
        // if none of the cases worked out, try to apply the rules on the rest
        // but remember how many times we did no work
        case a :: b => SIM(b ::: List(a), areWeDone + 1, binderacc, ff)
        case Nil => {
          (Nil,Nil)
        }
      }

    }


    SIM(List((left, right)), 0, Nil, Nil)
  }

    abstract class ArithExp {
      def toNum: Int
    }

    case class Plus(left: ArithExp, right: ArithExp) extends ArithExp {
      def toNum = left.toNum + right.toNum
    }
    case class Times(left: ArithExp, right: ArithExp) extends ArithExp {
      def toNum = left.toNum * right.toNum
    }
    case class Exp(base: ArithExp, exp: ArithExp) extends ArithExp {
      def toNum = math.pow(base.toNum.toDouble, exp.toNum.toDouble).toInt
    }
    case class Num(n: Int) extends ArithExp {
      def toNum = n
    }
    case class Minus(left: ArithExp, right: ArithExp) extends ArithExp {
      def toNum = left.toNum - right.toNum
    }
    case class Div(nom: ArithExp, denom: ArithExp) extends ArithExp {
      def toNum = nom.toNum + denom.toNum
    }
    case class Mod(num: ArithExp, mod: ArithExp) extends ArithExp {
      def toNum = num.toNum + mod.toNum
    }
    case class Root(num: ArithExp, root: ArithExp) extends ArithExp {
      def toNum = num.toNum + root.toNum
    }


    def generatePlus(n: Formula, m: Formula) = {

      val n1 = Var(generateString(2))
      val m1 = Var(generateString(2))
      val s = Var(generateString(1))
      val o = Var(generateString(1))


      val baseLambda = Lambda(n1, (E ->: E) ->: E ->: E, Lambda(m1, (E ->: E) ->: E ->: E,
        Lambda(s, E ->: E, Lambda(o, E, Apply(Apply(n1, s), Apply(Apply(m1, s), o))))))

      Apply(Apply(baseLambda, n), m)
    }

    def generateTimes(n: Formula, m: Formula): Formula = {

      val n1 = Var(generateString(2))
      val m1 = Var(generateString(2))
      val s = Var(generateString(1), E ->: E)
      val o = Var(generateString(1), E)

      val baseLambda = Lambda(n1, (E ->: E) ->: E ->: E, Lambda(m1, (E ->: E) ->: E ->: E,
        Lambda(s, E ->: E, Lambda(o, E, Apply(n1, Apply(m1, s))))))

      Apply(Apply(baseLambda, n), m)
    }

    def generateExp(n: Formula, m: Formula): Formula = {
      val n1 = Var(generateString(2))
      val m1 = Var(generateString(2))

      val baseLambda = Lambda(n1, (E ->: E) ->: E ->: E, Lambda(m1, (E ->: E) ->: E ->: E, Apply(m1, n1)))

      Apply(Apply(baseLambda, n), m)
    }

    def generateMinus(n: Formula, m: Formula): Formula = {
      val x = Var(generateString(2))
      val left = generatePlus(m, x)
      val right = n

      Equal(left, right)
    }


    def generateDiv(n: Formula, m: Formula): Formula = {
      val x = Var(generateString(2))
      val left = generateTimes(m, x)
      val right = n

      Equal(left, right)

    }


    def generateRoot(n: Formula, m: Formula): Formula = {
      val x = Var(generateString(2))
      val left = generateExp(x, m)
      val right = n

      Equal(left, right)
    }

    def churchexp(exp: ArithExp): Formula = {

      if (exp.toNum < 0) {
        throw new Error("Negative numbers cannot be evaluated")
      }
      exp match {
        case Num(n: Int) => churchnum(n)
        case Plus(a, b) => {
          val n = churchexp(a)
          val m = churchexp(b)
          generatePlus(n, m)
        }
        case Times(a, b) => {
          val n = churchexp(a)
          val m = churchexp(b)
          generateTimes(n, m)
        }
        case Exp(a, b) => {
          val n = churchexp(a)
          val m = churchexp(b)
          generateExp(n, m)
        }
        case Minus(a, b) => {
          val n = churchexp(a)
          val m = churchexp(b)
          generateMinus(n, m)
        }
        case Div(a, b) => {
          val n = churchexp(a)
          val m = churchexp(b)
          generateDiv(n, m)
        }
        case Mod(a, b) => {
          val n = churchexp(a)
          val m = churchexp(b)
          churchexp(Minus(a, Times(Div(a, b), b)))
        }
        case Root(a, b) => {
          val n = churchexp(a)
          val m = churchexp(b)
          generateRoot(n, m)
        }
      }
    }


    def churchnum(num: Int): Formula   = {

      def successors(n: Int): Formula = {
        if (n == 0) {
          Var("O", E)
        } else {
          Apply(Var("S", E ->: E), successors(n - 1))
        }
      }
      Lambda(Var("S", E ->: E), E ->: E, Lambda(Var("O", E), E, successors(num)))
    }


    def churchtono(numeral: Formula): Int = {

      def churchtonoHelper(numeral: Formula): Int = numeral match {
        case t: Lambda => churchtonoHelper(t.form)
        case t: Apply => 1 + churchtonoHelper(t.form)
        case t: Var => 0
        case _ => throw new Error("Malformed numeral")
      }
      //    numeral match {
      //      case Lambda(t: Var, Arrow(alpha1, alpha2), Lambda(s: Var, alpha, f)) if (alpha1 == alpha2) => churchtonoHelper(numeral)
      //      case _ => throw new Error("Malformed numeral")
      //    }

      churchtonoHelper(numeral)
    }


    def normalize(form: Formula): Formula = {

      def betanfRoutine(form: Formula): Formula = {
        //val formulaType = getType(form)

        form match {
          case Apply(predicate: Lambda, formula) => {
            betanfRoutine(substitute(formula, predicate.variable, predicate.form))
          }
          case Apply(predicate, formula) => {
            Apply(betanfRoutine(predicate), betanfRoutine(formula))
          }
          case Lambda(v, tp, form1) => {
            Lambda(v, tp, betanfRoutine(form1))
          }
          case Equal(l, r) => {
            val solved = higherOrderUnification(l, r)
            var result: Formula = l
            if (solved.length == 0) {
              throw new Error("Error during unification")
            }
            solved.foreach({
              case (x: Var, y) => result = substitute(y, x, result)
              case _ => throw new Error("Error during unification")
            })
            result
          }
          case t: Const => t
          case v: Var => v
        }
      }

      betanfRoutine(form)
    }


    def ellipsis() = {
      val love = Apply(Apply(Var("love", Arrow(E, Arrow(E, E))), Const("peter", E)), Apply(Var("wife_of", Arrow(E, E)), Const("peter", E)))
      val peter = Apply(Var("P", E ->: E), Const("Peter", E))
      val john = Apply(Var("P", E ->: E), Const("John", E))

      val unifiers = higherOrderUnification(john, love)
      if (unifiers.length < 1) {
        throw new Error("Error during unification")
      }

      println(unifiers)
      println(unifiers.size)
      unifiers.foreach({case(x,y) => println((substitute(y,x,john)))})
    }

    //betanf doesn't work properly
    def churcheval(formula: Formula) = {

      var last = normalize(formula)
      while (last != normalize(last)) {
        last = normalize(last)
      }
      last
    }



  def getApplicationHead(apply: Formula): Formula = apply match {
    case Apply(l, r) => {
      getApplicationHead(l)
    }
    case t: Var => t
    case t: Const => t
    case _ => null
  }


  def generate_var(tpe : Type) : Var = {
    //to be impl
    return Var(generateString(2),tpe)

  }

  def generate_sk(formula : Lambda) : Formula = {
    //to be
    val free = formula.free
    var result : Formula = Const(generateString(2),formula.varTpe)

    free.foreach(x => result = Apply(result, generate_var(x.tpe)))
    result
  }



  /**
   *
   * @param formula
   * @return true - if something can be made true else false.
   */
  def higherOrderProver(formula : Formula): Boolean = {

    var skolems: List[Const] = Nil

    def containsSkolems(tuples: List[(Formula, Formula)], consts: List[Const]): Boolean = {
      val constants = tuples.map({ case (left, right) => {
        (left.constants ::: right.constants).distinct
      }
      })

      constants.intersect(consts) != Nil
    }


    def elimConditionCheck(tuples: List[(Formula, Formula)], skolems: List[Const]): Boolean = {
      tuples match {
        case (left: Var, right: Formula) :: rest => {
          return !right.free.contains(left) && !containsSkolems((Var("test"), right) :: Nil, skolems) && rest.flatMap({ case (x, y) => x.free ::: y.free}).contains(left)
        }
        case _ => false
      }
    }

    def getApplicationHead(apply: Formula): Formula = apply match {
      case Apply(l, r) => {
        getApplicationHead(l)
      }
      case t: Var => t
      case t: Const => t
      case _ => null
    }


    /**
     * Most of the parts here are reused from HOU. The only changes are ORing the cases rather than ANDing in ff fr and in the new Equal case.
     *
     * @param tobeUni - pairs to be unified (simplifed)
     * @param areWeDone - counts the number of circulations because of no case match
     * @return - the simplified pairs
     */

    def SIM(tobeUni: List[(Formula, Formula)], areWeDone: Integer, binderacc: List[(Var, Formula)], isRecursingBack : Boolean): List[(Var, Formula)] = {
      // REUSED FROM HOU
      val newUni = tobeUni.filterNot({
        case (x: Var, y: Var) => (x == y)
        case _ => false
      })

      val vars = newUni.collect({
        case (x: Var, y) => x
        case (y, x: Var) => x
      })

      //are all the pairs distinct on variable part and are all the pairs x =? smth and smth doesnt contain skolems or x
      if (newUni == Nil || (vars.distinct.size == vars.size && newUni.forall({
        case (x: Var, y: Formula) => !y.free.contains(x) && y.constants.intersect(skolems) == Nil
        case (y: Formula, x: Var) => !y.free.contains(x) && y.constants.intersect(skolems) == Nil
        case (c1 : Const , c2 : Const ) => true
        case _ => false
      }))) {
        val newBinderacc: List[(Var, Formula)] = binderacc.flatMap({case(x,y) => newUni.collect({
          case(v : Var,s) => (x,substitute(s,v,y))
          case(s,v:Var) => (x,substitute(s,v,y))
        })})
        if(newUni == Nil){
          return binderacc
        }
        return newBinderacc
      }


      //CHANGED FROM HOU. RECURSING BACK RULE TO ELIMINATE NEG(NEG(B)) = B kind of terms.
      if (areWeDone - 2 > tobeUni.size) {
        if(isRecursingBack){
          return null
        }

        val pairs1 = tobeUni.flatMap({
          case (left,right) => produce_pairs((left,true), Nil, true) ::: produce_pairs((right,false), Nil, true)
        })

        val pairs2 = tobeUni.flatMap({
          case (left,right) => produce_pairs((left,false), Nil, true) ::: produce_pairs((right,true), Nil, true)
        })

        val result1 = cut_branches(pairs1, Nil, true)
        val result2 = cut_branches(pairs2, Nil, true)

        if(result1 && result2){
           Nil
        }else{
          null
        }
      }


      tobeUni match {
        //make the substitutions in both pairs and recurse
        case (left: Lambda, right: Lambda) :: rest => {
          val skol = Const("sk_" + skolems.size, left.varTpe)
          skolems ::= skol
          val l = substitute(skol, left.variable, left.form)
          val r = substitute(skol, right.variable, right.form)

          SIM((r, l) :: rest, 0, binderacc.distinct, isRecursingBack)
        }
        //use the eta rule
        case (left: Lambda, right: Formula) :: rest => {
          val skol = Const("sk_" + skolems.size, left.varTpe)
          skolems ::= skol
          val l = substitute(skol, left.variable, left.form)
          val r = Apply(right, skol)
          SIM((r, l) :: rest, 0, binderacc.distinct, isRecursingBack)
        }
        //reuse the previous case
        case (left: Formula, right: Lambda) :: rest => {
          SIM((right, left) :: rest, 0, binderacc, isRecursingBack)
        }
        //if the head of the applications match use the decompose case
        case (left: Apply, right: Apply) :: rest if (left.pred == right.pred) => {

          SIM((left.form, right.form) :: rest, 0, binderacc.distinct, isRecursingBack)

        }

        case (left: Var, right) :: rest if (elimConditionCheck((left, right) :: rest, skolems)) => {
          //x = x ? or the regular check
          if (left == right) {
            return SIM(rest, areWeDone + 1, binderacc, isRecursingBack) //note that this would return Nil if there is nothing there, which is not a FAIL return.
          }

          var modified = false

          //the rest is SIM stuff
          //check the individual pairs
          val newrest = rest.map({
            case (x, y) => {

              if (!containsSkolems(List((x, y)), skolems) //do they contains skolem constants?
                && (x.free ::: y.free)
                .distinct
                .exists(x => (x.name == left.name)) // is there anything we can substitute, (is X in free(E))
              ) {
                modified = true
                (substitute(right, left, x), substitute(right, left, y))
              } else {
                (x, y)
              }

            }
          })

          // if nothing was substituted then increase the counter
          if (modified)
            SIM(newrest :+(left, right), 0, binderacc.distinct, isRecursingBack)
          else
            SIM(newrest :+(left, right), areWeDone + 1, binderacc.distinct, isRecursingBack)

        }
        case (left: Apply, right) :: rest => {
          //check if the decomposition matches on head
          val matchingPairs: List[(Formula, Formula)] = getDecomposeMatch(left, right)
          var result : List[(Var, Formula)] = Nil
          if (matchingPairs != null) {
            var partial_result : List[(Var,Formula)] = null

            for(pair <- matchingPairs){
              var subs_pair = pair

              //try to substitute whatever resolved in another branch.
              if(partial_result != null){
                partial_result.foreach(x => {
                  subs_pair = (pair._1.replace(x._1, x._2), pair._2.replace(x._1, x._2))
                })
              }

              partial_result = SIM(List(subs_pair),0,binderacc, isRecursingBack)

              if(partial_result == null){
                return null
              }else{
                result :::= partial_result
              }
            }

            if(result == Nil) null else result

          } else {

            //REUSED FROM HOU
            val leftHead = getApplicationHead(left)
            val rightHead = getApplicationHead(right)

            //if there is no proper construction of nested applications I will get null
            if (leftHead != null && rightHead != null) {
              (leftHead, rightHead) match {
                case (l: Var, r: Const) =>

                  if(l.inftype == null || r.tp == null) {
                    throw new Error("Variables have to be strongly typed!")
                  }
                  val binders = gbinding(Var(r.name, r.tp), l.inftype, Nil)

                  if (binders == null || binders.size == 0) {
                    null
                  } else {
                    var result: List[(Var, Formula)] = Nil

                    for(binder <- binders){
                      val newleft: Formula = betanfRecursive(substitute(binder, l, left))

                      var newBinderacc : List[(Var,Formula)] = Nil
                      if(binderacc != Nil) {
                        // NOTE THIS PART OF SUBSTITUTION AND BETA REDUCTION CAUSES THE PROBLEMS. 2 MORE hours and i can fix it
                        newBinderacc = binderacc.map({ case (v, f) => (v, betanfRecursive(substitute(binder, l, f)))})
                      }else{
                        newBinderacc = List(l -> binder)
                      }
                      //find the substitutions by replacing them recursively
                      val res: List[(Var, Formula)] = SIM(((newleft, right) :: rest).distinct, 0, newBinderacc.distinct, isRecursingBack)

                      //did it fail?
                      //we also need to check if it returned Nil
                      if (res != null) {
                        result :::= res
                        break
                      }
                    }

                    result.distinct
                  }
                case (l: Var, r: Var) => {
                  //REUSED FROM HOU
                  if (l.inftype == null || r.inftype == null) {
                    throw new Error("Variables have to be strongly typed!")
                  }
                  val binders = gbinding(Var(r.name, r.inftype), l.inftype, Nil)

                  //for each binder recursively get the substitutions (binders) in lower level
                  //apply the substitutions to the binder from which they were generated
                  //check if we HAVE TO unify other pairs, if not return the substitutions(binders) up in the tree
                  //the reason I am using a list of lists is that one binder can have multiple substitutions to be made in order to solve it
                  //in other words in that binder we generated more than one variable


                  //if there are no binders that can be generated then it can't be unified. return null for failure
                  // we don't care if there is something in the rest because if there is, it is an AND branch.

                  if (binders == null || binders.size == 0) {
                    null
                  } else {
                    var result: List[(Var, Formula)] = Nil

                    // CHANGED FROM HOU: If one binder succedes we don't try the others.
                    for(binder <- binders){
                      val newleft: Formula = betanfRecursive(substitute(binder, l, left))

                      var newBinderacc : List[(Var,Formula)] = Nil
                      if(binderacc != Nil) {

                        // NOTE THIS PART OF SUBSTITUTION AND BETA REDUCTION CAUSES THE PROBLEMS. 2 MORE hours and i can fix it
                        newBinderacc = binderacc.map({ case (v, f) => (v, betanfRecursive(substitute(binder, l, f)))})
                      }else{
                        newBinderacc = List(l -> binder)
                      }
                      //find the substitutions by replacing them recursively
                      val res: List[(Var, Formula)] = SIM(((newleft, right) :: rest).distinct, 0, newBinderacc.distinct, isRecursingBack)

                      //did it fail?
                      //we also need to check if it returned Nil
                      if (res != null) {
                        result :::= res
                        break
                      }
                    }

                    result.distinct
                  }
                }
                  // REUSED FROM HOU
                case _ => SIM((right, left) :: rest, areWeDone + 1, binderacc.distinct, isRecursingBack)
              }
            } else {
              // REUSED FROM HOU
              SIM(rest :+(left, right), areWeDone + 1, binderacc.distinct, isRecursingBack)
            }
          }
        }
        // REUSED FROM HOU
        case (left, right: Apply) :: rest => {
          SIM((right, left) :: rest, areWeDone, binderacc.distinct, isRecursingBack)
        }
        case (left : Equal, right : Equal) :: rest =>{
          val first = SIM(List(left.l -> right.l), 0, binderacc, isRecursingBack)

          var subs_left = left.r
          var subs_right = right.r

          first.foreach(x => {
            subs_left = subs_left.replace(x._1, x._2)
            subs_right = subs_right.replace(x._1, x._2)
          })

          val second = SIM(List(subs_left -> subs_right), 0, binderacc, isRecursingBack)

          if(second == null || first == null){
            val result = SIM(Equal(left.r,left.l) -> right :: rest, areWeDone, binderacc, isRecursingBack)
            if(result == null){
              null
            }else{
              result
            }
          }else{
            val result = SIM(rest, 0, binderacc, isRecursingBack)
            if(result != null){
              first ::: second ::: result
            }else{
              null
            }
          }

        }
        // REUSED FROM HOU
        case a :: b => SIM(b ::: List(a), areWeDone + 1, binderacc.distinct, isRecursingBack)
        case Nil => {
          Nil
        }
      }

    }


    def produce_pairs(expr : (Formula,Boolean), acc : List[(Formula,Boolean)], isRecursingBack : Boolean) : List[List[(Formula,Boolean)]] = {
      expr match{
        case (Forall(lambda),bool) =>{
          if(bool){
            val newterm = Apply(lambda,generate_var(lambda.varTpe))
            produce_pairs((betanfRecursive(newterm),true),acc, isRecursingBack)
          }else{
            val newterm = Apply(lambda,generate_sk(lambda))
            produce_pairs((betanfRecursive(newterm),false),acc, isRecursingBack)
          }
        }
        case (Disj(left,right),bool) =>{
          if(bool){
            (produce_pairs((left,true), acc, isRecursingBack) ::: produce_pairs((right,true), acc, isRecursingBack)).distinct
          }else{
            //get the pairs that can be formed from one side and from the other
            //then create all possible branches n*n
            val pair1 = produce_pairs((left,false),acc, isRecursingBack)
            val pair2 = produce_pairs((right,false), acc, isRecursingBack)
            val branches : List[List[(Formula,Boolean)]] = pair1.flatMap(x => pair2.map(y => x:::y))
            branches.distinct
          }
        }
        case (Conj(left,right),bool) =>{
          if(bool){
            val pair1 = produce_pairs((left,true),acc, isRecursingBack)
            val pair2 = produce_pairs((right,true), acc, isRecursingBack)
            val branches : List[List[(Formula,Boolean)]] = pair1.flatMap(x => pair2.map(y => x:::y))
            branches.distinct
          }else{
            (produce_pairs((left,true), acc, isRecursingBack) ::: produce_pairs((right,true), acc, isRecursingBack)).distinct
          }
        }
        case (Neg(formula),bool) =>{
          produce_pairs((formula,!bool),acc, isRecursingBack)
        }
        case _ =>{
          List(expr::acc)
        }
      }

    }

    def add_axiom(tuples: List[List[(Formula, Boolean)]], pairs : List[List[(Formula, Boolean)]]): List[List[(Formula, Boolean)]] ={
      tuples.flatMap(x => pairs.map(y => y:::x))
    }


    def cut_branches(branches : List[List[(Formula,Boolean)]], substitutions : List[(Var,Formula)], isRecursingBack : Boolean) : Boolean = {
      branches match{
        case head::tl => {
          for(term1 <- head){
            for(term2 <- head){
              if(term1._2 != term2._2){
                var subs_term1 : Formula = term1._1
                var subs_term2 : Formula = term2._1
                substitutions.foreach(subs => {
                  subs_term1 = term1._1.replace(subs._1, subs._2)
                  subs_term2 = term2._1.replace(subs._1, subs._2)
                })

                val subst = SIM(List(subs_term1 -> subs_term2), 0, Nil, isRecursingBack)

                if(subst != null){
                  val next = cut_branches(tl,subst, isRecursingBack)
                  if(next){
                    return true
                  }
                }
              }
            }
          }

          false
        }
        case Nil => true
      }
    }

    var pairs = produce_pairs((formula,false), Nil, false)

    val axiom1 = Equal(Var("X", E), Apply(Const("s", E->:E),Var("X",E)))
    val impl = Forall(Lambda(Var("N", E), E, Equal(Apply(Var("H",E->:E),Var("N",E)), Apply(Var("K", E->:E), Var("N",E)))))
    val axiom2 = Disj(Neg(Equal(Var("H", E->:E), Var("K",E->:E))), impl)

    pairs = add_axiom(produce_pairs(axiom1 -> false, Nil, false), pairs)
    pairs = add_axiom(produce_pairs(axiom2 -> true, Nil,false), pairs)

    cut_branches(pairs, Nil,false)



  }


  def main(args: Array[String]): Unit = {
    val left = Conj(Const("B",E),Neg(Const("B",E)))
    println(higherOrderProver(left))


    val cantor = Forall(Lambda(Var("F"), E->:E ->: E,Neg(Forall(Lambda(Var("G"), E->:E, Neg(Forall(Lambda(Var("J"), E, Neg(Equal(Apply(Var("F", E->:E->:E), Var("J", E)), Var("G", E->:E)))))))))))

    println(higherOrderProver(cantor))
  }

}





