package main.scala.HigherOrder


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

  def bound: List[Var]
  def constants : List[Const]
  def rename(variable: Var, renamed: Var): Formula
}

case class Const(name: String, tp: Type) extends Formula {
  //  def checkVariableTypeMatch(variable : Var) = true
  def free = Nil
  def constants = List(this)
  def bound = Nil

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

  def rename(variable: Var, renamed: Var) = if (variable == this) renamed else Var(name)

  override def toString = "V("+name+")"
}

case class Apply(pred: Formula, form: Formula) extends Formula {
  def constants = (pred.constants ::: form.constants).distinct
  def free = (form.free ::: pred.free).distinct
  def bound = (pred.bound ::: form.bound).distinct
  def rename(variable: Var, renamed: Var) = Apply(pred.rename(variable, renamed), form.rename(variable, renamed))
  override def toString = pred.toString+"("+ form.toString + ")"
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
        case c: Const =>
      }
    }

    bindVariable(form.form, form.variable)
  }

  def constants = form.constants
  def free = form.free diff List(variable)
  def bound = variable :: form.bound
  def rename(variable: Var, renamed: Var) = {
    if (variable == this.variable)
      Lambda(renamed, varTpe, form.rename(variable, renamed))
    else
      Lambda(this.variable, varTpe, form.rename(variable,renamed))
  }
  override def toString = "λ"+variable.toString+"."+form.toString
}

object LambdaManipulations{

  def alphaVariants(left: Formula, right: Formula) = alphaVariantRoutine(left, right, Nil)

  def alphaVariantRoutine(form1: Formula, form2: Formula, renamings: List[(Var, Var)]): List[(Var, Var)] = {
    (form1, form2) match {
      case (Lambda(var1, type1, form1), Lambda(var2, type2, form2)) if (type1 == type2) => {
        alphaVariantRoutine(form1, form2, (var1, var2) :: renamings)
      }
      case (Apply(pred1, form1), Apply(pred2, form2)) => {
        if (pred1 != pred2) {
          val renam = alphaVariantRoutine(pred1, pred2, renamings)

          if(renam != Nil) alphaVariantRoutine(form1, form2, renam)
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
  def substitute(sub : Formula, tosub : Var, formula : Formula) = {

    var counter = 0
    def subst(sub: Formula, tobesub: Var, form: Formula, bound: List[Var]): Formula = {
      form match {
        case Const(name, tp) => Const(name, tp)
        case variable : Var => {
          if (bound.exists(x => x.name == variable.name )) {
            variable
          } else if (tobesub.name == variable.name /*&& variable.inftype == tobesub.inftype*/) {
            sub
          } else {
            variable
          }
        }
        case Apply(pred, formula) => {
          Apply(subst(sub, tobesub, pred, bound), subst(sub, tobesub, formula, bound))
        }
        case Lambda(variable, tpe, body) => {
          if(tobesub.name == variable.name /*&& variable.inftype == tobesub.inftype*/){
            body //this was described in the hint of the problem
          }else if(sub.free.exists(v => variable.name == v.name  /*&& v.inftype == variable.inftype*/)){
            val newvar = Var("gen_"+counter)
            counter+=1
            newvar.inftype = variable.inftype
            val renamed = Lambda(variable, tpe, body).rename(variable, newvar)
            subst(sub, tobesub, renamed, newvar :: bound diff List(variable))
          }else {
            Lambda(variable, tpe, subst(sub, tobesub, body, bound))
          }
        }
      }
    }


    def substituteRoutine(subs: Formula, toBeSub: Var, form: Formula): Formula = {
        subst(subs, toBeSub, form, form.bound)
    }

    substituteRoutine(sub, tosub, formula)
  }


  //the TC function, I renamed it for readability issues
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
        case Apply(predicate, formula) => {
          Apply(betanfRoutine(predicate), betanfRoutine(formula))
        }
        case Lambda(v, tp, form) => {
          Lambda(v, tp, betanfRoutine(form))
        }
        case t: Const => t
        case v: Var => v
      }
    }

    betanfRoutine(form)
  }

  def Simplification(left : Formula, right : Formula) : List[(Formula,Formula)] = {

    var skolems: List[Const] = Nil

    def containsSkolems(tuples: List[(Formula, Formula)], consts: List[Const]): Boolean = {
      val constants = tuples.map({ case (left, right) => {
        (left.constants ::: right.constants).distinct
      }
      })

      constants.intersect(consts) != Nil
    }

    def SIM(tobeUni: List[(Formula, Formula)], areWeDone: Integer): List[(Formula, Formula)] = {
      //if we circulated all the pairs without doing work then we're done
      if (areWeDone > tobeUni.size){
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
        case (left: Apply, right: Apply) :: rest if (left.pred == right.pred) => {
          SIM((left.form, right.form) :: rest, 0)
        }
        // the syntax gets ugly, i even googled it, that's the preferred way to do it.
        case (left: Var, right) :: rest if (!right.free.exists(x => (x.name == left.name))) => { //do we have the case X = something (X) ?
          var modified = false

          //check the individual pairs
          val newrest = rest.map({
            case (x, y) => {

              if(!containsSkolems(List((x,y)), skolems) //do the contains skolem constants?
                && (x.free ::: y.free)
                .distinct
                .exists(x => (x.name == left.name))  // is there anything we can substitute, (is X in free(E))
              ){
                modified = true
                (substitute(right, left, x),substitute(right, left, y))
              }else{
                (x,y)
              }

            }
          })

          // if nothing was substituted then increase the counter
          if(modified)
            SIM(newrest :+(left, right), 0)
          else
            SIM(newrest :+ (left,right), areWeDone+1)

        }
        case Nil => {
          tobeUni
        }
        // if none of the cases worked out, try to apply the rules on the rest
        // but remember how many times we did no work
        case a :: b => SIM(b ::: List(a), areWeDone + 1)
      }

    }

    SIM(List((left,right)),0)
  }


  private def getReturnType(t : Type) : Type = {
    t match{
      case arrow : Arrow => getReturnType(arrow.right)
      case E => E
      case T => T
    }
  }


  //generates the application arguments that are going to be applied to lambda expression
  def gApplication(value : Type, formula : Formula, vars : List[Var], avoid : List[Var]) = {

    //generates the block that is used inside H1,H2,.. (for instance H1XY)
    def generateOne(vars: List[Var], formula : Formula): Formula = {
      vars match {
        case head :: tail => {
          generateOne(tail, Apply(formula, head))
        }
        case Nil => formula
      }
    }

    //keeps track of the indexes, used to label H_1xy H_2xy and so on
    var h_counter = 0

    // this generates the actual application arguments to the lambda expression
    def generateApplications(value: Type, varName : String, formula: Formula): Formula = {
      h_counter += 1
      value match {
        case Arrow(a, b) => {
          //if we are not at the end (return type) then we can go on and recurse
          if (!(b == E || b == T)) {
            generateApplications(b, varName, Apply(formula, generateOne(vars, Var(varName + h_counter, a))))
          } else {
            Apply(formula, generateOne(vars, Var(varName + h_counter, a)))
          }
        }
      }
    }

    //made in China
    val random = new scala.util.Random()
    var name = random.alphanumeric(1).toString
    val avoiding = vars ::: avoid
    while(avoiding.exists(x => (x.name.substring(0,name.length) == name))){
      name = random.alphanumeric(1).toString
    }
    generateApplications(value, name, formula)
  }

  //generates the lambda expression based on the type
  def gLambda(value : Type, vars : List[Var], application : Formula ) = {

    var counter = 0

    def generateLambdas(value: Type, variableName : String, appl: Formula): Formula = {
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
    val random = new scala.util.Random()
    var name = random.alphanumeric(1).toString
    while(vars.exists(x => (x.name.substring(0,name.length) == name))){
      name = random.alphanumeric(1).toString
    }

    generateLambdas(value, name, application)
  }

  def gbinding(head : Var, tpe : Type, avoid : List[Var]) : Formula = {
    //if the return types don't match there is noway to generate anything correct or if the type is base type
    if(getReturnType(head.inftype) != getReturnType(tpe) || tpe == E || tpe == T) {
      return null
    }

    val application : Formula = head
    var formula : Formula = gLambda(tpe, avoid, application)

    //if the head indicates that it takes parameters then we go an generate them
    if(!(head.inftype == E || head.inftype == T)){
      formula = gApplication(head.inftype, formula, formula.bound, avoid)
    }

    formula
  }

  def main(args : Array[String]) : Unit = {
    val left = Lambda(Var("X"), E,  Var("X"))
    val right = Lambda( Var("Y"), E, Var("Z", E))

    val left1 = Lambda( Var("X"), E->:E, Apply(Var("X"),Const("a",E)))
    val right1 = Const("f", (E ->: E) ->: E)


    println(Simplification(left,right))
    println(Simplification(left1,right1))

    val head = Var("k", T ->: T->: E)
    val tpe = T ->: E ->: E

    val left2 = Lambda(Var("X"),E->: E ->:E, Lambda(Var("Y"), E->:E, Apply(Var("Z"),Var("K"))))
    val right2 = Lambda(Var("A"),E->: E ->:E, Lambda(Var("B"), E->:E, Apply(Var("Z"),Var("F1"))))

    val left3 = Lambda(Var("X"),E->: E ->:E, Lambda(Var("Y"), E->:E, Apply(Var("Z"),Var("K"))))
    val right3 = Apply(Var("X"),Apply(Var("Z"), Apply(Var("F"),Var("E1"))))

    println(Simplification(left2,right2))
    println(Simplification(left3,right3))
    println(gbinding(head,tpe, Nil))
  }

}



