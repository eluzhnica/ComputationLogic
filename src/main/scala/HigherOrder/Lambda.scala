package main.scala.HigherOrder

import scala.collection.mutable


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
        case c: Const =>
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

object LambdaManipulations{

  val rand = new scala.util.Random(System.currentTimeMillis())
  var generated : List[String] = Nil

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
            val newvar = Var(generateString(2)+counter)
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


  def generateString(n : Int) : String = {
    var res = rand.nextString(n)
    while(generated.contains(res)){
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
        case Lambda(v, tp, form1) => {
          Lambda(v, tp, betanfRoutine(form1))
        }
        case t: Const => t
        case v: Var => v
      }
    }

    betanfRoutine(form)
  }

  def getDecomposeMatch(left: Formula, right: Formula) : List[(Formula,Formula)] = (left, right) match {
    case (l : Var, r : Var) =>{
      if(l.name==r.name){
        Nil
      }else {
        null
      }
    }
    case (l : Const, r : Const) =>{
      if(l == r){
        Nil
      }else{
        null
      }
    }
    case (Apply(l1,r1), Apply(l2,r2)) =>{
      val dec = getDecomposeMatch(l1,l2)
      if(dec == null){
        return null
      }else{
         (r1,r2) :: dec
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
  def Simplification(left : Formula, right : Formula) : List[(Formula,Formula)] = {

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
        case (left: Apply, right: Apply) :: rest => {
          if (left.pred == right.pred) {
            SIM((left.form, right.form) :: rest, 0)
          }else{
            val matchingPairs = getDecomposeMatch(left,right)
            if(matchingPairs != null){
              SIM(matchingPairs ::: rest, 0)
            }else{
              SIM(rest :+ (left,right), areWeDone+1)
            }
          }
        }
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


  /**
   *
   * @param t
   * @return the return type of a type
   */
  private def getReturnType(t : Type) : Type = {
    t match{
      case arrow : Arrow => getReturnType(arrow.right)
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
  def gApplication(value : Type, formula : Formula, vars : List[Var], avoid : List[Var]) : Formula = {

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

    var name = generateString(1)
    val avoiding = vars ::: avoid
    while(avoiding.exists(x => (x.name.contains(name)))){
      name = generateString(1)
    }


    generateApplications(value, name, formula)
  }

  /**
   *
   * @param value - the alpha type
   * @param vars - variables to avoid
   * @param application - application to be used, usually the given head of gBinding
   * @return lambdaExpression.head
   */
  def gLambda(value : Type, vars : List[Var], application : Formula ) : Formula= {

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
    var name = generateString(1)
    while(vars.exists(x => (x.name.contains(name)))){
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
    formula match{
      case Lambda(v,t,form) => {
        Lambda(v,t,gProjections(form,value))
      }
      case v : Var => value
      case _ => throw new Error("Malformed base lambda")
    }
  }

  def getHead(formula: Formula) : Var = formula match{
    case Lambda(v,t,form) =>{
      getHead(form)
    }
    case hd : Var=> hd
    case _ => throw new Error("Not a proper lambda passed!")
  }

  /**
   *
   * @param head - the head of the general binder
   * @param tpe - the type of the to be generated general binder
   * @param avoid - variables to avoid
   * @return  general binder + projections
   */
  def gbinding(head : Var, tpe : Type, avoid : List[Var]) : List[Formula] = {
    //if the return types don't match there is noway to generate anything correct or if the type is base type
    if(getReturnType(head.inftype) != getReturnType(tpe) || tpe == E || tpe == T) {
      return null
    }

    var application : Formula = head

    //avoid the head, don't capture it
    var formula : Formula = gLambda(tpe, head::avoid, application)

    if(!(head.inftype == E || head.inftype == T)){
      application = gApplication(head.inftype, application, formula.bound, head::avoid)
    }

    formula = formula.replace(head,application)

    val headReturnType = getReturnType(head.inftype)

    //projections without the applications part
    //generate projections for which the variable type matches with the return type that head has

    var projections : List[Formula] = Nil
    formula.bound.foreach(variable =>{
      if(variable.inftype != headReturnType){}
      else if(variable.inftype == E || variable.inftype == T){
        projections ::= formula.rename(head,variable)
      }else {
        val tempAppl= gApplication(head.inftype, variable, formula.bound, avoid)
        projections ::= formula.replace(variable,tempAppl)
      }
    })  //we don't need to avoid the head


    //if the head indicates that it takes parameters then we go and generate them


    formula::projections
  }



  def higherOrderUnification(left : Formula, right : Formula) : List[List[(Var,Formula)]] = {

    var skolems: List[Const] = Nil

    def containsSkolems(tuples: List[(Formula, Formula)], consts: List[Const]): Boolean = {
      val constants = tuples.map({ case (left, right) => {
        (left.constants ::: right.constants).distinct
      }
      })

      constants.intersect(consts) != Nil
    }



    def betanfRecursive(formula : Formula) : Formula = {
      var last = formula
      while(last != betanf(last)){
        last = betanf(last)
      }
      last
    }


    def elimConditionCheck(tuples : List[(Formula,Formula)], skolems : List[Const]) : Boolean = {
      tuples match {
        case (left: Var, right: Formula) :: rest => {
          return !right.free.contains(left) && !containsSkolems((Var("test"), right) :: Nil, skolems) && rest.flatMap({ case (x, y) => x.free ::: y.free}).contains(left)
        }
        case _ => false
      }
    }

    def getApplicationHead(apply: Formula) : Formula = apply match{
      case Apply(l,r) => {
        getApplicationHead(l)
      }
      case t : Var => t
      case t : Const => t
      case _ => null
    }


    /**
     *
     * @param tobeUni - pairs to be unified (simplifed)
     * @param areWeDone - counts the number of circulations because of no case match
     * @return - the simplified pairs
     */
    def SIM(tobeUni: List[(Formula, Formula)], areWeDone: Integer): List[List[(Var, Formula)]] = {
      //if we circulated all the pairs without doing work then we're done, it's unified

      val newUni = tobeUni.filterNot({
        case(x:Var,y:Var) => (x==y)
        case _ => false
      })

      val vars = newUni.collect({
        case(x: Var, y) => x
        case(y, x : Var) => x
      })

      //are all the pairs distinct on variable part and are all the pairs x =? smth and smth doesnt contain skolems or x
      if(newUni == Nil || (vars.size == newUni.size && vars.distinct.size == vars.size && newUni.forall({
        case(x : Var, y: Formula) => !y.free.contains(x) && y.constants.intersect(skolems) == Nil
        case(y : Formula, x : Var) => !y.free.contains(x) && y.constants.intersect(skolems) == Nil
      }))){
        return Nil
      }

      if (areWeDone - 2 > tobeUni.size){

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
        case (left: Apply, right : Apply) :: rest if (left.pred == right.pred) =>{

          SIM((left.form, right.form) :: rest, 0)

        }

        case (left: Var, right) :: rest if(elimConditionCheck((left,right)::rest, skolems)) => {
          //x = x ? or the regular check
          if (left == right){
            return SIM(rest,areWeDone+1) //note that this would return Nil if there is nothing there, which is not a FAIL return.
          }

          var modified = false

          //the rest is SIM stuff
          //check the individual pairs
          val newrest = rest.map({
            case (x, y) => {

              if(!containsSkolems(List((x,y)), skolems) //do they contains skolem constants?
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
        case (left : Apply, right) :: rest =>{
          //check if the decomposition matches on head
          val matchingPairs = getDecomposeMatch(left,right)
          if(matchingPairs != null){
            SIM(matchingPairs ::: rest, 0)
          }else{

            val leftHead = getApplicationHead(left)
            val rightHead = getApplicationHead(right)

            //if there is no proper construction of nested applications I will get null
            if(leftHead != null && rightHead != null){

              (leftHead, rightHead) match{
                case (l : Var, r : Const) =>{
                  val binders: List[Formula] = gbinding(Var(r.name,r.tp), l.inftype, (left.bound ::: left.free ::: right.bound ::: right.free).diff(List(Var(r.name,r.tp))))

                  //for each binder recursively get the substitutions (binders) in lower level
                  //apply the substitutions to the binder from which they were generated
                  //check if we HAVE TO unify other pairs, if not return the substitutions(binders) up in the tree
                  //the reason I am using a list of lists is that one binder can have multiple substitutions to be made in order to solve it
                  //in other words in that binder we generated more than one variable

                  //if there are no binders that can be generated then it can't be unified. return null for failure
                  // we don't care if there is something in the rest because if there is, it is an AND branch.
                  if(binders == null || binders.size == 0) {
                    null
                  }else {
                    var one_setOfSub_perBinder : List[(Var,Formula)] = Nil
                    var allSubsPerBinder: List[List[(Var, Formula)]] = Nil
                    var results_for_all_binders : List[List[(Var,Formula)]] = Nil

                    binders.foreach(binder => {
                      val newleft = betanfRecursive(substitute(binder, l, left))

                      //find the substitutions by replacing them recursively
                      val result = SIM((newleft, right) :: rest, 0)

                      //did it fail?
                      //we also need to check if it returned Nil
                      if (result != null) {


                        //if not then get each set of substitution for the variables generated in the binder and apply them to solve the binder
                        result.foreach(set_of_sub => {
                          if (set_of_sub != null) {
                            var onePossibleBinder: Formula = binder
                            var variableSubs: List[(Var, Formula)] = Nil
                            set_of_sub.foreach({
                              case (varib, subst) => {
                                if (onePossibleBinder.free.contains(varib)) {
                                  onePossibleBinder = substitute(subst, varib, onePossibleBinder)
                                } else {
                                  variableSubs ::= (varib, subst)
                                }
                              }
                            })
                            //the head -> binder should be added to the results
                            one_setOfSub_perBinder ::= (l -> betanfRecursive(onePossibleBinder))
                            one_setOfSub_perBinder :::= variableSubs
                            allSubsPerBinder ::= one_setOfSub_perBinder
                          }
                        })
                      }

                      //if Nil then it unified but generated nothing else
                      if (result == Nil) {
                        allSubsPerBinder ::= List(l -> binder)
                      }

                      val next = SIM(rest,0)
                      var appended: List[List[(Var, Formula)]] = Nil
                      if(next == Nil){ //succeeded but nothing generated
                        appended = allSubsPerBinder
                      }else if(next == null){ //failed, since all should unify, none of the subs holds anymore
                        appended = Nil
                      }else{
                        appended = allSubsPerBinder.flatMap(x => next.map(y => x:::y))  //create all the possible pairs
                      }

                      results_for_all_binders :::= appended
                    })
                    if(results_for_all_binders == Nil){
                      null
                    }else {
                      results_for_all_binders.distinct
                    }
                  }

                }
                case (l : Var, r : Var) => {

                  //copy paste the code form above, change some stuff (okay I could build a function)

                  if(l.inftype ==null || r.inftype==null){
                    throw new Error("Variables have to be strongly typed!")
                  }
                  val binders = gbinding(Var(r.name,r.inftype), l.inftype, (left.bound ::: left.free ::: right.bound ::: right.free).diff(List(r)))

                  //for each binder recursively get the substitutions (binders) in lower level
                  //apply the substitutions to the binder from which they were generated
                  //check if we HAVE TO unify other pairs, if not return the substitutions(binders) up in the tree
                  //the reason I am using a list of lists is that one binder can have multiple substitutions to be made in order to solve it
                  //in other words in that binder we generated more than one variable



                  //if there are no binders that can be generated then it can't be unified. return null for failure
                  // we don't care if there is something in the rest because if there is, it is an AND branch.
                  if(binders == null || binders.size == 0) {
                    null
                  }else {
                    var one_setOfSub_perBinder : List[(Var,Formula)] = Nil
                    var allSubsPerBinder: List[List[(Var, Formula)]] = Nil
                    var results_for_all_binders : List[List[(Var,Formula)]] = Nil

                    binders.foreach(binder => {
                      val newleft = betanfRecursive(substitute(binder, l, left))

                      //find the substitutions by replacing them recursively
                      val result = SIM((newleft, right) :: Nil, 0)

                      //did it fail?
                      //we also need to check if it returned Nil
                      if (result != null) {

                        //if not then get each set of substitution for the variables generated in the binder and apply them to solve the binder
                        result.foreach(set_of_sub => {
                          if (set_of_sub != null) {
                            var onePossibleBinder: Formula = binder
                            var variableSubs: List[(Var, Formula)] = Nil
                            set_of_sub.foreach({
                              case (varib, subst) => {
                                if (onePossibleBinder.free.contains(varib)) {
                                  onePossibleBinder = substitute(subst, varib, onePossibleBinder)
                                } else {
                                  variableSubs ::= (varib, subst)
                                }
                              }
                            })
                            //the head -> binder should be added to the results
                            one_setOfSub_perBinder ::= (l -> betanfRecursive(onePossibleBinder))
                            one_setOfSub_perBinder :::= variableSubs
                            allSubsPerBinder ::= one_setOfSub_perBinder
                          }
                        })
                      }

                      //if Nil then it unified but generated nothing else
                      if (result == Nil) {
                        allSubsPerBinder ::= List(l -> binder)
                      }

                      val next = SIM(rest,0)

                      var appended = allSubsPerBinder.flatMap(x => next.map(y => x:::y))
                      if(next == Nil){
                        appended = allSubsPerBinder
                      }else if(next == null){
                        appended = Nil
                      }

                      results_for_all_binders :::= appended
                    })
                    if(results_for_all_binders == Nil){
                      null
                    }else {
                      results_for_all_binders.distinct
                    }
                  }

                }
                case _ => SIM((right,left) :: rest, areWeDone+1)
              }
            }else {
              SIM(rest :+(left, right), areWeDone + 1)
            }
          }
        }
        case (left, right : Apply) :: rest => {
          SIM((right,left)::rest, areWeDone)
        }
        // if none of the cases worked out, try to apply the rules on the rest
        // but remember how many times we did no work
        case a :: b => SIM(b ::: List(a), areWeDone + 1)
        case Nil => {
          Nil
        }
      }

    }


    SIM(List((left,right)),0)
  }

  case class Equals(left : Formula, right : Formula) extends Formula{
    //  def checkVariableTypeMatch(variable : Var) : Boolean
    override def free: List[Var] = null

    override def rename(variable: Var, renamed: Var): Formula = null

    override def bound: List[Var] = null

    override def replace(variable: Var, formula: Formula): Formula = null

    override def constants: List[Const] = null

    override def toString = left.toString + "=" + right.toString
  }


  abstract class ArithExp{
    def toNum : Int
  }

  case class Plus(left : ArithExp, right : ArithExp) extends ArithExp{
    def toNum = left.toNum + right.toNum
  }
  case class Times(left : ArithExp, right : ArithExp) extends ArithExp{
    def toNum = left.toNum * right.toNum
  }
  case class Exp(base : ArithExp, exp : ArithExp) extends ArithExp{
    def toNum = math.pow(base.toNum.toDouble, exp.toNum.toDouble).toInt
  }
  case class Num(n : Int) extends ArithExp{
    def toNum = n
  }
  case class Minus(left : ArithExp, right : ArithExp) extends ArithExp{
    def toNum = left.toNum - right.toNum
  }
  case class Div(nom : ArithExp, denom : ArithExp) extends ArithExp{
    def toNum = nom.toNum + denom.toNum
  }
  case class Mod(num : ArithExp, mod : ArithExp) extends ArithExp{
    def toNum = num.toNum + mod.toNum
  }
  case class Root(num : ArithExp, root : ArithExp) extends ArithExp{
    def toNum = num.toNum + root.toNum
  }


  def generatePlus(n : Formula, m : Formula) = {

    val n1 = Var(generateString(2))
    val m1 = Var(generateString(2))
    val s = Var(generateString(1))
    val o = Var(generateString(1))


    val baseLambda = Lambda(n1, (E->:E) ->: E ->: E, Lambda(m1, (E->:E) ->: E ->: E ,
      Lambda(s, E->:E, Lambda(o, E, Apply(Apply(n1,s), Apply(Apply(m1, s),o))))))

    Apply(Apply(baseLambda,n),m)
  }

  def generateTimes(n: Formula, m: Formula): Formula = {

    val n1 = Var(generateString(2))
    val m1 = Var(generateString(2))
    val s = Var(generateString(1), E->:E)
    val o = Var(generateString(1), E)

    val baseLambda = Lambda(n1, (E->:E) ->: E ->: E, Lambda(m1, (E->:E) ->: E ->: E ,
      Lambda(s, E->:E, Lambda(o, E, Apply(n1, Apply(m1,s))))))

    Apply(Apply(baseLambda,n),m)
  }

  def generateExp(n : Formula, m: Formula): Formula = {
    val n1 = Var(generateString(2))
    val m1 = Var(generateString(2))

    val baseLambda = Lambda(n1, (E->:E) ->: E ->: E, Lambda(m1, (E->:E) ->: E ->: E, Apply(m1,n1)))

    Apply(Apply(baseLambda,n),m)
  }

  def generateMinus(n : Formula, m : Formula) : Formula = {
    val x = Var(generateString(2))
    val left = generatePlus(m,x)
    val right = n

    Equals(left,right)
  }


  def generateDiv(n : Formula, m : Formula) : Formula = {
    val x = Var(generateString(2))
    val left = generateTimes(m,x)
    val right = n

    Equals(left, right)

  }


  def generateRoot(n: Formula, m: Formula): Formula ={
    val x = Var(generateString(2))
    val left = generateExp(x,m)
    val right = n

    Equals(left,right)
  }

  def churchexp(exp : ArithExp) : Formula = {

    if(exp.toNum < 0){
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


  def churchnum(num : Int) : Formula = {

    def successors(n : Int) : Formula = {
      if(n==0){
        Var("O",E)
      }else{
        Apply(Var("S",E ->: E), successors(n-1))
      }
    }
    Lambda(Var("S", E ->: E), E->:E, Lambda(Var("O", E), E, successors(num)))
  }


  def churchtono(numeral : Formula) : Int = {

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

    def betanfRoutine(form : Formula) : Formula = {
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
        case Equals(l,r) => {
          val solved = higherOrderUnification(l,r)
          var result : Formula = l
          if(solved.length == 0){
            throw new Error("Error during unification")
          }
          solved(0).foreach({
            case(x : Var,y) => result = substitute(y,x,result)
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
    val peter = Apply(Var("P", E->:E),Const("Peter",E))
    val john = Apply(Var("P", E->:E),Const("John",E))

    val unifiers = higherOrderUnification(john,love)
    if(unifiers.length < 1){
      throw new Error("Error during unification")
    }
    println(unifiers)
    println(unifiers.size)
    //unifiers.foreach(uni => uni.foreach{case(x,y) => println(substitute(y,x,john))})
  }

  //betanf doesn't work properly
  def churcheval(formula : Formula) = {

    var last = normalize(formula)
    while(last != normalize(last)){
      last = normalize(last)
    }
    last
  }

  def main(args : Array[String]) : Unit = {
//    val left = Lambda(Var("X"), E,  Var("X"))
//    val right = Lambda( Var("Y"), E, Var("Z", E))
//
//    val left1 = Lambda( Var("X"), E->:E, Apply(Var("X"),Const("a",E)))
//    val right1 = Const("f", (E ->: E) ->: E)
//
//
//    println(Simplification(left,right))
//    println(Simplification(left1,right1))
//
//    val head = Var("k", T ->: T->: E)
//    val tpe = T ->: E ->: E
//
//    val left2 = Lambda(Var("X"),E->: E ->:E, Lambda(Var("Y"), E->:E, Apply(Var("Z"),Var("K"))))
//    val right2 = Lambda(Var("A"),E->: E ->:E, Lambda(Var("B"), E->:E, Apply(Var("Z"),Var("F1"))))
//
//    val left3 = Lambda(Var("X"),E->: E ->:E, Lambda(Var("Y"), E->:E, Apply(Var("Z"),Var("K"))))
//    val right3 = Apply(Var("X"),Apply(Var("Z"), Apply(Var("F"),Var("E1"))))
//
//    println(Simplification(left2,right2))
//    println(Simplification(left3,right3))
//    println(gbinding(head,tpe, List(Var("K"))))


    println(churchnum(1))
    println(churchnum(0))
    println(churchnum(5))

    println(churchtono(churchnum(5)))
    println(churchtono(churchnum(0)))
    println(churchtono(churchnum(1)))
    println(churchtono(churchnum(13)))


    //examples for Problem 2
//    val expr1 = Plus(Num(4), Num(14))
//    val expr2 = Times(Num(22),Num(3))
//    val expr3 = Plus(expr1,Num(5))
//    val expr4 = Exp(Num(4),Num(5))
//    val expr5 = Plus(expr4,expr3)
//
//    println(expr1)
//    println(churchtono(churcheval(churchexp(expr1))))
//
//    println(expr2)
//    println(churchtono(churcheval(churchexp(expr2))))
//
//    println(expr3)
//    println(churchtono(churcheval(churchexp(expr3))))
//
//    println(expr4)
//    println(churchtono(churcheval(churchexp(expr4))))
//
//    println(expr5)
//    println(churchtono(churcheval(churchexp(expr5))))


//    println(higherOrderUnification(Apply(Var("Q",E->:E),Var("J",E)),Var("F",E)))

//    val expr5 = Plus(Minus(Num(4),Num(3)),Num(5))
//    println(churchexp(expr5))
//    println(churchtono(churcheval(churchexp(expr5))))

    ellipsis()

    val l1 = List(List(1,2,3,4),List(1,2,3,4,5))
    val l2 = List(List(11,121), List(13,169), List(134,168))

    println(l1.flatMap(x => l2.map(y => x:::y)))
    println(higherOrderUnification(Apply(Var("B",E->:E),Var("j",E)),Var("j",E)))


  }

  //think twice before starting to fix any bugs though.

}



