package main.scala.FirstOrder

import main.scala._

import scala.collection.mutable
import scala.collection.mutable._

object ModelGen{

  private def simplePredicateCheck(form : FirstOrder.Formula, model : Map[FirstOrder.Formula,Boolean], truth : Boolean, proof : StandardTableauProof) = form match{
    case t : Pred =>{
      if(model.toList.exists({case(te : Pred,va) => (te.p == t.p) && (va != truth) && (t.args == te.args); case _ => false})){
        proof.standardTableauxFail = true
      }
    }
    case _ =>
  }

  def variable_unifier(variable: Variable, term: Term, unified: Map[Term, Term]) = {
    if(unified.contains(variable)){ //if the variable is already binded try to unify the other part
      unify(unified(variable) :: Nil,term::Nil,unified)
    }else if(unified.contains(term)){
      unify(variable::Nil , unified(term)::Nil, unified)
    }else if(term.freeVars.contains(variable.name)){ // if smth like X = S(X) , NO NO.
      unified(Variable("FAIL")) = Variable("FAIL")
    }else{ //match the variable and move on.
      unified(variable) = term
    }

  }


  def unify(left : List[Term] , right : List[Term], unified : Map[Term,Term]) : Map[Term,Term] = {
    if(unified.contains(Variable("FAIL"))){
      return unified
    }
    (left,right) match {
      //triviality
      case (Constant(x)::r1,Constant(y)::r2) =>{
        if(x==y){ // lucky case, move on
          unify(r1,r2,unified)
        }else{ //we can't play with the constants that much. If not equal, bad things happen.
          unified(Variable("FAIL")) = Variable("FAIL")
          unify(r1,r2,unified)
        }
      }
      case (Variable(x)::r1,y::r2)=> {
        variable_unifier(Variable(x),y,unified)
        unify(r1,r2,unified)
      }
      case (x::r1,Variable(y)::r2) => {
        // keep the variable as the first argument since we don't want to have two functions
        // just because of that
        variable_unifier(Variable(y),x,unified)
        unify(r1,r2,unified)
      }
      //first rule
      case (Func(x,argsx)::r1,Func(y,argsy)::r2) => {
        if(x != y){
          unified(Variable("FAIL")) = Variable("FAIL")
        }
        unify(argsx,argsy,unified)
        unify(r1,r2,unified)
      }
      case (_,_) => unified
    }

  }

  def areUnifiable(left : List[Term] , right : List[Term]) = !unify(left,right, new mutable.HashMap[Term,Term]()).contains(Variable("FAIL"))



  private class StandardTableauProof(form : FirstOrder.Formula){
    var guesses : List[Constant] = form.constants.map(x => Constant(x)) :+ Constant("general_1")
    var standardTableauxFail = false


    def initiate(form : FirstOrder.Formula) = {
      guesses = form.constants.map(x => Constant(x))
    }
  }

  private def standardTableauxRoutine(form : FirstOrder.Formula, model : Map[FirstOrder.Formula,Boolean], subs : Map[String,String], proof : StandardTableauProof) : Unit = form match{
    case t : Atom =>{
      if(proof.standardTableauxFail){
        return
      }
      //model.toList
      println(t+"_"+model(t))
    }
    case t : Conj =>{
      if(proof.standardTableauxFail){
        return
      }
      val isThere = model(t)
      if((model.contains(t.l) && model(t.l)!=isThere) ||(model.contains(t.r) && model(t.r) != isThere)){
        proof.standardTableauxFail = true
        println("("+t.l+")_"+isThere+"\t" + " ∧ \t" + "("+t.r+")_"+isThere )
        println("⊥")
        return
      }

      if(isThere) {
        println("(" + t.l + ")_" + isThere + "\t" + " ∧ \t" + "(" + t.r + ")_" + isThere + "\t")
        simplePredicateCheck(t.l, model, isThere, proof)
        if (proof.standardTableauxFail) {
          return
        }
        model(t.l) = isThere
        standardTableauxRoutine(t.l, model, subs, proof)

        simplePredicateCheck(t.r, model, isThere, proof)
        if (proof.standardTableauxFail) {
          return
        }
        model(t.r) = isThere



        standardTableauxRoutine(t.r, model, subs, proof)
      }
      else{
        println("(" + t.l + ")_" + isThere + "\t" + " v \t" + "(" + t.r + ")_" + isThere + "\t")
        simplePredicateCheck(t.l, model, isThere, proof)
        if (proof.standardTableauxFail) {
          return
        }
        val copymodel = model.clone()
        model(t.l) = isThere
        standardTableauxRoutine(t.l, model, subs, proof)
        if (proof.standardTableauxFail) {
          proof.standardTableauxFail = false
        }

        if (proof.standardTableauxFail) {
          return
        }
        copymodel(t.r) = isThere
        standardTableauxRoutine(t.r, copymodel, subs, proof)
        model.clear()
        model ++=copymodel
      }
    }
    case t : Neg =>{
      if(proof.standardTableauxFail){
        return
      }

      val isThere = model(t)
      println(t.form + "_"+ (!isThere))
      if(model.contains(t.form) && model(t.form) == isThere){
        proof.standardTableauxFail = true
        println("("+t.form +")_"+isThere)
        println("⊥")
        return
      }
      simplePredicateCheck(t.form,model,!isThere, proof)
      if(proof.standardTableauxFail){
        return
      }
      model(t.form) = !isThere


      standardTableauxRoutine(t.form, model,subs, proof)
    }
    case t : Pred =>{
      if(proof.standardTableauxFail){
        return
      }
      //NOTE: I could add all the arguments of the predicate to the model to make them true
      //but i am not doing that on purpose, because without a predicate interpretation function that doesn't make sense to me.
      //model.toList

      println(t+"_"+model(t))
    }
    case t : Forall => {
      if(proof.standardTableauxFail){
        return
      }

      val isThere = model(t)
      if(model.contains(t.body) && model(t.body) != isThere){
        proof.standardTableauxFail = true
        println("("+t.body +")_"+isThere)
        println("⊥")
        return
      }

      if(isThere) {

        proof.guesses.foreach(c => {
          t.context.vars.foreach(name =>{
            val replaced = t.replaceVar(c,name)
            subs(name) = c.name

            model(replaced) = isThere
            simplePredicateCheck(replaced.body,model,isThere, proof)
            if(proof.standardTableauxFail){
              println("⊥")
              return
            }
            model(replaced.body) = isThere

            standardTableauxRoutine(replaced.body, model,subs, proof)
            if(proof.standardTableauxFail){
              println("⊥")
              return
            }else{
              proof.standardTableauxFail = false
              //model.remove(replaced.body)
              //subs.remove(name)
            }
          })

        })
      }else{

        proof.guesses.foreach(c => {
          t.context.vars.foreach(name =>{
            val replaced = t.replaceVar(c,name)
            subs(name) = c.name


            model(replaced) = isThere
            simplePredicateCheck(replaced.body,model,isThere, proof)
            if(proof.standardTableauxFail){
              println("⊥")
              return
            }
            model(replaced.body) = isThere
            standardTableauxRoutine(replaced.body, model,subs,proof)
            if(proof.standardTableauxFail){
              println("⊥")
              return
            }else{
              proof.standardTableauxFail = false
              model.remove(replaced.body)
              subs.remove(name)
            }
          })

        })
      }

    }
    case _ => throw new Error("Only negation, conjuction and forall allowed")
  }

  /**
   *
   * @param form - main.scala.FirstOrder.Formula
   * @return a pair of lists, model and substitutions
   */
  def standardTableaux(form : FirstOrder.Formula)  = {
    val proof = new StandardTableauProof(form)
    val map = new HashMap[FirstOrder.Formula,Boolean]()
    val subs = new HashMap[String,String]()
    map(form)=true

    println("("+form+")_"+true)
    println("____P__R__O__O__F_____")
    standardTableauxRoutine(form.translate(), map,subs,proof)
    val model = map
    val result = model collect {
      case (t: Atom, b) => (t,b)
      case (t: Pred,b) => (t,b)
    }
    if(!proof.standardTableauxFail){
      Some(result.toList)
    }else{
      None
    }
  }



  //these can easily be passed as parameters to a function but that's not the point
  class Proof{
    var result : List[List[(FirstOrder.Formula,Boolean)]] = Nil
    var functionCounter = 0
    var variableCounter = 0
    var methodFail = false

    def addResult(rs : List[(FirstOrder.Formula,Boolean)]) = {
      if(result == Nil){
        result = List(rs)
      }else{
        result = rs :: result
      }
    }


  }
  def freeVariableTableauxRoutine(form : FirstOrder.Formula, model : Map[List[Term],Boolean], value : Boolean, fund : Map[FirstOrder.Formula,Boolean], proof : Proof) : Unit = {
    form match {
      case t : Forall =>{
        println(t.toString +"_"+value)
        var replaced = t
        if(value){
          val context = t.context.vars
          context.foreach(x =>{
            replaced = replaced.replaceVar(Variable("gen_"+ proof.variableCounter), x)
            proof.variableCounter += 1
          })
        }else{
          val variables = t.freeVars
          variables.foreach(x =>{
            replaced = replaced.replaceVar(Func("func_"+ proof.functionCounter, variables.map(y => Variable(y))), x)
            proof.functionCounter += 1
          })
        }
        freeVariableTableauxRoutine(replaced.body, model, value, fund, proof)
      }
      case t : Conj =>{
        println(t.toString + "_"+value)
        if(value) {
          freeVariableTableauxRoutine(t.l, model, value, fund, proof)
          if(proof.methodFail){
            return
          }
          freeVariableTableauxRoutine(t.r, model, value, fund, proof)
        }else{
          val modelcopy: Map[List[Term], Boolean] = model.clone()
          val fundcopy = fund.clone()
          freeVariableTableauxRoutine(t.l,model,value, fund, proof)
          freeVariableTableauxRoutine(t.r, modelcopy, value, fundcopy, proof)
        }
      }
      case t : Neg =>{
        println(t.toString + "_"+value)
        freeVariableTableauxRoutine(t.form, model, !value, fund, proof)
      }
      case t : Pred  =>{
        println(t.toString + "_"+value)
        model(t.args) = value
        fund(t) = value
        val listed = model.toList
        if(listed.exists({case(te,va) => (va != value) && areUnifiable(te,t.args)})){
          println("⊥")
          proof.methodFail = true
          proof.result = Nil
          return
        }else{
          proof.addResult(fund.toList)
        }
      }
      case _ =>
    }

  }

  def freeVariableTableaux(form : FirstOrder.Formula) = {

    val model = new mutable.HashMap[List[Term],Boolean]()
    val fund = new mutable.HashMap[FirstOrder.Formula,Boolean]()
    val proof = new Proof()
    freeVariableTableauxRoutine(form.translate(),model,true,fund, proof)
    proof.result
  }

}
