package main.scala.FirstOrder

import main.scala._

import scala.collection.immutable.{List, Map, Set}

/**
 * Created by enxhi on 10/25/14.
 */
// Problem 5
class Model(univ : List[String],
            atoms : Map[String, Boolean],
            preds : Map[String, Set[List[String]]],
            vars : Map[String, String],
            cons : Map[String, String],
            funcs : Map[String, Map[List[String], String]]) {
  require(preds.values.flatten.flatten.forall(univ.contains), "predicate interpretation args must be from the universe")
  require(vars.values.forall(univ.contains), "variables interpretation must be from the universe")
  require(cons.values.forall(univ.contains), "constants interpretation must be from the universe")
  require(funcs.values.flatten.map(p => p._2 :: p._1).flatten.forall(univ.contains), "function interpretation args must be from the universe")

  def wff(sig : Signature) : Boolean = {
    val pv = preds forall {p =>
      val (name, pdef) = p
      sig.preds.isDefinedAt(name) && {
        pdef forall {args =>
          sig.preds(name) == args.size
        }
      }
    }
    val fv =  funcs forall {p =>
      val (name, fdef) = p
      sig.funcs.isDefinedAt(name) && {
        fdef forall {p2 =>
          val (args, result) = p2
          args.length == sig.funcs(name)
        }
      }
    }
    pv && fv
  }


  private def evaluateRoutine(term : Term) : String = term match{
    case Variable(name) => vars(name)
    case Constant(name) => cons(name)
    case Func(name,args) => funcs(name)(args map(x => evaluateRoutine(x)))
  }

  private def evaluateRoutine(pred : FirstOrder.Formula) : Boolean = pred match{
    case a : Atom => atoms(a.name)
    case Pred(name,args) => preds.get(name) match {
      case None => throw new Error("Ill formed")
      case Some(a) => a.toList contains args
    }
    case Neg(f) => !evaluateRoutine(f)
    case Equiv(l,r) => evaluateRoutine(l) == evaluateRoutine(r)
    case Conj(l,r) => evaluateRoutine(l) && evaluateRoutine(r)
    case Disj(l,r) => evaluateRoutine(l) || evaluateRoutine(r)
    case Impl(l,r) => if(evaluateRoutine(l)) evaluateRoutine(r) else true
    case Forall(context, b)  => throw new Error("PLNQ only. Not supported yet!")
    case Exists(context, b)  => throw new Error("PLNQ only. Not supported yet!")
    case Equality(l,r) => evaluateRoutine(r).equals(evaluateRoutine(l))
  }

  def evaluate(pred : FirstOrder.Formula,sig : Signature, con : Context) : Boolean = {
    require(!pred.wff(sig,con))
    evaluateRoutine(pred)
  }
}
