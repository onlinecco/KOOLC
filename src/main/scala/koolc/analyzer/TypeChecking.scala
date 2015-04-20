package koolc
package analyzer

import ast.Trees._

import Symbols._
import Types._
import utils._

object TypeChecking extends Pipeline[Program, Program] {

  /** Typechecking does not produce a value, but has the side effect of
   * attaching types to trees and potentially outputting error messages. */
  def run(ctx: Context)(prog: Program): Program = {
    import ctx.reporter._
    var curClassType = Types.anyObject

    def getObjectSymbol(expr: ExprTree) : ClassSymbol = {
            expr match {

        case MethodCall(obj,meth,args) => {

          getObjectSymbol(obj)

        }
        
        case exp : Identifier => exp.getSymbol.asInstanceOf[ClassSymbol]
        case This() => curClassType.classSymbol
        case New(exp) => exp.getSymbol.asInstanceOf[ClassSymbol]
        case _ => sys.error("Uncaught object symbol")

      }
    }
    def tcExpr(expr: ExprTree, expected: Type*): Type = {
      val tpe: Type = { // TODO: Compute type for each kind of expression
        expr match{
          case MethodCall(obj,meth,args) => {

            if(!tcExpr(obj).isSubTypeOf(Types.anyObject)){
             error("Type Error: Undeclared object")
             TError
            }
            else{

            getObjectSymbol(obj) match{
                  case b: ClassSymbol => {
                    b.lookupMethod(meth.value) match {
                      case None => {
                        error("Type Error : Undeclared method " + meth.value)
                        TError
                      }
                      case Some(m) => {
                        if(args.length != m.argList.length){
                         error("Type Error: Incorrect number of arguments")
                         TError
                        }
                        else{
                          for( (arg1,arg2) <- m.argList zip args ){
                            if(!tcExpr(arg2).isSubTypeOf(arg1.getType)){
                             error("Type Error: Argument type does not match")
                             TError
                            }
                          }
                          val result = m.returnT match {
                            case IntArrayType() => TIntArray
                            case IntType() => TInt
                            case BooleanType() => TBoolean
                            case StringType() => TString
                            case i : Identifier => i.getType
                          }
                          expr.setType(result)
                          result
                        }
                      }
                    }
                  }

                  case _ => sys.error("Internal Error: Uncaught classsymbol")
                }
              
            }
          }
          case And(lhs,rhs) => {
            tcExpr(lhs)
            tcExpr(rhs)
            expr.setType(TBoolean)
            TBoolean
          }
          case Or(lhs,rhs) => {
            tcExpr(lhs)
            tcExpr(rhs)
            expr.setType(TBoolean)
            TBoolean
          }
          case Plus(lhs,rhs) => {

            var result = tcExpr(lhs) match {
              case TString => {
                tcExpr(rhs) match{
                  case TString => TString
                  case TInt => TString
                  case _ => {
                    error("Type Error: Unspported type of + operator")
                    TError
                  }
                }
              }
              case TInt => {
                tcExpr(rhs) match{
                  case TString => TString
                  case TInt => TInt
                  case _ => {
                    error("Type Error: Unspported type of + operator")
                    TError
                  }
                }

              }
              case _ => {
                error("Type Error: Unspported type of + operator")
                TError
              }
            }
            expr.setType(result)
            result

          }
          case Minus(lhs,rhs) => {
            tcExpr(lhs,TInt)
            tcExpr(rhs,TInt)
            expr.setType(TInt)
            TInt
          }
          case Times(lhs,rhs) => {
            tcExpr(lhs,TInt)
            tcExpr(rhs,TInt)
            expr.setType(TInt)
            TInt
          }
          case Div(lhs,rhs) => {
            tcExpr(lhs,TInt)
            tcExpr(rhs,TInt)
            expr.setType(TInt)
            TInt
          }
          case LessThan(lhs,rhs) => {
            tcExpr(lhs,TInt)
            tcExpr(rhs,TInt)
            expr.setType(TInt)
            TBoolean
          }
          case Equals(lhs,rhs) => {
            val tp1 = tcExpr(lhs)
            val tp2 = tcExpr(rhs)
            val result = tp1 match {
              case TInt if tp2.isSubTypeOf(TInt)=> TBoolean
              case TString if tp2.isSubTypeOf(TString) => TBoolean
              case TBoolean if tp2.isSubTypeOf(TBoolean) => TBoolean
              case TIntArray if tp2.isSubTypeOf(TIntArray) => TBoolean
              case TObject(_) if tp2.isSubTypeOf(Types.anyObject) => TBoolean
              case _ => {
                error("Type Error: Unspported type of == operator")
                TError
              }
            }
            expr.setType(result)
            TBoolean
          }
          case ArrayRead(arr,index) => {
            tcExpr(arr,TIntArray)
            tcExpr(index,TInt)
            expr.setType(TInt)
            TInt
          }
          case thi:This => {
            thi.setType(curClassType)
            curClassType
          }
          case ArrayLength(arr) => {
            tcExpr(arr,TIntArray)
            expr.setType(TInt)
            TInt
          }
          case IntLit(_) => {
            expr.setType(TInt)
            TInt
          }
          case StringLit(_) => {
            expr.setType(TString)
            TString
          }
          case True() => {
            expr.setType(TBoolean)
            TBoolean
          }
          case False() => {
            expr.setType(TBoolean)
            TBoolean
          }
          case New(tpe) => {
            val t = tcExpr(tpe)
            expr.setType(t)
            t
            
          }
          case NewIntArray(size) => {
            tcExpr(size,TInt)
            expr.setType(TIntArray)
            TIntArray
          }
          case Not(e) => {
            tcExpr(e)
            expr.setType(TBoolean)
            TBoolean
          }
          case exp : Identifier => {
            exp.getType
          }
          case _ => {
            error("Type error: Uncaught expression type")
            TError
          }
        }

      }
      // Check result and return a valid type in case of error
      if (expected.isEmpty) {
        tpe
      } else if (!expected.exists(e => tpe.isSubTypeOf(e))) {
        error("Type error: expected: " + expected.toList.mkString(" or ") + ", found: " + tpe, expr)
        expected.head
      } else {
        tpe
      }
    }

    def tcStat(stat : StatTree): Unit = {
      stat match{
        case Block(stats) => stats.foreach(tcStat(_))
        case If(expr,thn,els) => {
          tcExpr(expr, TBoolean)
          tcStat(thn)
          els match{
            case None =>
            case Some(e) => tcStat(e)
          }
        }
        case While(expr,stat) => {
          tcExpr(expr, TBoolean)
          tcStat(stat)
        }
        case Println(expr) => {
          tcExpr(expr) match {
            case TInt | TBoolean | TString =>
            case a => error("Type error: cannot use println on type " + a )
          }
        }
        case Assign(id,expr) => {

          if(!tcExpr(expr).isSubTypeOf(id.getType)) error("Type error: Invalid assignment", stat)
        }
        case ArrayAssign(id,index,expr) => {
          tcExpr(index,TInt)
          tcExpr(expr, TIntArray)
        }
        case _ => 
      }
    }

    def tcFormal(f : Formal): Unit = {

      f.tpe match{
        case IntArrayType() => f.id.getSymbol.setType(TIntArray)
        case IntType() => f.id.getSymbol.setType(TInt)
        case BooleanType() => f.id.getSymbol.setType(TBoolean)
        case StringType() => f.id.getSymbol.setType(TString)
        case i : Identifier => f.id.getSymbol.setType(i.getType)
        case _ => sys.error("Internal Error: Uncaught typetree")
      }

    }

    def installTypeOnReturn(ret : TypeTree) = {
      ret match{
        case IntArrayType() => ret.setType(TIntArray)
        case IntType() => ret.setType(TInt)
        case BooleanType() => ret.setType(TBoolean)
        case StringType() => ret.setType(TString)
        case i : Identifier => ret.setType(i.getType)
      }
    }
    def tcMethod(med : MethodDecl): Unit = {

      med.vars.foreach(tcVarDecl(_))
      med.stats.foreach(tcStat(_))
      installTypeOnReturn(med.retType)
      tcExpr(med.retExpr).isSubTypeOf(med.retType.getType)
      val m = med.getSymbol

      m.overridden match{
        case None =>
        case Some(m2) => {
          //check para types
          for((arg1,arg2) <- m.argList zip m2.argList){
            if(arg1.getType != arg2.getType) error("Type Error: parameters types of overriding methods do not match")
          }
          //TODO check return types

          if(m2.returnT.getType != med.retType.getType) error("Type Error: return types of overriding methods do not match")

        }
      }
        
      
    }

    def tcVarDecl(vard : VarDecl): Unit = {

      vard.tpe match{
        case IntArrayType() => vard.id.getSymbol.setType(TIntArray)
        case IntType() => vard.id.getSymbol.setType(TInt)
        case BooleanType() => vard.id.getSymbol.setType(TBoolean)
        case StringType() => vard.id.getSymbol.setType(TString)
        case i : Identifier => vard.id.getSymbol.setType(i.getType)
        case _ => sys.error("Internal Error: Uncaught typetree")
      }

    }
    def tcClass(cla : ClassDecl): Unit = {
      curClassType = new TObject(cla.getSymbol)
      cla.vars.foreach(tcVarDecl(_))
      cla.methods.foreach(tcMethod(_))

    }

    def installArgTypeMed(med: MethodDecl): Unit = {
      med.args.foreach(tcFormal(_))
    }
    def installArgTypeCla(cla: ClassDecl): Unit = {
      cla.methods.foreach(installArgTypeMed(_))
    }
    def tcProg : Unit = {
      //TODO MainObject
      prog.classes.foreach(installArgTypeCla(_))
      prog.classes.foreach(tcClass(_))
      prog.main.stats.foreach(tcStat(_))

    }

    tcProg
    prog
  }

}
