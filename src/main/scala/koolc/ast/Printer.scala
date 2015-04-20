package koolc
package ast

import utils._
import Trees._

object Printer {
  def apply(t: Program): String = {

  	var indent = "  "
  	var level = 0
    var result = new StringBuilder

    //main part
    printMainOb(t.main)
    for(decl <- t.classes)
 		printClassDecl(decl)


    def pfx(i : Int, str : String) {
    	level = level+i
    	result ++= indent*level + str
    }
    def end(i: Int, str: String){
    	result ++= str + "\n"
    	level = level +i
    }

    def add(i: Int, str: String, j: Int){
    	pfx(i,str)
    	end(j, "")
    }



    def printMainOb(main: Trees.MainObject){
    	add(0, "object "+ main.id.value + "#" +main.id.getSymbol.id +" {", 1)
    	add(0, "def main() : Unit = {", 1)
    	for(stat <- main.stats) printStat(stat)
    	add(-1, "}", 0)
    	add(-1, "}", 0)

    }

    def printClassDecl(classDecl : Trees.ClassDecl){
    	val par = classDecl.parent match {
    		case Some(id) => " extends " + id.value + "#" +id.getSymbol.id
    		case None => ""
    	}
    	add(0, "\nclass " + classDecl.id.value + "#" + classDecl.getSymbol.id+ par + " {" ,1)
    	for(va <- classDecl.vars) printVarDecl(va)
    	for(m <- classDecl.methods) printMethodDecl(m)
    	add(-1, "}", 0)
    }

 	def printType(tpe: TypeTree){
 		tpe match{
 			case IntType()=>{
 				result ++= "Int"
 			}
 			case BooleanType() => {
 				result ++= "Bool"
 			}
 			case StringType() => {
 				result ++= "String"
 			}
 			case IntArrayType() =>{
 				result ++= "Int[]"
 			}
 			case x:Identifier => {
 				result ++= x.value + "#" + x.getSymbol.id
 			}
 		}
 	}
    def printVarDecl(v: Trees.VarDecl){
    	pfx(0, "var " + v.id.value + "#" +v.id.getSymbol.id +" : ")
    	printType(v.tpe)
    	end(0, ";")
    }
    
    def printMethodDecl(m: Trees.MethodDecl){
    	pfx(0, "def " + m.id.value + "#" + m.id.getSymbol.id +"(")
    	var first = true
    	for(arg <- m.args){
    		if(!first){
    			result ++= ", "
    		}else first = false
    		result ++= arg.id.value + "#" + arg.id.getSymbol.id + " : "
    		printType(arg.tpe)
    	}


    	result ++= ") : "
		printType(m.retType)
		end(1, " = {")
		for(v <- m.vars)
			printVarDecl(v)
		for(s <- m.stats)
			printStat(s)
		pfx(0, "return ")
		printExpr(m.retExpr)
		end(0, ";")
		add(-1, "}", 0)
	}
    


    

    def printStat(stat: Trees.StatTree){
    	stat match{
    		case Block(stats) => {
    			add(0, "{", 1)
    			for(s <- stats) printStat(s)
    			add(-1, "}", 0)

    		}
    		case If(expr, thn, els) => {
    			pfx(0, "if (" )
    			printExpr(expr)
    			end(1, ")")
    			printStat(thn)
    			els match {
    				case Some(s) => {
    					add(-1, "else", 1)
    					printStat(s)
    				}
    				case None => {}
    			}
    			level = level-1

    		}
    		case While(expr, stat) => {
    			pfx(0, "while (")
    			printExpr(expr)
    			end(1, ")")
    			printStat(stat)
    			level = level -1
    		}
    		case Println(expr) => {
    			pfx(0, "println(")
    			printExpr(expr)
    			end(0, ");")
    		}
    		case Assign(id, expr) => {
    			pfx(0, id.value + "#" +id.getSymbol.id + " = ")
    			printExpr(expr)
    			end(0, ";")
    		}
    		case ArrayAssign(id, index, expr) => {
    			pfx(0, id.value + "#" + id.getSymbol.id+ "[")
    			printExpr(index)
    			result ++= "] = "
    			printExpr(expr)
    			end(0, ";")
    		}
    	}
    }

    def printExpr(expr : ExprTree){
    	printMinPrec(expr, 0)
    }

    object Prec extends Enumeration{
    	val Equals, Or, And, LessThan, Minus, Plus, Div, Times, Bang, Last = Value
    }

 
    def getPrec(expr: ExprTree): Int = {
    	expr match{
    		case And(_,_)	=> Prec.And.id
        	case Or(_, _)     => Prec.Or.id
        	case Equals(_, _) => Prec.Equals.id
        	case LessThan(_, _)   => Prec.LessThan.id
        	case Plus(_, _)    => Prec.Plus.id
        	case Minus(_, _)    => Prec.Minus.id
       	 	case Times(_, _)    => Prec.Times.id
        	case Div(_, _)    => Prec.Div.id
   			case _ 			=> -1

    	}
    }

    def printOper(expr: ExprTree, prec:Int){
    	val (lhs, rhs, str) = expr match{
            case And(lhs, rhs) => (lhs, rhs, "&&")
       	 	case Or(lhs, rhs) => (lhs, rhs, "||")
        	case Equals(lhs, rhs) => (lhs, rhs, "==")
        	case LessThan(lhs, rhs) => (lhs, rhs, "<")
        	case Plus(lhs, rhs) => (lhs, rhs, "+")
        	case Minus(lhs, rhs) => (lhs, rhs, "-")
        	case Times(lhs, rhs) => (lhs, rhs, "*")
        	case Div(lhs, rhs) => (lhs, rhs, "/")
        	case _				=> (null, null, null)
    	}
    	printMinPrec(lhs, prec)
    	result ++= " " + str + " "
    	printMinPrec(rhs, prec+1)
    }
    

    def printMinPrec(expr: ExprTree, min: Int){
    	val prec = getPrec(expr)
    	if(prec >= 0){
    		if(prec < min){
    			result ++= "("
    			printOper(expr, prec)
    			result ++= ")"
    		}
    		else
    			printOper(expr, prec)
    	}
    	else{
    		expr match{
    			case value:Identifier => {
                    result ++= value.value + "#" + value.getSymbol.id 
                }
    			case IntLit(value)		=> {result ++= value.toString}
    			case StringLit(value)	=> {result ++= '"' + value + '"'}
    			case True()				=> {result ++= "true"}
    			case False()			=> {result ++= "false"}
    			case thi :This				=> {result ++= "this" + "#" + thi.getSymbol.id}
    			case ArrayRead(arr, index)	=> {printMinPrec(arr, Prec.Last.id); result ++= "["; printExpr(index); result ++= "]"}
    			case ArrayLength(arr)	=> {printMinPrec(arr, Prec.Last.id); result ++= ".length"}
    			case MethodCall(obj, meth, args)	=> {printMinPrec(obj, Prec.Last.id); 
    													result ++= "." + meth.value + "#??" +"("; 
    													var first = true
    													for(m <- args){
    														if(!first){
    														result ++= ", "
    														}else first = false
    														printExpr(m);
    													}
    													result ++= ")";
    													}
    			case New(tpe)			=> {result ++= "new "+ tpe.value + "#" + tpe.getSymbol.id+"()"}
    			case Not(expr)			=> {result ++= "!"; printMinPrec(expr, Prec.Last.id)}
    			case NewIntArray(size)	=> {result ++= "new Int["; printMinPrec(size, Prec.Last.id); result ++= "]"}
    			case _ => None
    		}
    	}
    }
 	









    result.toString

  }
}
