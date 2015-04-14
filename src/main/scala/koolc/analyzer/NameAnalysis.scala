package koolc
package analyzer

import utils._
import ast.Trees._
import Symbols._

object NameAnalysis extends Pipeline[Program, Program] {

  def run(ctx: Context)(prog: Program): Program = {
    import ctx.reporter._
    var globe = new GlobalScope

    def addClass(c : ClassDecl) : ClassSymbol = {

println("---class")
    	val name = c.id.value
    	var result = globe.lookupClass(name)

    	result match{
    		case Some(_) => error("a class is defined more than once", c)
    		case None => {
    			if (name == globe.mainClass.name)
    				error("a class uses the same name as the main object", c)
    			else{
    				var cla = new ClassSymbol(name)
    				c.setSymbol(cla)
    				result = Some(cla)
    				println("**Class added: " + name)
    				globe.classes += (name -> cla)
    			}
    		}
    	}
    	result.get
    } 

    def processClass(c : ClassDecl) : Unit= {
println("---processclass")
    	val sym = addClass(c)

    	c.parent match{
    		case Some(p) => {
    			globe.lookupClass(p.value) match{
    				case None => error("a class name is used as a symbol (as parent class or type, for instance) but is not declared", c)
    				case Some(_) => {
    					//TODO check for cycles
    					if(p.value == c.id.value)
    						error("the inheritance graph has a cycle",c)
    					else{
    					var parentMap = Map(c.id.value -> 0, p.value -> 0)
    					var cur = globe.lookupClass(p.value)
    					var break = false
    					while(!break){

    						cur.get.parent match {
    							case None => break = true
    							case Some(pp) => {
    								if(parentMap.get(pp.name) != None){
    									error("the inheritance graph has a cycle",c)
    									break = true
    								}
    								parentMap += (pp.name -> 0)
    								cur = globe.lookupClass(pp.name)
    							}
    						}

    					}
    					}
    				}
    			}
    		}
    		case None =>
    	}

    	c.vars.foreach(processVarInClass(_, sym))
    	c.methods.foreach(processMethodsInClass(_, sym))
    }

    def checkParentClassOverload(m : MethodSymbol, s : ClassSymbol) : Unit = {
println("---class")
    	if(s.parent != None){
    		s.parent.get.lookupMethod(m.name) match {
    			case Some(a) => {
    				if(m.argList.length != a.argList.length || !m.params.keySet.equals(a.params.keySet)){
    					error("a method overloads a method in its super class",m)
    				}
    			}
    			case None => {
    				//checkParentClassOverloadRecursive(m,s.parent)
    			}
    		}
    	}
    }

    def processMethodsInClass(m : MethodDecl, s : ClassSymbol) : Unit = {
    	var method = s.lookupMethod(m.id.value)
println("---method")
    	method match{

    		case Some(_) => error("a method overloads a method in the same class",m)
    		case None => {
    			var met = new MethodSymbol(m.id.value, s)
    			m.setSymbol(met)
    			s.methods += (m.id.value -> met)
    		}
    	}


    	//check overloading and overriding in super class
    	checkParentClassOverload(m.getSymbol,s)
    	println("args length: " + m.args.length)
    	m.args.foreach(processArgs(_,m.getSymbol))
    	m.vars.foreach(processVarsInMethod(_,m.getSymbol))
    	m.stats.foreach(processStat(_,m.getSymbol))
    	processExpr(m.retExpr,m.getSymbol)

    }

    def processArgs(a : Formal, m : MethodSymbol) : Unit = {
    	var elem = m.lookupVar(a.id.value)
println("---args")
    	elem match{

    		case Some(_) => error("two method arguments have the same name",a)
    		case None =>{
    			var p = new VariableSymbol(a.id.value)
    			a.setSymbol(p)
    			println(a+","+a.getSymbol)
    			m.params += (a.id.value -> p)
    			m.argList = p :: m.argList
    		}
    	}
    }

    def processVarsInMethod(v : VarDecl, m : MethodSymbol) : Unit = {
println("---varinmethod")
    	if(m.params.get(v.id.value) != None) error("a method argument is shadowed by a local variable declaration",v)
    	else{
    		var elem = m.lookupVar(v.id.value)

    		elem match{

    			case Some(_) => error("a variable is defined more than once",v)
    			case None =>{
    				var p = new VariableSymbol(v.id.value)
    				v.setSymbol(p)
   	 				m.members += (v.id.value -> p)
    			}
    		}
    	}
    }

    def processStat(s : StatTree, m : MethodSymbol) : Unit = {
println("---stat")
    	s match{

    		case Block(stats) => stats.foreach(processStat(_,m))
    		case If(expr, thn, els) => {
    			processExpr(expr,m)
    			processStat(thn,m)
    			if(els!= None) processStat(els.get,m)
    		}
    		case While(expr, stat) =>{
    			processExpr(expr,m)
    			processStat(stat,m)
    		}
    		case Println(expr) => processExpr(expr,m)
    		case Assign(id, expr) => {
    			//check if id is declared
    			checkId(id,m)
    			processExpr(expr,m)
    		}
    		case ArrayAssign(id, index, expr) => {
    			//check if id is declared
    			checkId(id,m)
    			processExpr(index,m)
    			processExpr(expr,m)
    		}
    	}
    }
    def checkId(id : Identifier, med : MethodSymbol) : Unit = {
println("---checkid")
    	val key = id.value
		if(med != null){


    	med.lookupVar(key) match {
    		case None => {
    			med.classSymbol.lookupVar(key) match {
    				case None => {
    					//looking for methods of current class
    					med.classSymbol.lookupMethod(key) match {
    						case Some(result5) => id.setSymbol(result5)
    						case None => {
    							//looking for vars of parent class
    							var p = med.classSymbol.parent
    							if(p!=None){
    								p.get.lookupVar(key) match {
    									case None => {
    										//looking for methods of parent class
    										p.get.lookupMethod(key) match{
    											case None => {
    					   							//looking for classes in globe
    					   							println(key)
    												globe.lookupClass(key) match{

    													case Some(result4) =>{
    														id.setSymbol(result4)
    													}
    													case None => error("an identifier "+ key +" is used as a variable but is not declared",id)
    												}
    											}
    											case Some(result6) =>{
    												id.setSymbol(result6)
    											} 
    										}
    									}
    									case Some(result3) =>{
    										id.setSymbol(result3)
   										}
   									}
   								}
    						}
    					}
    				}
    				case Some(result2) => id.setSymbol(result2)
    			}
    		}
    		case Some(result) => id.setSymbol(result)
    	}
    }else{
    	globe.lookupClass(key) match{
    		case Some(result4) => id.setSymbol(result4)
    		case None => error("an identifier "+ key +" is used as a class symbol but is not declared",id)
    	}
    }
    }

    def processExpr(expr : ExprTree, m : MethodSymbol) : Unit = {
println("---expr" + expr)

    	//TODO need to exclude method names
    	expr match {

    		case MethodCall(obj,meth,args) => {

    			processExpr(obj,m)
    			//can't check methods yet
    			//checkId(meth,m)
    			args.foreach(processExpr(_,m))
    		}
    		case And(lhs,rhs) => {
    			processExpr(lhs,m)
    			processExpr(rhs,m)
    		}
    		case Or(lhs,rhs) => {
    			processExpr(lhs,m)
    			processExpr(rhs,m)
    		}
    		case Plus(lhs,rhs) => {
    			processExpr(lhs,m)
    			processExpr(rhs,m)
    		}
    		case Minus(lhs,rhs) => {
    			processExpr(lhs,m)
    			processExpr(rhs,m)
    		}
    		case Times(lhs,rhs) => {
    			processExpr(lhs,m)
    			processExpr(rhs,m)
    		}
    		case Div(lhs,rhs) => {
    			processExpr(lhs,m)
    			processExpr(rhs,m)
    		}
    		case LessThan(lhs,rhs) => {
    			processExpr(lhs,m)
    			processExpr(rhs,m)
    		}
    		case Equals(lhs,rhs) => {
    			processExpr(lhs,m)
    			processExpr(rhs,m)
    		}
    		case ArrayRead(arr,index) => {
    			processExpr(arr,m)
    			processExpr(index,m)
    		}
    		case thi:This => {
    			thi.setSymbol(m.classSymbol)
    		}
    		case ArrayLength(arr) => {
    			processExpr(arr,m)
    		}
    		case New(tpe) => {
    			processExpr(tpe,m)
    		}
    		case NewIntArray(size) =>processExpr(size,m)
    		case Not(e) => {
    			processExpr(e,m)
    		}
    		case exp : Identifier => checkId(exp,m)
    		case _ =>

    	}

    }
    def processVarInClass(v : VarDecl, s : ClassSymbol) : Unit = {
println("---varinclass")

    	var elem = s.lookupVar(v.id.value)

    	elem match{
    		case Some(_) => error("a variable is defined more than once",v)
    		case None => {
    			checkParentVarOverload(v.id,s)
    			val va = new VariableSymbol(v.id.value)
    			v.setSymbol(va)
    			s.members += (v.id.value -> va)
    		}
    	}



    }

    def checkParentVarOverload(v : Identifier, s : ClassSymbol) : Unit = {
println("---parentvaroverload")
    	if(s.parent != None){
    		s.parent.get.lookupVar(v.value) match {
    			case Some(a) => {
    					error("a class member overloads a member in its super class",v)
    			}
    			case None => {
    			}
    		}
    	}
    }

    def collect = {

    	//Set the mainClass
    	val mainSym = new ClassSymbol(prog.main.id.value)
    	prog.main.id.setSymbol(new ClassSymbol(prog.main.id.value))
    	prog.main.setSymbol(mainSym)
    	globe.mainClass = mainSym
    	 	//Set the remainingClass
    	prog.classes.foreach(processClass(_))
    	prog.main.stats.foreach(processStat(_,null))
   
    }


    // Step 1: Collect symbols in declarations
    // Step 2: Attach symbols to identifiers (except method calls) in method bodies
    // (Step 3:) Print tree with symbol ids for debugging

    // Make sure you check for all constraints
    collect
    terminateIfErrors

    prog
  }
}
