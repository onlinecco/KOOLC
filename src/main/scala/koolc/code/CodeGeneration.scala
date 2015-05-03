package koolc
package code

import ast.Trees._
import analyzer.Symbols._
import analyzer.Types._
import cafebabe._
import AbstractByteCodes.{New => _, _}
import ByteCodes._
import utils._

object CodeGeneration extends Pipeline[Program, Unit] {

  def run(ctx: Context)(prog: Program): Unit = {
    import ctx.reporter._

    var curClassSymbol : Option[ClassSymbol] = None 

    def generateArgsType(vs : VariableSymbol, acc : StringBuilder, l : List[VariableSymbol]) : List[VariableSymbol] = {
      acc.append(generateType(vs.getType))
      l :+ vs
    }

    def generateType(t : Type) : String = {

      t match {
          case TInt => "I"
          case TString => "Ljava/lang/String;"
          case TBoolean => "Z"
          case TIntArray => "[I"
          case TObject(o) => "L" + o.name +";"
          case _ => sys.error("Unkown Type for field: " + t)
        }
    }
    /** Writes the proper .class file in a given directory. An empty string for dir is equivalent to "./". */
    def generateClassFile(sourceName: String, ct: ClassDecl, dir: String): Unit = {

      curClassSymbol = Some(ct.getSymbol)

      val parent = ct.parent match{
        case None => None
        case Some(p) => Some(p.value)
      }
      val classFile = new ClassFile(ct.id.value , parent)
      classFile.setSourceFile(sourceName)

      //Generate fields
      def addField(v : VarDecl) : Unit = {
        val t = generateType(v.getSymbol.getType)
        val fh: FieldHandler = classFile.addField(t, v.id.value)
      }
      ct.vars.foreach(addField(_))
      //Generate methods
      def addMethod(med : MethodDecl) : Unit = {
        val retT = generateType(med.retType.getType)
        var para = new StringBuilder()
        var argList = List[VariableSymbol]()
        for(arg <- med.getSymbol.argList){
          argList = generateArgsType(arg,para,argList)
        }
        val mh: MethodHandler = classFile.addMethod(retT, med.id.value , para.toString())
        generateMethodCode(mh.codeHandler, med, argList)

      }
      ct.methods.foreach(addMethod(_))
      classFile.addDefaultConstructor
      classFile.writeToFile(dir+ct.id.value+".class")
    }

    def getVarPos(ch:CodeHandler,s : Symbol, vars : Map[VariableSymbol, Int], put : Boolean = false) : Unit = {
      s match {
        case v: VariableSymbol => {
          def putORget(className : String) : Unit = {
            if(put) ch << ArgLoad(0) << SWAP << PutField(className,v.name,generateType(v.getType))
            else ch << ArgLoad(0) << GetField(className,v.name,generateType(v.getType))
          }
          val slot = vars.get(v)
          slot match{
            case None => {

              curClassSymbol match{
                case None => sys.error("No such field")
                case Some(beautiful) => {
                  beautiful.members.exists(_._2 == v) match{
                    case true => putORget(beautiful.name)
                    case false => {
                      beautiful.parent match {
                        case None => sys.error("No such field")
                        case Some(b2) => {
                          b2.members.exists(_._2 == v) match {
                            case true => putORget(b2.name)
                            case false => sys.error("No such field")
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            case Some(i) => {
              v.getType match{
                case TInt | TBoolean if put => ch << IStore(i)
                case TIntArray | TString | TObject(_) if put => ch << AStore(i)
                case TInt | TBoolean => ch << ILoad(i)
                case TIntArray | TString | TObject(_) => ch << ALoad(i)
                case _ => sys.error("")
              }
            }
          }
        }
        //case c: classSymbol => 
        case _ => sys.error("Unkown symbol: "+ s.name)
      }


    }

      def generateMethodCall(ch:CodeHandler,obj: ExprTree, meth: Identifier,args:List[ExprTree],vars : Map[VariableSymbol, Int]) : Unit = {
        generateExpr(ch,obj,vars)

        var acc = new StringBuilder()
        acc.append("(")
        for(arg <- meth.getSymbol.asInstanceOf[MethodSymbol].argList){
          acc.append(generateType(arg.getType))
        }
        for(arg <- args){
          generateExpr(ch,arg,vars,true)
        }
        acc.append(")"+generateType(meth.getSymbol.getType))

        val objectName = obj.getType match{
          case TObject(c) => c.name
          case _ => sys.error("Method call on non-object type")
        }
        ch << InvokeVirtual(objectName, meth.value , acc.toString())
      }
      def generateExpr(ch:CodeHandler,e : ExprTree, vars : Map[VariableSymbol, Int], returnBool : Boolean = false) : Unit = {
        e match {
          case i : Identifier => {
            getVarPos(ch,i.getSymbol,vars)
            
          }
          case Plus(l,r) => {

            if(l.getType == TInt && r.getType == TInt){
            generateExpr(ch,l,vars,returnBool)
            generateExpr(ch,r,vars,returnBool)
            ch << IADD
            }
            else {
              val sb = "java/lang/StringBuilder"
              ch << DefaultNew(sb)
              generateExpr(ch,l,vars,returnBool)
              ch << InvokeVirtual(sb, "append", "(" + generateType(l.getType) + ")L" + sb + ";")
              generateExpr(ch,r,vars,returnBool)
              ch << InvokeVirtual(sb, "append", "(" + generateType(r.getType) + ")L" + sb + ";")
              ch << InvokeVirtual(sb, "toString", "()" + generateType(TString))
            }
          }
          case Minus(l,r) =>{
            generateExpr(ch,l,vars,returnBool)
            generateExpr(ch,r,vars,returnBool)
            ch << ISUB
          }
          case Times(l,r) =>{
            generateExpr(ch,l,vars,returnBool)
            generateExpr(ch,r,vars,returnBool)
            ch << IMUL
          }
          case Div(l,r) =>{
            generateExpr(ch,l,vars,returnBool)
            generateExpr(ch,r,vars,returnBool)
            ch << IDIV
          }
          case ArrayRead(arr,index) => {
            generateExpr(ch,arr,vars,returnBool)
            generateExpr(ch,index,vars,returnBool)
            ch << IALOAD
          }
          case ArrayLength(arr) => {
            generateExpr(ch,arr,vars,returnBool)
            ch << ARRAYLENGTH
          }
          case MethodCall(obj,meth,args)=> {
            generateMethodCall(ch,obj,meth,args,vars)
          }
          case IntLit(v) => ch << Ldc(v)
          case StringLit(v) => ch << Ldc(v)
          case This() => {
            ch << ALoad(0)
          }
          case NewIntArray(size) => {
            generateExpr(ch,size,vars,returnBool)
            ch << NewArray(10)
          }
          case New(expr) =>{
            ch << DefaultNew(expr.value) //MAYBE WRONG
          }
          case Not(x) => {
            val f = ch.getFreshLabel("false")
            val a = ch.getFreshLabel("after")
            generateExpr(ch,x,vars,returnBool)
            ch << IfNe(f) << Ldc(1) << Goto(a) << Label(f) << Ldc(0) << Label(a)
          }
          case And(l,r) => {
            val a = ch.getFreshLabel("after")
            val s = ch.getFreshLabel("second")
            val a2 = ch.getFreshLabel("after2")
            generateExpr(ch,l,vars,returnBool)
            ch << IfNe(s) << Goto(a) << Label(s)
            generateExpr(ch,r,vars,returnBool)
            ch << IfEq(a) << Ldc(1) << Goto(a2) << Label(a) << Ldc(0) << Label(a2)
          }
          case Or(l,r) =>{
            val t = ch.getFreshLabel("true")
            val a = ch.getFreshLabel("after")
            generateExpr(ch,l,vars,returnBool)
            ch << IfNe(t) << Ldc(0)
            generateExpr(ch,r,vars,returnBool)
            ch << IOR << Goto(a) << Label(t) << Ldc(1) << Label(a)
          }
          case True() => ch << Ldc(1)
          case False() => ch << Ldc(0)
          case LessThan(l,r) => {
            generateExpr(ch,l,vars,returnBool)
            generateExpr(ch,r,vars,returnBool)
            val t = ch.getFreshLabel("true")
            val f = ch.getFreshLabel("false")
            val a = ch.getFreshLabel("after")
            ch << If_ICmpLt(t) << Label(f) << Ldc(0) << Goto(a) << Label(t) << Ldc(1) << Label(a)
          }
          case Equals(l,r) => {

            generateExpr(ch,l,vars,returnBool)
            generateExpr(ch,r,vars,returnBool)
            val t = ch.getFreshLabel("true")
            val f = ch.getFreshLabel("false")
            val a = ch.getFreshLabel("after")
            
            l.getType match{
              case TIntArray | TString | TObject(_) =>ch << If_ACmpEq(t)
              case _ => ch << If_ICmpEq(t)
            }
            ch << Label(f) << Ldc(0) << Goto(a) << Label(t) << Ldc(1) << Label(a)
          }

          case _ => sys.error("Unkown Expression while genreating code." + e)

        }
      }
    def generateStat(ch: CodeHandler, s : StatTree, vars : Map[VariableSymbol, Int]) : Unit = {
      
      def branch(c : ExprTree, nTrue : String, nFalse : String) : Unit = {

        c match {
          case Not(x) => branch(x,nFalse,nTrue)
          case And(l,r) => {
            val n = ch.getFreshLabel("next")
            branch(l,n,nFalse)
            ch << Label(n)
            branch(r,nTrue,nFalse)
          }
          case Or(l,r) => {
            val n = ch.getFreshLabel("next")
            branch(l,nTrue,n)
            ch << Label(n)
            branch(r,nTrue,nFalse)
          }
          case True() => ch << Goto(nTrue)
          case False() => ch << Goto(nFalse)
          case i : Identifier => {
            getVarPos(ch,i.getSymbol,vars)
            ch <<  IfEq(nFalse) << Goto(nTrue)

          }
          case LessThan(l,r) =>{
            generateExpr(ch,l,vars)
            generateExpr(ch,r,vars)
            ch << If_ICmpLt(nTrue) << Goto(nFalse)
          }
          case Equals(l,r) => {
            //???object equal
            generateExpr(ch,l,vars)
            generateExpr(ch,r,vars)

            l.getType match{
              case TObject(_) =>ch << If_ACmpEq(nTrue) << Goto(nFalse)
              case _ => ch << If_ICmpEq(nTrue) << Goto(nFalse)
            }

          }
          case MethodCall(obj,meth,args)=> {
            generateMethodCall(ch,obj,meth,args,vars)
            ch << IfEq(nFalse) << Goto(nTrue)
          }

          case _ => sys.error("branch called for non-boolean type expression: " + c)
        }


      }

      s match{

          case Block(stats) => stats.foreach(generateStat(ch,_,vars))
          case If(expr, thn, els) => {

              val t = ch.getFreshLabel("then")
              val e = ch.getFreshLabel("else")
              val a = ch.getFreshLabel("after")
              branch(expr, t, e)

              ch << Label(t)
              generateStat(ch,thn,vars)
              ch << Goto(a) << Label(e)
              if(els!= None) generateStat(ch,els.get,vars)
              ch << Label(a)
          }
          case While(expr, stat) =>{
              val t = ch.getFreshLabel("test")
              val b = ch.getFreshLabel("body")
              val e = ch.getFreshLabel("exit")

              ch << Label(t)
              branch(expr, b, e)
              ch << Label(b)
              generateStat(ch,stat,vars)
              ch << Goto(t) << Label(e)
          }
          case Println(expr) => {
            ch << GetStatic("java/lang/System", "out", "Ljava/io/PrintStream;") 
            generateExpr(ch,expr,vars,true)
            ch << InvokeVirtual("java/io/PrintStream", "println", "("+generateType(expr.getType)+")V") 
          }
          case Assign(id, expr) => {
            //WRONG!!!!!
              generateExpr(ch,expr,vars,true)
              getVarPos(ch,id.getSymbol,vars,true)

          }
          case ArrayAssign(id, index, expr) => {
              generateExpr(ch,id,vars)
              generateExpr(ch,index,vars)
              generateExpr(ch,expr,vars)
              ch << IASTORE
          }
      }


    }
    // a mapping from variable symbols to positions in the local variables
    // of the stack frame
    def generateMethodCode(ch: CodeHandler, mt: MethodDecl, argList : List[VariableSymbol]): Unit = {
      val methSym = mt.getSymbol
      var vars = Map[VariableSymbol, Int]()

      for((arg,index) <- argList.zipWithIndex){
        val i = index + 1
        vars += (arg ->  i)
      }
      def generateMethodVar(tuple : (String, VariableSymbol) ) : Unit = {
        vars += (tuple._2 -> ch.getFreshVar)
      }
      methSym.members.foreach(generateMethodVar(_))

      mt.stats.foreach(generateStat(ch,_,vars))
      
      generateExpr(ch,mt.retExpr,vars, true)

      mt.retType.getType match{
        case TString | TIntArray | TObject(_) => ch << ARETURN
        case _ => ch << IRETURN
      }
      ch.freeze
    }

    def generateMainMethodCode(ch: CodeHandler, stmts: List[StatTree], cname: String): Unit = {

      curClassSymbol = None
      stmts.foreach(generateStat(ch,_,Map[VariableSymbol,Int]()))
      ch << RETURN
      ch.freeze
    }

    val outDir = ctx.outDir.map(_.getPath+"/").getOrElse("./")

    val f = new java.io.File(outDir)
    if (!f.exists()) {
      f.mkdir()
    }

    val sourceName = ctx.file.getName

    // output code
    prog.classes foreach {
      ct => generateClassFile(sourceName, ct, outDir)
    }

    val mainObject = new ClassFile(prog.main.id.value , None)
      mainObject.setSourceFile(sourceName)
    val mainHandler = mainObject.addMainMethod
    generateMainMethodCode(mainHandler.codeHandler,prog.main.stats, prog.main.id.value)
    mainObject.writeToFile(outDir+prog.main.id.value+".class")
    // Now do the main method
    // ...
  }

}
