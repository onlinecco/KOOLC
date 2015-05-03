package koolc
package ast

import utils._
import Trees._
import lexer._
import lexer.Tokens._

object Parser extends Pipeline[Iterator[Token], Program] {
  def run(ctx: Context)(tokens: Iterator[Token]): Program = {
    import ctx.reporter._
    def precedenceLevels(kind: TokenKind) :Int = {
      kind match{
        case Tokens.OR => 0
        case Tokens.AND => 1
        case Tokens.EQUALS => 2
        case Tokens.LESSTHAN => 2 
        case Tokens.MINUS => 3
        case Tokens.PLUS => 3
        case Tokens.DIV => 4
        case Tokens.TIMES => 4
        case Tokens.BANG => 5
        case _ => -1
      }
    }
    /** Store the current token, as read from the lexer. */
    var currentToken: Token = new Token(BAD)

    def readToken: Unit = {
      if (tokens.hasNext) {
        // uses nextToken from the Lexer trait
        currentToken = tokens.next

        // skips bad tokens
        while (currentToken.kind == BAD) {
          currentToken = tokens.next
        }
      }
    }

    /** ''Eats'' the expected token, or terminates with an error. */
    def eat(kind: TokenKind): Unit = {
      if (currentToken.kind == kind) {
        readToken
      } else {
        expected(kind)
      }
    }

    /** Complains that what was found was not expected. The method accepts arbitrarily many arguments of type TokenKind */
    def expected(kind: TokenKind, more: TokenKind*): Nothing = {
      fatal("expected: " + (kind::more.toList).mkString(" or ") + ", found: " + currentToken, currentToken)
    }

    def expect(kind: TokenKind)= {
      if (currentToken.kind == kind) {
        val oldToken = currentToken
        readToken
        oldToken
      } else {
        expected(kind)
      }
    }

    def expectId : Identifier = {
      val tok = currentToken
      (new Identifier(expect(Tokens.IDKIND).asInstanceOf[Tokens.ID].value)).setPos(tok)
    }

    def first(kind: Tree) : Set[TokenKind] = {

      kind match {

        case ClassDecl(_,_,_,_) => Set(Tokens.CLASS)
        case VarDecl(_,_) => Set(Tokens.VAR)
        case MethodDecl(_,_,_,_,_,_) => Set(Tokens.DEF)
        case Block(_) => Set(Tokens.LBRACE, Tokens.IF, Tokens.WHILE, Tokens.PRINTLN, Tokens.IDKIND)
        case _ => null
        //case And(_,_) => Set(Tokens.INTLITKIND, Tokens.STRLITKIND, Tokens.TRUE, Tokens.FALSE, Tokens.IDKIND, Tokens.THIS, Tokens.NEW, Tokens.BANG, Tokens.LPAREN)

      }

    }
    def parseRecursive[T] (cl: Tree,func : ()=>T) : List[T] = {
      if(first(cl) contains currentToken.kind) func() :: parseRecursive(cl, func) else Nil
    }

    def parseBlock : Block = {
      val tok = currentToken
      eat(Tokens.LBRACE)
      val block = parseRecursive(Block(null),()=>parseStatement)
      eat(Tokens.RBRACE)
      (new Block(block)).setPos(tok)
    }

    def parseMainObject : MainObject = {
      val tok = currentToken
      eat(Tokens.OBJECT)
      val id = expectId
      eat(Tokens.LBRACE)
      eat(Tokens.DEF)
      eat(Tokens.MAIN)
      eat(Tokens.LPAREN)
      eat(Tokens.RPAREN)
      eat(Tokens.COLON)
      eat(Tokens.UNIT)
      eat(Tokens.EQSIGN)
      val block = parseBlock
      eat(Tokens.RBRACE)

      (new MainObject(id,block.stats)).setPos(tok)
    }

    def parseClassDeclaration : ClassDecl = {
      val tok = currentToken
      eat(Tokens.CLASS)
      val id1 = expectId
      val ext = if(currentToken.kind == Tokens.EXTENDS) {
        readToken
        Some(expectId)
      }
        else None
      

      eat(Tokens.LBRACE)
      val varDecs = parseRecursive(VarDecl(null,null),()=>parseVarDeclaration)
      val medDecs = parseRecursive(MethodDecl(null,null,null,null,null,null),()=>parseMethodDeclaration)
      eat(Tokens.RBRACE)

      (new ClassDecl(id1,ext,varDecs, medDecs)).setPos(tok)
    }

    def parseType = {
      val tok = currentToken
      currentToken.kind match {

        case Tokens.IDKIND => expectId
        case Tokens.INT =>{
          val check = {
            readToken
            if(currentToken.kind == Tokens.LBRACKET){
              readToken
              if(currentToken.kind == Tokens.RBRACKET){
                readToken
                true
              }
            else
            {
              readToken
              error("Missing right bracket")
              false //or fatal
            }
            }
            else false
          }

          if(check) {
            (new IntArrayType()).setPos(tok)
          }
          else{
            (new IntType()).setPos(tok)
          }
        } 
        case Tokens.BOOLEAN =>{
          readToken
         (new BooleanType()).setPos(tok)
       }
        case Tokens.STRING =>{
          readToken
         (new StringType()).setPos(tok)
       }
        case _ => {
          readToken
          error("No such Type " + currentToken.kind)
          null
        }

      }
    }
    def parseVarDeclaration : VarDecl = {
      val tok = currentToken
      eat(Tokens.VAR)
      val id = expectId
      eat(Tokens.COLON)
      val type1 = parseType
      eat(Tokens.SEMICOLON)

      (new VarDecl(type1, id)).setPos(tok)

    }

    def parseMethodFormal : List[Formal] = {

      if(currentToken.kind == Tokens.COMMA){
        readToken
        val tok = currentToken
        val id = expectId
        eat(Tokens.COLON)
        val type3 = parseType
        (new Formal(type3,id)).setPos(tok) :: parseMethodFormal

      }
      else Nil

    }
    def parseMethodDeclaration : MethodDecl = {
        val tok = currentToken
        eat(Tokens.DEF)
        val id = expectId
        var list1 : List[Formal] = Nil
        eat(Tokens.LPAREN)
        val para = if(currentToken.kind == Tokens.RPAREN){
            Nil
          }
          else{
            val tok2 = currentToken
            val id = expectId
            eat(Tokens.COLON)
            val type2 = parseType
            list1 = List((new Formal(type2, id)).setPos(tok2))
            if(currentToken.kind == Tokens.COMMA){
              list1 = list1 ::: parseMethodFormal
            }
            list1
          }
        
        eat(Tokens.RPAREN)
        eat(Tokens.COLON)
        val returnType = parseType
        eat(Tokens.EQSIGN)
        eat(Tokens.LBRACE)
        val varD = parseRecursive(VarDecl(null,null),()=>parseVarDeclaration)
        val stat = parseRecursive(Block(null),()=>parseStatement)
        eat(Tokens.RETURN)
        val exp = parseExpression
        eat(Tokens.SEMICOLON)
        eat(Tokens.RBRACE)

        (new MethodDecl(returnType, id, list1, varD,stat,exp)).setPos(tok)
    }

    def parseStatement : StatTree= {
      val tok = currentToken
      currentToken.kind match {
        case Tokens.WHILE => {
          eat(Tokens.WHILE)
          eat(Tokens.LPAREN)
          val cond = parseExpression
          eat(Tokens.RPAREN)
          val then1 = parseStatement

          (new While(cond,then1)).setPos(tok)
        }
        case Tokens.PRINTLN => {
          eat(Tokens.PRINTLN)
          eat(Tokens.LPAREN)
          val para = parseExpression
          eat(Tokens.RPAREN)
          eat(Tokens.SEMICOLON)

          (new Println(para)).setPos(tok)
        }
        case Tokens.LBRACE => parseBlock
        case Tokens.IF => {

          eat(Tokens.IF)
          eat(Tokens.LPAREN)
          val cond = parseExpression
          eat(Tokens.RPAREN)
          val then1 = parseStatement

          val elsec = if(currentToken.kind == Tokens.ELSE){
            readToken
            Some(parseStatement)
          }
          else None

          (new If(cond, then1, elsec)).setPos(tok)
        }

        case Tokens.IDKIND => {
          val id = expectId
          currentToken.kind match {
            case Tokens.EQSIGN => {
              readToken
              val exp = parseExpression
              eat(Tokens.SEMICOLON)
              (new Assign(id,exp)).setPos(tok)
            }
            case Tokens.LBRACKET => {
              readToken
              val index = parseExpression
              eat(Tokens.RBRACKET)
              eat(Tokens.EQSIGN)
              val exp = parseExpression
              eat(Tokens.SEMICOLON)
              (new ArrayAssign(id,index,exp)).setPos(tok)

            }
            case _ =>{ 
              readToken
              error("BROKEN ID clause")
              null
          }
          }
        }
        case _ => null
      }
    }

    def parseExpression : ExprTree = {
      parseExpressionPrecedence(0)
    }
    def parseExpressionPrecedence(level: Int) : ExprTree = {
      val tok = currentToken
      var lhs = parseSimpleExpression

      var canParseMore = true
      while (canParseMore) {
        //println(currentToken.kind + "'s level: " + precedenceLevels(currentToken.kind)+" , current lvl: " + level)
        lhs = currentToken.kind match {

          case t if (precedenceLevels(t) >= level) => {

            readToken

            val rhs = parseExpressionPrecedence(precedenceLevels(t)+1)

            t match {
              case Tokens.BANG     => (new Not(rhs)).setPos(tok)
              case Tokens.AND      => (new And (lhs, rhs)).setPos(tok)
              case Tokens.OR       => (new Or  (lhs, rhs)).setPos(tok)
              case Tokens.EQUALS   => (new Equals (lhs, rhs)).setPos(tok)
              case Tokens.LESSTHAN => (new LessThan (lhs, rhs)).setPos(tok)
              case Tokens.PLUS     => (new Plus (lhs, rhs)).setPos(tok)
              case Tokens.MINUS    => (new Minus (lhs, rhs)).setPos(tok)
              case Tokens.TIMES    => (new Times (lhs, rhs)).setPos(tok)
              case Tokens.DIV      => (new Div (lhs, rhs)).setPos(tok)

              case _ => {
                error("Error character" + t)
                null 
              }
            }
          }
          case Tokens.LBRACKET => {
            readToken
            val exp = parseExpression
            eat(Tokens.RBRACKET)
            (new ArrayRead(lhs,exp)).setPos(tok)
          }
          case Tokens.DOT => {
            readToken
            currentToken.kind match {
              case Tokens.LENGTH => {
                readToken
                (new ArrayLength(lhs)).setPos(tok)
              }
              case Tokens.IDKIND => {
                val id = expectId
                eat(Tokens.LPAREN)
                var list : List[ExprTree] = Nil
                if(currentToken.kind != Tokens.RPAREN){
                  list = parseExpression :: parseMoreExpression
                }
                eat(Tokens.RPAREN)
                (new MethodCall(lhs,id,list)).setPos(tok)
              }
            
              case _ => {
                readToken
                error("Wrong token following dot")
                null
              }
            }
          }
          case _ => {
            canParseMore = false
            lhs
          }
        }
      }
      lhs
    }

    def parseMoreExpression: List[ExprTree] = {
      if(currentToken.kind != Tokens.RPAREN){
        eat(Tokens.COMMA)
        parseExpression :: parseMoreExpression
      }
      else Nil
    }

    def parseSimpleExpression : ExprTree = {
      val tok = currentToken
      currentToken.kind match{
        case Tokens.INTLITKIND => {
           val str = currentToken.asInstanceOf[Tokens.INTLIT].value
          readToken
          (new IntLit(str)).setPos(tok)

        }
        case Tokens.STRLITKIND => {
          val str = currentToken.asInstanceOf[Tokens.STRLIT].value
          readToken
          (new StringLit(str)).setPos(tok)

        }
        case Tokens.TRUE => {
          readToken
          (new True).setPos(tok)
        }
        case Tokens.FALSE => {
          readToken
          (new False).setPos(tok)
        }
        case Tokens.IDKIND => {
          expectId

        }
        case Tokens.THIS => {
          readToken
          (new This).setPos(tok)
        }
        case Tokens.NEW => {
          readToken
          currentToken.kind match{
            case Tokens.INT => {
              readToken
              eat(Tokens.LBRACKET)
              val exp = parseExpression
              eat(Tokens.RBRACKET)
              (new NewIntArray(exp)).setPos(tok)
            }
            case Tokens.IDKIND => {
              val id = expectId
              eat(Tokens.LPAREN)
              eat(Tokens.RPAREN)
              (new New(id)).setPos(tok)
            }
            case _ => {
              error("Invalid New")
              null
            }
          }
        }
        case Tokens.LPAREN => {
          readToken
          val content = parseExpression
          eat(Tokens.RPAREN)
          content
        }
        case Tokens.BANG => null
        case _ => {
          
          error("NO LHS FOUND")
          null
        }
      }
    }
    def parseGoal: Program = {
      val tok = currentToken
      val main = parseMainObject
      val classL = parseRecursive(ClassDecl(null,null,null,null),()=>parseClassDeclaration)
      eat(Tokens.EOF)

      (new Program(main, classL)).setPos(tok)
    }

    readToken
    val tree = parseGoal
    terminateIfErrors
    tree
  }
}
