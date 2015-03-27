package koolc
package lexer

import utils._
import scala.io.Source
import java.io.File

object Lexer extends Pipeline[File, Iterator[Token]] {
  import Tokens._

  def run(ctx: Context)(f: File): Iterator[Token] = {
    val source = Source.fromFile(f)
    import ctx.reporter._

    new Iterator[Token] {

    var curChar : Char = ' '
    var skip = false
    var eof = false

    def checkNextChar : Char= {
      skip = true
      if(source.hasNext) curChar = source.next
      else{
        curChar = '\u0000'
      }
      curChar
    }

    def checkCommentEnd : Boolean= {
            val nextChar = checkNextChar
            if(nextChar != '\u0000' && nextChar != '\n') true
            else false
          }
    def decideToken(ch : Char) = {
      ch match {

        case _ if ch.isWhitespace => {
          next
        }
        
        case '=' if checkNextChar == '=' => {
          skip = false
          new Token (Tokens.EQUALS)
        }
        case ':' => new Token (Tokens.COLON)
        case ';' => new Token (Tokens.SEMICOLON)
        case '.' => new Token (Tokens.DOT)
        case ',' => new Token (Tokens.COMMA)
        case '=' => new Token (Tokens.EQSIGN)
        case '!' => new Token (Tokens.BANG)
        case '(' => new Token (Tokens.LPAREN)
        case ')' => new Token (Tokens.RPAREN)
        case '[' => new Token (Tokens.LBRACKET)
        case ']' => new Token (Tokens.RBRACKET)
        case '{' => new Token (Tokens.LBRACE)
        case '}' => new Token (Tokens.RBRACE)
        case '<' => new Token (Tokens.LESSTHAN)
        case '+' => new Token (Tokens.PLUS)
        case '-' => new Token (Tokens.MINUS)
        case '*' => new Token (Tokens.TIMES)


        case '&' if checkNextChar == '&' => { 
          skip = false
          new Token (Tokens.AND) 
        }
        case '|' if checkNextChar == '|' => { 
          skip = false
          new Token (Tokens.OR) 
        }
        case '/' if checkNextChar == '/' => {
          skip = false
          while (checkCommentEnd) {}
          next
        }
        case '/' if curChar == '*' => {
          skip = false

          val checkNestedCommentEnd : Boolean = {
            var result = false
            checkNextChar
            while(result != true && curChar != '\u0000'){
              if(curChar == '*'){
                if(checkNextChar == '/') {
                  result = true

                }
              }
              else checkNextChar
            }
            result
          }
          val a = checkNestedCommentEnd
          if (a){
            skip = false
            next
          }
          else new Token (Tokens.BAD)
        }
        case '/' => new Token(Tokens.DIV)

        case '"' => {
          var word = ""
          while(checkNextChar != '"'){
            word += curChar
          }
          skip = false
          new Tokens.STRLIT (word)
        }

        case _ if ch.isLetter => {
          val word = {
            var result = "" + ch
            while(checkNextChar.isLetterOrDigit || curChar == '_'){
             result += curChar
             skip = false
            }
            result
          }

          word match {
            case "object" => new Token (Tokens.OBJECT)
            case "class" => new Token (Tokens.CLASS)
            case "def" => new Token (Tokens.DEF)
            case "var" => new Token (Tokens.VAR)
            case "Unit" => new Token (Tokens.UNIT)
            case "main" => new Token (Tokens.MAIN)
            case "String" => new Token (Tokens.STRING)
            case "extends" => new Token (Tokens.EXTENDS)
            case "Int" => new Token (Tokens.INT)
            case "Bool" => new Token (Tokens.BOOLEAN)
            case "while" => new Token (Tokens.WHILE)
            case "if" => new Token (Tokens.IF)
            case "else" => new Token (Tokens.ELSE)
            case "return" => new Token (Tokens.RETURN)
            case "length" => new Token (Tokens.LENGTH)
            case "true" => new Token (Tokens.TRUE)
            case "false" => new Token (Tokens.FALSE)
            case "this" => new Token (Tokens.THIS)
            case "new" => new Token (Tokens.NEW)
            case "println" => new Token (Tokens.PRINTLN)
            case _ => new Tokens.ID (word)
          }
        }
        case _ if ch.isDigit => {
          val word = {
            var result = "" + ch
            while(checkNextChar.isLetterOrDigit){
             result += curChar
             skip = false
            }
            result
          }
          try {
            var parsedInt = word.toInt
            new Tokens.INTLIT (parsedInt)
          } catch {
            case e:NumberFormatException => new Token (Tokens.BAD)
          }
        }
        case _ if ch == '\u0000' => {
          eof = true
          new Token(Tokens.EOF)
        }
        case _ => {
          new Token (Tokens.BAD)
        }
      }
    }

      def hasNext = !eof

      def next = {

        var result = new Token(Tokens.BAD)

        if(eof) throw new NoSuchElementException("Reached end")

        if(!skip){ 
          if(source.hasNext) curChar = source.next
          else{
            curChar = '\u0000'
          }
        }
        else{
          skip = false
        }

        result = decideToken(curChar).setPos(f, source.pos)

        result

      }
    }

  }
}
