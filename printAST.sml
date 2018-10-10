use "parser.sml";

fun out s = TextIO.output (TextIO.stdOut, s);

fun binaryOperatorString BOP_PLUS = "+"
  | binaryOperatorString BOP_MINUS = "-"
  | binaryOperatorString BOP_TIMES = "*"
  | binaryOperatorString BOP_DIVIDE = "/"
  | binaryOperatorString BOP_MOD = "%"
  | binaryOperatorString BOP_EQ = "=="
  | binaryOperatorString BOP_NE = "!="
  | binaryOperatorString BOP_LT = "<"
  | binaryOperatorString BOP_GT = ">"
  | binaryOperatorString BOP_LE = "<="
  | binaryOperatorString BOP_GE = ">="
  | binaryOperatorString BOP_AND = "&&"
  | binaryOperatorString BOP_OR = "||"
  | binaryOperatorString BOP_COMMA = ","
;

fun unaryOperatorString UOP_NOT = "!"
  | unaryOperatorString UOP_TYPEOF = "typeof "
  | unaryOperatorString UOP_MINUS = "-"
;

fun expressionString (EXP_ID s) = s
  | expressionString (EXP_NUM n) =
    if n < 0 then "-" ^ (Int.toString (~n)) else Int.toString n
  | expressionString (EXP_STRING s) = "\"" ^ (String.toString s) ^ "\""
  | expressionString EXP_TRUE = "true"
  | expressionString EXP_FALSE = "false"
  | expressionString EXP_UNDEFINED = "undefined"
  | expressionString EXP_THIS = "this"
  | expressionString (EXP_BINARY {opr, lft, rht}) =
   "(" ^
       (expressionString lft) ^
       " " ^ (binaryOperatorString opr) ^ " " ^
       (expressionString rht) ^
   ")"
  | expressionString (EXP_UNARY {opr, opnd}) =
   "(" ^
     (unaryOperatorString opr) ^ (expressionString opnd) ^
   ")"
  | expressionString (EXP_COND {guard, thenExp, elseExp}) =
   "(" ^
       (expressionString guard) ^
       " ? " ^
       (expressionString thenExp) ^
       " : " ^
       (expressionString elseExp) ^
   ")"
  | expressionString (EXP_ASSIGN {lhs, rhs}) =
   "(" ^
       (expressionString lhs) ^ " = " ^ (expressionString rhs) ^
   ")"
  | expressionString (EXP_CALL {func, args}) =
   (expressionString func) ^ "(" ^ (argumentsString args) ^ ")"
  | expressionString (EXP_ANON {params, body}) =
   "(" ^
      funcString (NONE) params body ^
   ")"
  | expressionString (EXP_DOT {lft, id}) =
   "(" ^ (expressionString lft) ^ "." ^ id ^ ")"
  | expressionString (EXP_NEW {ctorExp, args}) =
   "(new " ^
       (expressionString ctorExp) ^
       "(" ^ (argumentsString args) ^ ")" ^
   ")"
  | expressionString (EXP_OBJ {props}) =
   "{\n" ^ (propertiesString props) ^ "}"
and propertiesString [] = ""
  | propertiesString (prop::props) =
   (propertyString prop) ^
      (String.concat
         (List.map (fn prop => (", " ^ propertyString prop)) props))
and propertyString {id, exp} =
   id ^ ":" ^ (expressionString exp)
and argumentsString [] = ""
  | argumentsString (arg::args) =
   (expressionString arg) ^
       (String.concat (List.map (fn a => (", " ^ expressionString a)) args))

and statementString (ST_EXP {exp}) =
   (expressionString exp) ^ ";\n"
  | statementString (ST_BLOCK {stmts}) =
   "{\n" ^
      (String.concat (List.map statementString stmts)) ^
   "}\n"
  | statementString (ST_IF {guard, th, el}) =
   "if (" ^ (expressionString guard) ^ ")\n" ^
       (statementString th) ^
   "else\n" ^
       (statementString el)
  | statementString (ST_PRINT {exp}) =
   "print " ^ (expressionString exp) ^ ";\n"
  | statementString (ST_WHILE {guard, body}) =
   "while (" ^ (expressionString guard) ^ ")\n" ^
       (statementString body)
  | statementString (ST_RETURN {exp}) =
   "return " ^ (expressionString exp) ^ ";\n"
  | statementString ST_GC =
   "gc;\n"
  | statementString ST_INUSE =
   "inUse;\n"
    
and funcString name params body =
   "function " ^
    (case name of SOME id =>  id | NONE => "") ^
     "(" ^
       parametersString params ^
     ")\n" ^
     "{\n" ^
       sourceElementsString body ^
     "}\n"
and parametersString [] = ""
  | parametersString (param::params) =
   param ^ (String.concat (List.map (fn p => (", " ^ p)) params))
and declarationsString [] = ""
  | declarationsString (decl::decls) =
   (declString decl) ^
      (String.concat (List.map (fn d => (", " ^ (declString d))) decls))
and declString (DECL_ID {id}) = id
  | declString (DECL_INIT {id, src}) = id ^ " = " ^ (expressionString src)

and sourceElementString (STMT {stmt}) =
   statementString stmt
  | sourceElementString (FUNC_DECL {name, params, body}) =
   funcString (SOME name) params body
  | sourceElementString (VAR_DECL {decls}) =
   "var " ^ (declarationsString decls) ^ ";\n"
and sourceElementsString els =
   String.concat (List.map sourceElementString els)
;

fun printAST (PROGRAM {elems}) =
   out (sourceElementsString elems)
;
