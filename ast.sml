datatype binaryOperator =
     BOP_PLUS
   | BOP_MINUS
   | BOP_TIMES
   | BOP_DIVIDE
   | BOP_MOD
   | BOP_EQ
   | BOP_NE
   | BOP_LT
   | BOP_GT
   | BOP_LE
   | BOP_GE
   | BOP_AND
   | BOP_OR
   | BOP_COMMA
;

datatype unaryOperator =
     UOP_NOT
   | UOP_TYPEOF
   | UOP_MINUS
;

datatype declaration =
     DECL_ID of {id: string}
   | DECL_INIT of {id: string, src: expression}
and expression =
     EXP_ID of string
   | EXP_NUM of int
   | EXP_STRING of string
   | EXP_TRUE
   | EXP_FALSE
   | EXP_UNDEFINED
   | EXP_THIS
   | EXP_BINARY of {opr: binaryOperator, lft: expression, rht: expression}
   | EXP_UNARY of {opr: unaryOperator, opnd: expression}
   | EXP_COND of {guard: expression, thenExp: expression, elseExp: expression}
   | EXP_ASSIGN of {lhs: expression, rhs: expression}
   | EXP_CALL of {func: expression, args: expression list}
   | EXP_ANON of {params: string list, body: sourceElement list}
   | EXP_DOT of {lft: expression, id: string}
   | EXP_NEW of {ctorExp: expression, args: expression list}
   | EXP_OBJ of {props: {id:string, exp:expression} list}
and statement =
     ST_EXP of {exp: expression}
   | ST_BLOCK of {stmts: statement list}
   | ST_IF of {guard: expression, th: statement, el: statement}
   | ST_PRINT of {exp: expression}
   | ST_WHILE of {guard: expression, body: statement}
   | ST_RETURN of {exp: expression}
   | ST_GC
   | ST_INUSE
and sourceElement =
     STMT of {stmt: statement}
   | FUNC_DECL of {name: string, params: string list, body: sourceElement list}
   | VAR_DECL of {decls: declaration list}
;

datatype program =
  PROGRAM of {elems: sourceElement list}
;
