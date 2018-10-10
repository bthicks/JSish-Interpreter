open TextIO;

use "tokenizer.sml";
use "ast.sml";

fun err_expect want got =
   error ("expected '" ^ want ^ "', found '" ^ got ^"'\n")
;

fun someifyFirst (first, second) = (SOME first, second);

fun match_id fstr (TK_ID x) = (x, nextToken fstr)
  | match_id fstr tk = err_expect "identifier" (tkString tk)
;

fun match_num fstr (TK_NUM n) = (n, nextToken fstr)
  | match_num fstr tk = err_expect "number" (tkString tk)
;

fun match_string fstr (TK_STRING s) = (s, nextToken fstr)
  | match_string fstr tk = err_expect "string" (tkString tk)
;

fun match_tk fstr tk expected =
   if tk = expected
   then nextToken fstr
   else err_expect (tkString expected) (tkString tk)
;

fun match_eof fstr TK_EOF = TK_EOF
  | match_eof fstr tk = err_expect (tkString TK_EOF) (tkString tk)
;

fun findPair s xs = List.find (fn (st, _) => st = s) xs;
fun inOps tk ops = isSome (findPair tk ops);

val eqOps = [(TK_EQ, BOP_EQ), (TK_NE, BOP_NE)];
val relOps = [(TK_LT, BOP_LT), (TK_GT, BOP_GT), (TK_LE, BOP_LE),
   (TK_GE, BOP_GE)];
val addOps = [(TK_PLUS, BOP_PLUS), (TK_MINUS, BOP_MINUS)];
val multOps = [(TK_TIMES, BOP_TIMES), (TK_DIVIDE, BOP_DIVIDE),
   (TK_MOD, BOP_MOD)];
val unaryOps = [(TK_NOT, UOP_NOT), (TK_TYPEOF, UOP_TYPEOF),
   (TK_MINUS, UOP_MINUS)];
val andOps = [(TK_AND, BOP_AND)];
val orOps = [(TK_OR, BOP_OR)];
val commaOps = [(TK_COMMA, BOP_COMMA)];

fun opErrorMsgList [] strs= []
  | opErrorMsgList ((x, _)::[]) strs = (tkString x) :: strs
  | opErrorMsgList ((x, _)::(y, _)::[]) strs =
       (tkString y)::" or "::(tkString x) :: strs
  | opErrorMsgList ((x, _)::(y, _)::(z, _)::[]) strs =
      (tkString z)::", or "::(tkString y)::", "::(tkString x)::strs
  | opErrorMsgList ((x, _)::xs) strs =
      opErrorMsgList xs (", "::(tkString x)::strs)
;
fun opErrorMsg ops = foldl (op ^) "" (opErrorMsgList ops []);

fun isEqOp tk = inOps tk eqOps;
fun isRelOp tk = inOps tk relOps;
fun isAddOp tk = inOps tk addOps;
fun isMultOp tk = inOps tk multOps;
fun isUnaryOp tk = inOps tk unaryOps;
fun isAndOp tk = inOps tk andOps;
fun isOrOp tk = inOps tk orOps;
fun isCommaOp tk = inOps tk commaOps;

fun isExpression TK_LPAREN = true
  | isExpression (TK_ID _) = true
  | isExpression (TK_NUM _) = true
  | isExpression (TK_STRING _) = true
  | isExpression TK_TRUE = true
  | isExpression TK_FALSE = true
  | isExpression TK_UNDEFINED = true
  | isExpression TK_NOT = true
  | isExpression TK_TYPEOF = true
  | isExpression TK_MINUS = true
  | isExpression TK_FUNCTION = true
  | isExpression TK_NEW = true
  | isExpression TK_LBRACE = true
  | isExpression TK_THIS = true
  | isExpression _ = false
;

val isAssignmentExpression = isExpression;

fun isExpressionStatement tk =
   isExpression tk andalso not (tk = TK_FUNCTION) andalso not (tk = TK_LBRACE)
;

fun isValidLHS (EXP_ID _) = true
  | isValidLHS (EXP_DOT _) = true
  | isValidLHS _ = false
;

fun isStatement tk =
   tk = TK_LBRACE orelse tk = TK_IF orelse tk = TK_PRINT orelse
   tk = TK_WHILE orelse tk = TK_RETURN orelse tk = TK_GC orelse
   tk = TK_INUSE orelse isExpressionStatement tk
;

fun isSourceElement tk =
   isStatement tk orelse tk = TK_FUNCTION orelse tk = TK_VAR
;

fun parseRepetitionHelper fstr tk pred parse_single xs =
   if pred tk
   then
      let
         val (x, tk1) = parse_single fstr tk;
      in
         parseRepetitionHelper fstr tk1 pred parse_single (x::xs)
      end
   else
      (rev xs, tk)
;

fun parseRepetition fstr tk pred parse_single =
   parseRepetitionHelper fstr tk pred parse_single []
;

fun parseSeparatedSequence pred parse_sep parse_single fstr tk =
   let
      val (one, tk1) = parse_single fstr tk;
      val (more, tk2) =
         parseRepetition fstr tk1 pred
            (fn fstr => fn tk => parse_single fstr (parse_sep fstr tk))
   in
      (one::more, tk2)
   end
;

fun parseCommaSeparatedSequence parse_single fstr tk =
   parseSeparatedSequence
      (fn tk => tk = TK_COMMA)
      (fn fstr => fn tk => match_tk fstr tk TK_COMMA)
      parse_single
      fstr
      tk
;

(* expression parsing functions *)
fun parseOp fstr tk ops =
   case findPair tk ops of
      SOME (tk1, opr) => (opr, match_tk fstr tk tk1)
   |  NONE => err_expect (opErrorMsg ops) (tkString tk)
;
fun parseEqOp fstr tk = parseOp fstr tk eqOps;
fun parseRelOp fstr tk = parseOp fstr tk relOps;
fun parseAddOp fstr tk = parseOp fstr tk addOps;
fun parseMultOp fstr tk = parseOp fstr tk multOps;
fun parseUnaryOp fstr tk = parseOp fstr tk unaryOps;
fun parseAndOp fstr tk = parseOp fstr tk andOps;
fun parseOrOp fstr tk = parseOp fstr tk orOps;
fun parseCommaOp fstr tk = parseOp fstr tk commaOps;

fun parseBinaryExpLeft fstr tk parse_opnd is_opr parse_opr =
   let
      fun parseBinaryExpLeftH tk lft =
         if is_opr tk
         then
            let
               val (opr, tk1) = parse_opr fstr tk;
               val (rht, tk2) = parse_opnd fstr tk1;
            in
               parseBinaryExpLeftH tk2 (EXP_BINARY {opr=opr, lft=lft, rht=rht})
            end
         else (lft, tk)
      ;
      val (lft, tk1) = parse_opnd fstr tk;
   in
      parseBinaryExpLeftH tk1 lft
   end
;

fun parseParameterList fstr (tk as TK_ID _) =
   parseCommaSeparatedSequence match_id fstr tk
  | parseParameterList fstr tk = ([], tk)
;

fun parseExpression fstr tk =
   parseBinaryExpLeft fstr tk parseAssignmentExpression isCommaOp parseCommaOp
and parseAssignmentExpression fstr tk =
   (case parseConditionalExpression fstr tk of
      (lhs, TK_ASSIGN) =>
         if isValidLHS lhs
         then
            let
               val tk1 = match_tk fstr TK_ASSIGN TK_ASSIGN;
               val (rhs, tk2) = parseAssignmentExpression fstr tk1;
            in
               (EXP_ASSIGN {lhs=lhs, rhs=rhs}, tk2)
            end
         else error ("unexpected token '" ^ (tkString TK_ASSIGN) ^ "'\n")
   |  ret => ret
   )
and parseConditionalExpression fstr tk =
   (case parseLogicalOrExpression fstr tk of
      (guard, TK_QUESTION) =>
         let
            val tk1 = match_tk fstr TK_QUESTION TK_QUESTION;
            val (thenExp, tk2) = parseAssignmentExpression fstr tk1;
            val tk3 = match_tk fstr tk2 TK_COLON;
            val (elseExp, tk4) = parseAssignmentExpression fstr tk3;
         in
            (EXP_COND {guard=guard, thenExp=thenExp, elseExp=elseExp}, tk4)
         end
   |  ret => ret
   )
and parseLogicalOrExpression fstr tk =
   parseBinaryExpLeft fstr tk parseLogicalAndExpression isOrOp parseOrOp
and parseLogicalAndExpression fstr tk =
   parseBinaryExpLeft fstr tk parseEqualityExpression isAndOp parseAndOp
and parseEqualityExpression fstr tk =
   parseBinaryExpLeft fstr tk parseRelationalExpression isEqOp parseEqOp
and parseRelationalExpression fstr tk =
   parseBinaryExpLeft fstr tk parseAdditiveExpression isRelOp parseRelOp
and parseAdditiveExpression fstr tk =
   parseBinaryExpLeft fstr tk parseMultiplicativeExpression isAddOp parseAddOp
and parseMultiplicativeExpression fstr tk =
   parseBinaryExpLeft fstr tk parseUnaryExpression isMultOp parseMultOp
and parseUnaryExpression fstr tk =
   if isUnaryOp tk
   then
      let
         val (opr, tk1) = parseUnaryOp fstr tk;
         val (opnd, tk2) = parseLeftHandSideExpression fstr tk1;
      in
         (EXP_UNARY {opr=opr, opnd=opnd}, tk2)
      end
   else parseLeftHandSideExpression fstr tk
and parseLeftHandSideExpression fstr tk =
   parseCallExpression fstr tk
and parseCallExpression fstr tk =
   let
      val (func, tk1) = parseMemberExpression fstr tk;
   in
      parseOptionalArguments fstr tk1 func
   end
and parseMemberExpression fstr (tk as TK_NEW) =
   let
      val tk1 = match_tk fstr tk TK_NEW;
      val (exp, tk2) = parseMemberExpression fstr tk1;
      val (args, tk3) = parseArguments fstr tk2;
   in
      parseDotSequence fstr tk3 (EXP_NEW {ctorExp=exp, args=args})
   end
  | parseMemberExpression fstr tk =
   let
      val (exp, tk1) = parsePrimaryExpression fstr tk;
   in
      parseDotSequence fstr tk1 exp
   end
and parsePrimaryExpression fstr (tk as TK_LPAREN) =
   let
      val tk1 = match_tk fstr tk TK_LPAREN;
      val (exp, tk2) = parseExpression fstr tk1;
      val tk3 = match_tk fstr tk2 TK_RPAREN;
   in
      (exp, tk3)
   end
  | parsePrimaryExpression fstr (tk as TK_LBRACE) =
   let
      val tk1 = match_tk fstr tk TK_LBRACE;
      val (props, tk2) = parseOptionalPropertyAssignments fstr tk1;
      val tk3 = match_tk fstr tk2 TK_RBRACE;
   in
      (EXP_OBJ {props=props}, tk3)
   end
  | parsePrimaryExpression fstr (tk as TK_ID id) =
   (EXP_ID id, #2 (match_id fstr tk))
  | parsePrimaryExpression fstr (tk as TK_NUM n) =
   (EXP_NUM n, #2 (match_num fstr tk))
  | parsePrimaryExpression fstr (tk as TK_TRUE) =
   (EXP_TRUE, match_tk fstr tk TK_TRUE)
  | parsePrimaryExpression fstr (tk as TK_FALSE) =
   (EXP_FALSE, match_tk fstr tk TK_FALSE)
  | parsePrimaryExpression fstr (tk as TK_UNDEFINED) =
   (EXP_UNDEFINED, match_tk fstr tk TK_UNDEFINED)
  | parsePrimaryExpression fstr (tk as TK_STRING s) =
   (EXP_STRING s, #2 (match_string fstr tk))
  | parsePrimaryExpression fstr (tk as TK_FUNCTION) =
   let
      val tk1 = match_tk fstr tk TK_FUNCTION;
      val tk2 = match_tk fstr tk1 TK_LPAREN;
      val (params, tk3) = parseParameterList fstr tk2;
      val tk4 = match_tk fstr tk3 TK_RPAREN;
      val tk5 = match_tk fstr tk4 TK_LBRACE;
      val (body, tk6) = parseSourceElements fstr tk5;
      val tk7 = match_tk fstr tk6 TK_RBRACE;
   in
      (EXP_ANON {params=params, body=body}, tk7)
   end
  | parsePrimaryExpression fstr (tk as TK_THIS) =
   (EXP_THIS, match_tk fstr tk TK_THIS)
  | parsePrimaryExpression fstr tk =
   err_expect "value" (tkString tk)
and parseOptionalArguments fstr (tk as TK_LPAREN) func =
   let
      val (args, tk1) = parseArguments fstr tk;
   in
      parseOptionalIdArgs fstr tk1 (EXP_CALL {func=func, args=args})
   end
  | parseOptionalArguments fstr tk exp = (exp, tk)
and parseOptionalIdArgs fstr (tk as TK_LPAREN) func =
   let
      val (args, tk1) = parseArguments fstr tk;
   in
      parseOptionalIdArgs fstr tk1 (EXP_CALL {func=func, args=args})
   end
  | parseOptionalIdArgs fstr (tk as TK_DOT) exp =
   let
      val tk1 = match_tk fstr tk TK_DOT;
      val (id, tk2) = match_id fstr tk1;
   in
      parseOptionalIdArgs fstr tk2 (EXP_DOT {lft=exp, id=id})
   end
  | parseOptionalIdArgs fstr tk exp = (exp, tk)
and parseArguments fstr tk =
   let
      val tk1 = match_tk fstr tk TK_LPAREN;
      val (args, tk2) = parseArgumentList fstr tk1;
      val tk3 = match_tk fstr tk2 TK_RPAREN;
   in
      (args, tk3)
   end
and parseArgumentList fstr tk =
   if isAssignmentExpression tk
   then
      parseCommaSeparatedSequence parseAssignmentExpression fstr tk
   else
      ([], tk)
and parseDotSequence fstr (tk as TK_DOT) exp =
   let
      val tk1 = match_tk fstr tk TK_DOT;
      val (id, tk2) = match_id fstr tk1;
   in
      parseDotSequence fstr tk2 (EXP_DOT {lft=exp, id=id})
   end
  | parseDotSequence fstr tk exp =
   (exp, tk)
and parseOptionalPropertyAssignments fstr (tk as TK_ID _) =
   parseCommaSeparatedSequence parsePropertyAssignment fstr tk
  | parseOptionalPropertyAssignments fstr tk =
   ([], tk)
and parsePropertyAssignment fstr tk =
   let
      val (id, tk1) = match_id fstr tk;
      val tk2 = match_tk fstr tk1 TK_COLON;
      val (exp, tk3) = parseAssignmentExpression fstr tk2;
   in
      ({id=id, exp=exp}, tk3)
   end

(* statement parsing functions *)
and parseExpressionStatement fstr tk =
   let
      val (exp, tk1) = parseExpression fstr tk;
      val tk2 = match_tk fstr tk1 TK_SEMI;
   in
      (ST_EXP {exp=exp}, tk2)
   end

and parseStatement fstr (tk as TK_LBRACE) = parseBlockStatement fstr tk
  | parseStatement fstr (tk as TK_IF) = parseIfStatement fstr tk
  | parseStatement fstr (tk as TK_PRINT) = parsePrintStatement fstr tk
  | parseStatement fstr (tk as TK_WHILE) = parseWhileStatement fstr tk
  | parseStatement fstr (tk as TK_RETURN) = parseReturnStatement fstr tk
  | parseStatement fstr (tk as TK_GC) =
      (ST_GC, match_tk fstr (match_tk fstr TK_GC TK_GC) TK_SEMI)
  | parseStatement fstr (tk as TK_INUSE) = 
      (ST_INUSE, match_tk fstr (match_tk fstr TK_INUSE TK_INUSE) TK_SEMI)
  | parseStatement fstr tk =
   if isExpressionStatement tk
   then parseExpressionStatement fstr tk
   else err_expect "statement" (tkString tk)
and parseBlockStatement fstr tk =
   let
      val tk1 = match_tk fstr tk TK_LBRACE;
      val (lst, tk2) = parseRepetition fstr tk1 isStatement parseStatement;
      val tk3 = match_tk fstr tk2 TK_RBRACE;
   in
      (ST_BLOCK {stmts=lst}, tk3)
   end
and parseIfStatement fstr tk =
   let
      val tk1 = match_tk fstr tk TK_IF;
      val tk2 = match_tk fstr tk1 TK_LPAREN;
      val (guard, tk3) = parseExpression fstr tk2;
      val tk4 = match_tk fstr tk3 TK_RPAREN;
      val (th, tk5) = parseBlockStatement fstr tk4;
      val (el, tk6) = parseElse fstr tk5;
   in
      (ST_IF {guard=guard, th=th, el=el}, tk6)
   end
and parseElse fstr (tk as TK_ELSE) =
   let
      val tk1 = match_tk fstr tk TK_ELSE;
      val (el, tk2) = parseBlockStatement fstr tk1;
   in
      (el, tk2)
   end
  | parseElse fstr tk =
      (ST_BLOCK {stmts=[]}, tk)
and parsePrintStatement fstr tk =
   let
      val tk1 = match_tk fstr tk TK_PRINT;
      val (exp, tk2) = parseExpression fstr tk1;
      val tk3 = match_tk fstr tk2 TK_SEMI;
   in
      (ST_PRINT {exp=exp}, tk3)
   end
and parseWhileStatement fstr tk =
   let
      val tk1 = match_tk fstr tk TK_WHILE;
      val tk2 = match_tk fstr tk1 TK_LPAREN;
      val (guard, tk3) = parseExpression fstr tk2;
      val tk4 = match_tk fstr tk3 TK_RPAREN;
      val (body, tk5) = parseBlockStatement fstr tk4;
   in
      (ST_WHILE {guard=guard, body=body}, tk5)
   end
and parseReturnStatement fstr tk =
   let
      val tk1 = match_tk fstr tk TK_RETURN;
      val (exp, tk2) = if (isExpression tk1)
                        then parseExpression fstr tk1
                        else (EXP_UNDEFINED, tk1);
      val tk3 = match_tk fstr tk2 TK_SEMI;
   in
      (ST_RETURN {exp=exp}, tk3)
   end
and parseVariableElement fstr tk =
   let
      val tk1 = match_tk fstr tk TK_VAR;
      val (decls, tk2) = parseVariableDeclarationList fstr tk1;
      val tk3 = match_tk fstr tk2 TK_SEMI;
   in
      (VAR_DECL {decls=decls}, tk3)
   end
and parseVariableDeclarationList fstr tk =
   parseCommaSeparatedSequence parseVariableDeclaration fstr tk
and parseVariableDeclaration fstr tk =
   let
      val (id, tk1) = match_id fstr tk;
   in
      parseOptionalInitializer fstr tk1 id
   end
and parseOptionalInitializer fstr (tk as TK_ASSIGN) id =
   let
      val tk1 = match_tk fstr tk TK_ASSIGN;
      val (exp, tk2) = parseAssignmentExpression fstr tk1;
   in
      (DECL_INIT {id=id, src=exp}, tk2)
   end
  | parseOptionalInitializer fstr tk id =
   (DECL_ID {id=id}, tk)

and parseFunctionDeclaration fstr tk =
   let
      val tk1 = match_tk fstr tk TK_FUNCTION;
      val (name, tk2) = match_id fstr tk1
      val tk3 = match_tk fstr tk2 TK_LPAREN;
      val (params, tk4) = parseParameterList fstr tk3;
      val tk5 = match_tk fstr tk4 TK_RPAREN;
      val tk6 = match_tk fstr tk5 TK_LBRACE;
      val (body, tk7) = parseSourceElements fstr tk6;
      val tk8 = match_tk fstr tk7 TK_RBRACE;
   in
      (FUNC_DECL {name=name, params=params, body=body}, tk8)
   end
and parseSourceElement fstr (tk as TK_FUNCTION) =
   parseFunctionDeclaration fstr tk
  | parseSourceElement fstr (tk as TK_VAR) =
   parseVariableElement fstr tk
  | parseSourceElement fstr tk =
   let
      val (stmt, tk1) = parseStatement fstr tk;
   in
      (STMT {stmt=stmt}, tk1)
   end
and parseSourceElements fstr tk =
   parseRepetition fstr tk isSourceElement parseSourceElement
;

fun parseProgram fstr tk =
   let
      val (elems, tk1) = parseSourceElements fstr tk;
      val _ = match_eof fstr tk1;
   in
      PROGRAM {elems=elems}
   end
;

fun parseStream fstr =
      parseProgram fstr (nextToken fstr)
;

fun parse file =
   let
      val fstr = openIn(file)
         handle oops =>
            (output (stdErr, "cannot open file: " ^ file ^ "\n");
            OS.Process.exit OS.Process.failure)
   in
      parseStream fstr
   end
;
