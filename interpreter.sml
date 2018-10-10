use "printAST.sml";
use "map.sml";

exception MalformedEnvironment;

datatype value =
     Num_Value of int
   | String_Value of string
   | Bool_Value of bool
   | Undefined_Value
   | Closure_Value of {params: string list, body: sourceElement list,
      env: (string, value) HashTable.hash_table list, rf: unit ref}
   | Object_Value of {data: (string, value) HashTable.hash_table, 
      mark: bool ref}
   | Reference_Value of int
;

val current_address : int ref = ref 0;
val heap : (int, value) HashTable.hash_table = HashTable.mkTable (Word.fromInt, (op =))
   (initial_size, UndefinedIdentifier)

fun createClosureValue params body env =
   Closure_Value {params=params, body=body, env=env, rf=ref ()}
;

fun createObjectValue data =
   let
      val obj = Object_Value {data=data, mark=ref false};
      val ref_val = Reference_Value (!current_address);
   in
      (HashTable.insert heap (!current_address, obj);
       current_address := !current_address + 1;
       ref_val)
   end
;

fun lookupHeap address id = 
   case lookup heap address of 
      Object_Value {data, mark} => 
         if contains data id
         then lookup data id
         else Undefined_Value
;  

fun insertHeap address id rhs =
   case lookup heap address of
      Object_Value {data, mark} => insert data id rhs
;

fun markObjects [] = () 
  | markObjects (item::items) =
   (case item of 
      Reference_Value i =>
         let
            val Object_Value {data, mark} = lookup heap i;
            val more_items = HashTable.listItems data;
         in
            (mark := true; markObjects more_items; markObjects items)
         end
 (*   | Closure_Value {params, body, (env, stack), rf} => markHeap (env, stack) *)  
    | v => markObjects items   
   )
   
and markHeap [] = ()
  | markHeap (env::envs) =
   let 
      val items = HashTable.listItems env;
   in
      (markObjects items; markHeap envs) 
   end
;

fun sweepHeap current reclaimed = 
   if current < !current_address
   then 
      let
         val Object_Value {data, mark} = lookup heap current;
      in
         if !mark = false
         then (remove heap current; 
            sweepHeap (current + 1) (current::reclaimed))
         else sweepHeap (current + 1) reclaimed
      end 
   else rev reclaimed
;  

fun reportHeap current in_use =
   if current < !current_address
   then
      if contains heap current
      then reportHeap (current + 1) (current::in_use)
      else reportHeap (current + 1) in_use 
   else rev in_use
;

fun resetHeap current = 
   if current < !current_address
   then
      let
         val Object_Value {data, mark} = lookup heap current;
      in
         (mark := false; resetHeap (current + 1))
      end
   else ()    
;

fun printCommaSeparated [] = TextIO.output (TextIO.stdOut, ("\n"))
  | printCommaSeparated (x::[]) = 
   TextIO.output (TextIO.stdOut, (", " ^ Int.toString x ^ "\n"))
  | printCommaSeparated (x::xs) = 
   (TextIO.output (TextIO.stdOut, (", " ^ Int.toString x)); printCommaSeparated xs)
;

fun printGC [] = TextIO.output (TextIO.stdOut, ("RECLAIMED: \n"))
  | printGC (x::xs) = 
   (TextIO.output (TextIO.stdOut, ("RECLAIMED: " ^ (Int.toString x)));
   printCommaSeparated xs)  
;   

fun printInUse [] = TextIO.output (TextIO.stdOut, ("IN USE: \n"))
  | printInUse (x::xs) = 
   (TextIO.output (TextIO.stdOut, ("IN USE: " ^ (Int.toString x)));
   printCommaSeparated xs)  
;  

fun valueToString (Num_Value n) = 
   (if n < 0 then "-" ^ (Int.toString (~n)) else Int.toString n)
  | valueToString (String_Value s) = s
  | valueToString (Bool_Value b) = Bool.toString b
  | valueToString Undefined_Value = "undefined"
  | valueToString (Closure_Value _) = "function"
  | valueToString (Object_Value _) = "object"
  | valueToString (Reference_Value n) = 
   (if n < 0 then "-" ^ (Int.toString (~n)) else Int.toString n)
;

fun typeString (Num_Value _) = "number"
  | typeString (Bool_Value _) = "boolean"
  | typeString (String_Value _) = "string"
  | typeString (Undefined_Value) = "undefined"
  | typeString (Closure_Value _) = "function"
  | typeString (Object_Value _) = "object"
  | typeString (Reference_Value _) = "object"
;

fun condTypeError found =
   error ("boolean guard required for 'cond' expression, found " ^
      (typeString found) ^ "\n")
;

fun unaryTypeError expected found oper =
   error ("unary operator '" ^
      (unaryOperatorString oper) ^ "' requires " ^
      (typeString expected) ^ ", found " ^ (typeString found) ^ "\n")
;

fun boolTypeError found oper =
   error ("operator '" ^ (binaryOperatorString oper) ^
      "' requires " ^ (typeString (Bool_Value true)) ^
      ", found " ^ (typeString found) ^ "\n")
;

fun binaryTypeError elft erht flft frht oper =
   error ("operator '" ^ (binaryOperatorString oper) ^ "' requires " ^
      (typeString elft) ^ " * " ^ (typeString erht) ^ ", found " ^
      (typeString flft) ^ " * " ^ (typeString frht) ^ "\n")
;

fun addTypeError flft frht oper =
   error ("operator '" ^ (binaryOperatorString oper) ^ "' requires " ^
      (typeString (Num_Value 0)) ^ " * " ^
      (typeString (Num_Value 0)) ^ " or " ^
      (typeString (String_Value "")) ^ " * " ^
      (typeString (String_Value "")) ^
      ", found " ^ (typeString flft) ^ " * " ^ (typeString frht) ^ "\n")
;

fun ifTypeError found =
   error ("boolean guard required for 'if' statement, found " ^
      (typeString found) ^ "\n")
;

fun whileTypeError found =
   error ("boolean guard required for 'while' statement, found " ^
      (typeString found) ^ "\n")
;

fun envChain {chain, retVal} = chain;
fun envRetVal {chain, retVal} = retVal;
fun createEnv chain retVal = {chain=chain, retVal=retVal};

fun atTopLevel {chain=[tle], retVal} = true
  | atTopLevel {chain, retVal} = false
;

fun insertCurrent env id v = (insert (hd (envChain env)) id v; env);
fun declareCurrent env id =
   if contains (hd (envChain env)) id
   then env
   else (insert (hd (envChain env)) id Undefined_Value; env)
;
fun insertEnvH [] id v = raise MalformedEnvironment
  | insertEnvH [global] id v = insert global id v
  | insertEnvH (env::envs) id v =
   if contains env id
   then insert env id v
   else insertEnvH envs id v
;
fun insertEnv env id v = (insertEnvH (envChain env) id v; env);
fun lookupEnvH [] id = raise UndefinedIdentifier
  | lookupEnvH (env::envs) id =
   if contains env id
   then lookup env id
   else lookupEnvH envs id
;
fun lookupEnv env id = lookupEnvH (envChain env) id;
fun growEnvironment env =
   createEnv ((new_map ())::(envChain env)) (envRetVal env)
;

fun operatorFunc comp funcs oper =
   List.find (fn (opr, _) => comp (opr, oper)) funcs
;

fun applyArithOp _ fnc (Num_Value lft) (Num_Value rht) =
   Num_Value (fnc (lft, rht))
  | applyArithOp oper _ lft rht =
   binaryTypeError (Num_Value 0) (Num_Value 0) lft rht oper
;

fun applyDivOp _ fnc (Num_Value lft) (Num_Value rht) =
   if rht = 0
   then (error "divide by zero\n"; Undefined_Value)
   else Num_Value (fnc (lft, rht))
  | applyDivOp oper _ lft rht =
   binaryTypeError (Num_Value 0) (Num_Value 0) lft rht oper
;

fun applyRelOp _ fnc (Num_Value lft) (Num_Value rht) =
   Bool_Value (fnc (lft, rht))
  | applyRelOp oper _ lft rht =
   binaryTypeError (Num_Value 0) (Num_Value 0) lft rht oper
;

fun applyAddOp oper (Num_Value lft) (Num_Value rht) =
   Num_Value (lft + rht)
  | applyAddOp oper (String_Value lft) (String_Value rht) =
   String_Value (lft ^ rht)
  | applyAddOp oper lft rht =
   addTypeError lft rht oper
;

fun applyEqualityOp (Num_Value lft) (Num_Value rht) =
   Bool_Value (lft = rht)
  | applyEqualityOp (String_Value lft) (String_Value rht) =
   Bool_Value (lft = rht)
  | applyEqualityOp (Bool_Value lft) (Bool_Value rht) =
   Bool_Value (lft = rht)
  | applyEqualityOp Undefined_Value Undefined_Value =
   Bool_Value true
  | applyEqualityOp (Closure_Value lft) (Closure_Value rht) =
   Bool_Value (#rf lft = #rf rht)
  | applyEqualityOp (Reference_Value lft) (Reference_Value rht) =
   Bool_Value (lft = rht)
  | applyEqualityOp _ _ =
   Bool_Value false
;

fun applyInequalityOp x y =
   let
      val Bool_Value b = applyEqualityOp x y;
   in
      Bool_Value (not b)
   end
;

fun applyCommaOp _ rht = rht;

fun applyEagerBoolOp _ fnc (Bool_Value lft) (Bool_Value rht) =
   Bool_Value (fnc (lft, rht))
  | applyEagerBoolOp oper _ lft rht =
   binaryTypeError (Bool_Value true) (Bool_Value true) lft rht oper
;

fun applyEagerAndOp oper lft rht =
   applyEagerBoolOp oper (fn (a, b) => a andalso b) lft rht
;

fun applyEagerOrOp oper lft rht =
   applyEagerBoolOp oper (fn (a, b) => a orelse b) lft rht
;

val binaryFuncs = [
   (BOP_PLUS, applyAddOp BOP_PLUS),
   (BOP_MINUS, applyArithOp BOP_MINUS (op -)),
   (BOP_TIMES, applyArithOp BOP_TIMES (op * )),
   (BOP_DIVIDE, applyDivOp BOP_DIVIDE (op div)),
   (BOP_MOD, applyDivOp BOP_MOD (op mod)),
   (BOP_EQ, applyEqualityOp),
   (BOP_NE, applyInequalityOp),
   (BOP_LT, applyRelOp BOP_LT (op <)),
   (BOP_GT, applyRelOp BOP_GT (op >)),
   (BOP_LE, applyRelOp BOP_LE (op <=)),
   (BOP_GE, applyRelOp BOP_GE (op >=)),
   (BOP_AND, applyEagerAndOp BOP_AND),
   (BOP_OR, applyEagerOrOp BOP_OR),
   (BOP_COMMA, applyCommaOp)
];

val binaryOperatorFunc =
   operatorFunc ((op =) : binaryOperator * binaryOperator -> bool) binaryFuncs
;

fun applyNotOp _ (Bool_Value b) =
   Bool_Value (not b)
  | applyNotOp oper opnd =
   unaryTypeError (Bool_Value true) opnd oper
;

fun applyMinusOp _ (Num_Value n) =
   Num_Value (~n)
  | applyMinusOp oper opnd =
   unaryTypeError (Num_Value 0) opnd oper
;

fun applyTypeofOp v = String_Value (typeString v);

val unaryFuncs = [
   (UOP_NOT, applyNotOp UOP_NOT),
   (UOP_TYPEOF, applyTypeofOp),
   (UOP_MINUS, applyMinusOp UOP_MINUS)
];

val unaryOperatorFunc =
   operatorFunc ((op =) : unaryOperator * unaryOperator -> bool) unaryFuncs
;

fun verifyBoolValue (v as Bool_Value b) oper =
   v
  | verifyBoolValue v oper =
   binaryTypeError (Bool_Value true) (Bool_Value true)
      (Bool_Value true) v oper
;

fun declareFunction {name, params, body} (env, stack) =
   (insertCurrent env name (createClosureValue params body (envChain env)), stack);

fun bindParameters [] args env = env
  | bindParameters (p::ps) [] env =
   bindParameters ps [] (insertCurrent env p Undefined_Value)
  | bindParameters (p::ps) (arg::args) env =
   bindParameters ps args (insertCurrent env p arg)
;

fun evalVariables [] (env, stack) = (env, stack)
  | evalVariables ((DECL_ID {id})::decls) (env, stack) =
   evalVariables decls (declareCurrent env id, stack)
  | evalVariables ((DECL_INIT {id, src})::decls) (env, stack) =
   evalVariables decls
      (insertCurrent env id (evalExpression src (env, stack)), stack)

and evalBinary BOP_AND lft rht (env, stack) =
   (case evalExpression lft (env, stack) of
       Bool_Value true => verifyBoolValue (evalExpression rht (env, stack)) BOP_AND
    |  Bool_Value false => Bool_Value false
    |  v => boolTypeError v BOP_AND
   )
  | evalBinary BOP_OR lft rht (env, stack) =
   (case evalExpression lft (env, stack) of
       Bool_Value true => Bool_Value true
    |  Bool_Value false => verifyBoolValue (evalExpression rht (env, stack)) BOP_OR
    |  v => boolTypeError v BOP_OR
   )
  | evalBinary oper lft rht (env, stack) =
   case (binaryOperatorFunc oper) of
      SOME (_, func) =>
         func (evalExpression lft (env, stack)) (evalExpression rht (env, stack))
   |  NONE =>
         error ("operator '" ^ (binaryOperatorString oper) ^ "' not found\n")
and evalUnary oper opnd (env, stack) =
   case (unaryOperatorFunc oper) of
      SOME (_, func) => func (evalExpression opnd (env, stack))
   |  NONE =>
         error ("operator '" ^ (unaryOperatorString oper) ^ "' not found\n")
and evalExpression (EXP_ID s) (env, stack) =
   (lookupEnv env s handle UndefinedIdentifier =>
      error ("variable '" ^ s ^ "' not found\n"))
  | evalExpression (EXP_NUM n) (env, stack) =
   Num_Value n
  | evalExpression (EXP_STRING s) (env, stack) =
   String_Value s
  | evalExpression EXP_TRUE (env, stack) =
   Bool_Value true
  | evalExpression EXP_FALSE (env, stack) =
   Bool_Value false
  | evalExpression EXP_UNDEFINED (env, stack) =
   Undefined_Value
  | evalExpression (EXP_BINARY {opr, lft, rht}) (env, stack) =
   evalBinary opr lft rht (env, stack)
  | evalExpression (EXP_UNARY {opr, opnd}) (env, stack) =
   evalUnary opr opnd (env, stack)
  | evalExpression EXP_THIS (env, stack) = 
   if atTopLevel env
   then (Reference_Value 0)
   else lookupEnv env "this"
  | evalExpression (EXP_COND {guard, thenExp, elseExp}) (env, stack) =
   (case evalExpression guard (env, stack) of
       Bool_Value true => evalExpression thenExp (env, stack)
    |  Bool_Value false => evalExpression elseExp (env, stack)
    |  v => condTypeError v
   )
  | evalExpression (EXP_ASSIGN {lhs, rhs}) (env, stack) =
   let
      val rhs = evalExpression rhs (env, stack);
   in
      (case lhs of
          EXP_ID s => insertEnv env s rhs   
       |  EXP_DOT {lft, id} => 
             (case (evalExpression lft (env, stack)) of 
                 Reference_Value i => (insertHeap i id rhs; env(*; (env, stack)*))
              |  v => error ("field reference '.' requires object, found " ^
                 typeString(v) ^ "\n")
             )  
       |  _ => error "unexpected target of assignment\n"
       ;
       rhs
      )
   end
  | evalExpression (EXP_CALL {func as EXP_DOT {lft, id}, args}) (env, stack) =
   (case (evalExpression lft (env, stack)) of
      (ref_val as Reference_Value i) => 
         (case lookupHeap i id of
            Closure_Value closure =>
               let
                  (* evaluate arguments in current environment *)
                  val argValues =
                     List.map (fn exp => evalExpression exp (env, stack)) args;
                  (* bind parameters in new environment *)
                  val newenv = bindParameters
                     ("this"::(#params closure))
                     (ref_val::argValues)
                     (growEnvironment (createEnv (#env closure) NONE));
                  (* evaluate body *)
                  val (resEnv, resStack) = evalSourceElements (#body closure) (newenv, stack);
               in
                  case envRetVal resEnv of
                     SOME v => v
                  |  NONE => Undefined_Value
               end
          | e => error ("attempt to invoke '" ^ typeString(e) ^
            "' value as a function\n")
         ) 
   |  e => error ("field reference '.' requires object, found " ^
      typeString(e) ^ "\n")
   )  
  | evalExpression (EXP_CALL {func, args}) (env, stack) =
   (case evalExpression func (env, stack) of
      Closure_Value closure =>
         let
            (* evaluate arguments in current environment *)
            val argValues =
               List.map (fn exp => evalExpression exp (env, stack)) args;
            (* create new object to bind to this *)
            val ref_val = (Reference_Value 0); 
            (* bind parameters in new environment *)
            val newenv = bindParameters
               ("this"::(#params closure))
               (ref_val::argValues)
               (growEnvironment (createEnv (#env closure) NONE));
            (* evaluate body *)
            val (resEnv, resStack) = evalSourceElements (#body closure) (newenv, stack);
         in
            case envRetVal resEnv of
               SOME v => v
            |  NONE => Undefined_Value
         end  
    | e => error ("attempt to invoke '" ^ typeString(e) ^
      "' value as a function\n")
   )
  | evalExpression (EXP_ANON {params, body}) (env, stack) =
   createClosureValue params body (envChain env)
  | evalExpression (EXP_DOT {lft, id}) (env, stack) = 
   (case (evalExpression lft (env, stack)) of
       Reference_Value i => lookupHeap i id
    |  v => error ("field reference '.' requires object, found " ^
       typeString(v) ^ "\n")
   )
  | evalExpression (EXP_NEW {ctorExp, args}) (env, stack) = 
   (case (evalExpression ctorExp (env, stack)) of
      Closure_Value closure =>
         let
            (* evaluate arguments in current environment *)  
            val argValues =
               List.map (fn exp => evalExpression exp (env, stack)) args;
            (* create new object to bind to this *)
            val ref_val = createObjectValue (new_map ());   
            (* bind parameters in new environment *)
            val newenv = bindParameters
               ("this"::(#params closure))
               (ref_val::argValues)
               (growEnvironment (createEnv (#env closure) NONE)); 
            (* evaluate body *)
            val (resEnv, resStack) = evalSourceElements (#body closure) (newenv, stack);
         in
            case envRetVal resEnv of 
               SOME v => retMemberExpression v ref_val
            |  NONE => ref_val
         end
    | e => error ("new may only be applied to a function, found " ^ 
      typeString(e) ^ "\n")
   )  
  | evalExpression (EXP_OBJ {props}) (env, stack) =
   let 
      val data = createObjectTable props (new_map ()) (env, stack);  
   in 
      createObjectValue data  
   end 

and retMemberExpression (Reference_Value i) this = (Reference_Value i)
  | retMemberExpression v this = this    

and createObjectTable [] table (env, stack) = table
  | createObjectTable (prop::props) table (env, stack) =
   createObjectTable props
      (insert table (#id prop) (evalExpression (#exp prop) (env, stack))) (env, stack)

and evalStatement _ (env as {chain, retVal=SOME _}, stack) = (env, stack)
  | evalStatement (ST_EXP {exp}) (env, stack) =
   evalExpStatement exp (env, stack)
  | evalStatement (ST_BLOCK {stmts}) (env, stack) =
   evalStatements stmts (env, stack)
  | evalStatement (ST_IF {guard, th, el}) (env, stack) =
   evalIfStatement guard th el (env, stack)
  | evalStatement (ST_PRINT {exp}) (env, stack) =
   evalPrintStatement exp (env, stack)
  | evalStatement (ST_WHILE {guard, body}) (env, stack) =
   evalWhileStatement guard body (env, stack)
  | evalStatement (ST_RETURN {exp}) (env, stack) =
   if not (atTopLevel env)
   then (createEnv (envChain env) (SOME (evalExpression exp (env, stack))), stack)
   else error ("return statements are only valid inside functions\n")
  | evalStatement ST_GC (env, stack) = 
   evalGCStatement (env, stack)
  | evalStatement ST_INUSE (env, stack) = 
   evalInUseStatement (env, stack)

and evalExpStatement exp (env, stack) =
   (evalExpression exp (env, stack); (env, stack))
and evalIfStatement guard th el (env, stack) =
   case evalExpression guard (env, stack) of
      Bool_Value true => evalStatement th (env, stack)
   |  Bool_Value false => evalStatement el (env, stack)
   |  v => ifTypeError v
and evalPrintStatement exp (env, stack) =
   (TextIO.output (TextIO.stdOut, valueToString (evalExpression exp (env, stack))); (env, stack))
and evalWhileStatement guard body (env, stack) =
   case evalExpression guard (env, stack) of
      Bool_Value true =>
         evalStatement
            (ST_WHILE {guard=guard, body=body}) (evalStatement body (env, stack))
   |  Bool_Value false => (env, stack)
   |  v => whileTypeError v
and evalGCStatement (env, stack) =    
   let
      val reset = resetHeap 1;
      val marked = markHeap (envChain env);
      val reclaimed = sweepHeap 1 [];
   in
      (printGC reclaimed; (env, stack))
   end
and evalInUseStatement (env, stack) =
   let
      val in_use = reportHeap 0 [];
   in
      (printInUse in_use; (env, stack))
   end 

and evalStatements [] (env, stack) = (env, stack)
  | evalStatements (stmt::stmts) (env, stack) =
   evalStatements stmts (evalStatement stmt (env, stack))
and evalSourceElement (STMT {stmt}) (env, stack) =
      evalStatement stmt (env, stack)
  | evalSourceElement (FUNC_DECL func) (env, stack) =
      declareFunction func (env, stack)
  | evalSourceElement (VAR_DECL {decls}) (env, stack) =
      evalVariables decls (env, stack)
and evalSourceElements [] (env, stack) = (env, stack)
  | evalSourceElements (elem::elems) (env, stack) = 
     evalSourceElements elems (evalSourceElement elem (env, stack))
;

fun createEnvironment () = createEnv [new_map ()] NONE;

fun evalProgram (PROGRAM {elems}) =
   let
      val env = createEnvironment ();
      val obj = createObjectValue (hd (envChain env));
      val stack : (string, value) HashTable.hash_table list list = [];
   in
      evalSourceElements elems (env, stack)
   end
;

fun interpret file =
   (evalProgram (parse file); ())
;
