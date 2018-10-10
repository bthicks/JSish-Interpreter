open TextIO;

val OPTIONAL = true;

exception InvalidSymbol of string;
exception InvalidNumber of string;
exception InvalidString;
exception UnterminatedString;
exception InvalidEscapeSequence of string;

datatype token =
     TK_LBRACE
   | TK_RBRACE
   | TK_LPAREN
   | TK_RPAREN
   | TK_LBRACKET
   | TK_RBRACKET
   | TK_COMMA
   | TK_SEMI
   | TK_QUESTION
   | TK_COLON
   | TK_DOT
   | TK_PLUS
   | TK_MINUS
   | TK_TIMES
   | TK_DIVIDE
   | TK_MOD
   | TK_AND
   | TK_OR
   | TK_ASSIGN
   | TK_EQ
   | TK_LT
   | TK_LE
   | TK_GT
   | TK_GE
   | TK_NOT
   | TK_NE
   | TK_ELSE
   | TK_FALSE
   | TK_FUNCTION
   | TK_IF
   | TK_NEW
   | TK_PRINT
   | TK_RETURN
   | TK_THIS
   | TK_TRUE
   | TK_TYPEOF
   | TK_UNDEFINED
   | TK_VAR
   | TK_WHILE
   | TK_GC
   | TK_INUSE
   | TK_NUM of int
   | TK_ID of string
   | TK_STRING of string
   | TK_EOF
;

val keywordTokens =
   [
      ("else", TK_ELSE),
      ("false", TK_FALSE),
      ("function", TK_FUNCTION),
      ("if", TK_IF),
      ("new", TK_NEW),
      ("print", TK_PRINT),
      ("return", TK_RETURN),
      ("this", TK_THIS),
      ("true", TK_TRUE),
      ("typeof", TK_TYPEOF),
      ("undefined", TK_UNDEFINED),
      ("var", TK_VAR),
      ("while", TK_WHILE),
      ("gc", TK_GC),
      ("inUse", TK_INUSE)
   ]
;

val symbolTokens =
   [
      ("{", TK_LBRACE),
      ("}", TK_RBRACE),
      ("(", TK_LPAREN),
      (")", TK_RPAREN),
      ("[", TK_LBRACKET),
      ("]", TK_RBRACKET),
      (",", TK_COMMA),
      (";", TK_SEMI),
      ("?", TK_QUESTION),
      (":", TK_COLON),
      (".", TK_DOT),
      ("+", TK_PLUS),
      ("-", TK_MINUS),
      ("*", TK_TIMES),
      ("/", TK_DIVIDE),
      ("%", TK_MOD),
      ("&&", TK_AND),
      ("||", TK_OR),
      ("=", TK_ASSIGN),
      ("==", TK_EQ),
      ("<", TK_LT),
      ("<=", TK_LE),
      (">", TK_GT),
      (">=", TK_GE),
      ("!", TK_NOT),
      ("!=", TK_NE)
   ]
;

fun error s = (output (stdErr, s); OS.Process.exit OS.Process.failure);

fun member s xs = List.exists (fn st => st = s) xs;

fun pairLookup s xs =
   case List.find (fn (st, _) => st = s) xs of
      NONE => NONE
   |  SOME (_, v) => SOME v
;

fun pairLookupReverse s xs =
   case List.find (fn (_, st) => st = s) xs of
      NONE => NONE
   |  SOME (v, _) => SOME v
;

fun clearWhitespace fstr =
   case lookahead fstr of
      NONE => fstr
   |  SOME c => if Char.isSpace c
        then (input1 fstr; clearWhitespace fstr)
        else fstr
;

fun buildToken fstr pred s =
   case lookahead fstr of
      SOME c => if pred c
                then (input1 fstr; buildToken fstr pred (c :: s))
                else implode (rev s)
   |  NONE => implode (rev s)
;

fun outputIdentifier id =
   case pairLookup id keywordTokens of
      NONE => TK_ID id
   |  SOME tk => tk
;

fun outputNumber s =
   case Int.fromString s of
      SOME n => TK_NUM n
   |  NONE => raise InvalidNumber s
;

fun outputString s = TK_STRING s;

fun outputSymbol sym =
   case pairLookup sym symbolTokens of
      NONE => raise InvalidSymbol sym
   |  SOME tk => tk
;

fun recognizeIdentifier fstr =
   buildToken
      fstr
      (fn x => (Char.isAlpha x) orelse (Char.isDigit x))
      []
;

fun recognizeNumber fstr =
   buildToken fstr Char.isDigit []
;

val escapeSequenceList =
   [
    (#"\"", #"\""),
    (#"\\", #"\\"),
    (#"b", #"\b"),
    (#"f", #"\f"),
    (#"n", #"\n"),
    (#"r", #"\r"),
    (#"t", #"\t"),
    (#"v", #"\v")
   ]
;

fun buildEscapeCharacter fstr =
   case input1 fstr of
      SOME c =>
         (case (pairLookup c escapeSequenceList) of
             SOME es => es
           | NONE => raise InvalidEscapeSequence ("\\" ^ (str c))
         )
   |  NONE => raise UnterminatedString
;

fun buildString fstr s =
   case input1 fstr of
      SOME #"\"" => implode (rev s)
   |  SOME #"\\" => buildString fstr ((buildEscapeCharacter fstr) :: s)
   |  SOME (#"\n" | #"\r" | #"\f") => raise UnterminatedString
   |  SOME c => buildString fstr (c :: s)
   |  NONE => raise UnterminatedString
;

fun recognizeString fstr =
   let
      val input = input1 fstr
   in
      case input of
         SOME #"\"" => buildString fstr []
      |  x => raise InvalidString
   end
;

fun buildSymbol need optional fstr s =
   let
      val input = lookahead fstr
   in
      if (isSome input) andalso (member (valOf input) need)
      then (input1 fstr; (s ^ (str (valOf input))))
      else if optional
           then s
           else raise InvalidSymbol s
   end
;

val symbolBuildList =
   let
      fun simple_symbol fstr s = s;
   in
      [
       (#"{", simple_symbol),
       (#"}", simple_symbol),
       (#"(", simple_symbol),
       (#")", simple_symbol),
       (#"[", simple_symbol),
       (#"]", simple_symbol),
       (#",", simple_symbol),
       (#";", simple_symbol),
       (#"?", simple_symbol),
       (#":", simple_symbol),
       (#".", simple_symbol),
       (#"+", simple_symbol),
       (#"-", simple_symbol),
       (#"*", simple_symbol),
       (#"/", simple_symbol),
       (#"%", simple_symbol),
       (#"&", buildSymbol [#"&"] (not OPTIONAL)),
       (#"|", buildSymbol [#"|"] (not OPTIONAL)),
       (#"=", buildSymbol [#"="] OPTIONAL),
       (#"<", buildSymbol [#"="] OPTIONAL),
       (#">", buildSymbol [#"="] OPTIONAL),
       (#"!", buildSymbol [#"="] OPTIONAL)
      ]
   end
;

fun recognizeSymbol fstr =
   let
      val input = input1 fstr
   in
      case input of
         SOME c =>
            (case (pairLookup c symbolBuildList) of
                SOME build_func => build_func fstr (str c)
              | NONE => raise InvalidSymbol (str c)
            )
      |  NONE => raise InvalidSymbol "-eof-"
   end
;

fun recognizeFirstToken fstr =
   case lookahead fstr of
      SOME c => if Char.isAlpha c
                then outputIdentifier (recognizeIdentifier fstr)
                else if Char.isDigit c
                then outputNumber (recognizeNumber fstr)
                else if c = #"\""
                then outputString (recognizeString fstr)
                else outputSymbol (recognizeSymbol fstr)
   | NONE => TK_EOF
;

fun nextToken fstr = recognizeFirstToken (clearWhitespace fstr)
   handle InvalidSymbol s => error ("invalid symbol: '" ^ s ^ "'\n")
        | InvalidNumber s => error ("invalid number: '" ^ s ^ "'\n")
        | UnterminatedString => error ("string not terminated\n")
        | InvalidString => error ("invalid string\n")
        | InvalidEscapeSequence s =>
            error ("invalid escape sequence: '" ^ s ^ "'\n")
;

val allTokens = symbolTokens @ keywordTokens;

fun tkString (TK_NUM n) = Int.toString n
  | tkString (TK_ID id) = id
  | tkString (TK_STRING s) = "\"" ^ (String.toString s) ^ "\""
  | tkString TK_EOF = "eof"
  | tkString tk =
      case pairLookupReverse tk allTokens of
         SOME v => v
      |  NONE => "invalid token"
;
