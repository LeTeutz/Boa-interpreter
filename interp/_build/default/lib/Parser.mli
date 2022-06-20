
(* The type of tokens. *)

type token = 
  | WITH
  | VAR of (Syntax.name)
  | UNEQUAL
  | TRUE
  | TIMES
  | THIS
  | THEN
  | SKIP
  | SEMICOLON2
  | SEMICOLON
  | RPAREN
  | REMAINDER
  | RBRACE
  | PLUS
  | PERIOD
  | OR
  | NOT
  | MINUS
  | LPAREN
  | LET
  | LESS
  | LBRACE
  | INT of (int)
  | IN
  | IF
  | FUN
  | FALSE
  | EQUAL
  | EOF
  | ELSE
  | DIVIDE
  | COPY
  | COMMA
  | ASSIGN
  | ARROW
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val toplevel: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.toplevel_cmd)

val file: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.toplevel_cmd list)
