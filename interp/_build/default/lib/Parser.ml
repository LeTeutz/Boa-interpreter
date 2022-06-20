
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | WITH
    | VAR of (
# 10 "lib/Parser.mly"
       (Syntax.name)
# 16 "lib/Parser.ml"
  )
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
    | INT of (
# 12 "lib/Parser.mly"
       (int)
# 41 "lib/Parser.ml"
  )
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
  
end

include MenhirBasics

# 3 "lib/Parser.mly"
  
open Syntax

# 65 "lib/Parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState00 : ('s, _menhir_box_file) _menhir_state
    (** State 00.
        Stack shape : .
        Start symbol: file. *)

  | MenhirState05 : (('s, 'r) _menhir_cell1_NOT, 'r) _menhir_state
    (** State 05.
        Stack shape : NOT.
        Start symbol: <undetermined>. *)

  | MenhirState06 : (('s, 'r) _menhir_cell1_LPAREN, 'r) _menhir_state
    (** State 06.
        Stack shape : LPAREN.
        Start symbol: <undetermined>. *)

  | MenhirState09 : (('s, 'r) _menhir_cell1_LET _menhir_cell0_VAR, 'r) _menhir_state
    (** State 09.
        Stack shape : LET VAR.
        Start symbol: <undetermined>. *)

  | MenhirState10 : (('s, 'r) _menhir_cell1_LBRACE, 'r) _menhir_state
    (** State 10.
        Stack shape : LBRACE.
        Start symbol: <undetermined>. *)

  | MenhirState12 : (('s, 'r) _menhir_cell1_VAR, 'r) _menhir_state
    (** State 12.
        Stack shape : VAR.
        Start symbol: <undetermined>. *)

  | MenhirState14 : (('s, 'r) _menhir_cell1_IF, 'r) _menhir_state
    (** State 14.
        Stack shape : IF.
        Start symbol: <undetermined>. *)

  | MenhirState17 : (('s, 'r) _menhir_cell1_FUN _menhir_cell0_VAR, 'r) _menhir_state
    (** State 17.
        Stack shape : FUN VAR.
        Start symbol: <undetermined>. *)

  | MenhirState19 : (('s, 'r) _menhir_cell1_COPY, 'r) _menhir_state
    (** State 19.
        Stack shape : COPY.
        Start symbol: <undetermined>. *)

  | MenhirState20 : ((('s, 'r) _menhir_cell1_COPY, 'r) _menhir_cell1_non_app, 'r) _menhir_state
    (** State 20.
        Stack shape : COPY non_app.
        Start symbol: <undetermined>. *)

  | MenhirState21 : ((('s, 'r) _menhir_cell1_non_app, 'r) _menhir_cell1_WITH, 'r) _menhir_state
    (** State 21.
        Stack shape : non_app WITH.
        Start symbol: <undetermined>. *)

  | MenhirState22 : (((('s, 'r) _menhir_cell1_non_app, 'r) _menhir_cell1_WITH, 'r) _menhir_cell1_non_app, 'r) _menhir_state
    (** State 22.
        Stack shape : non_app WITH non_app.
        Start symbol: <undetermined>. *)

  | MenhirState25 : (('s, 'r) _menhir_cell1_non_app, 'r) _menhir_state
    (** State 25.
        Stack shape : non_app.
        Start symbol: <undetermined>. *)

  | MenhirState28 : ((('s, 'r) _menhir_cell1_non_app, 'r) _menhir_cell1_PERIOD _menhir_cell0_VAR, 'r) _menhir_state
    (** State 28.
        Stack shape : non_app PERIOD VAR.
        Start symbol: <undetermined>. *)

  | MenhirState30 : (('s, 'r) _menhir_cell1_expr, 'r) _menhir_state
    (** State 30.
        Stack shape : expr.
        Start symbol: <undetermined>. *)

  | MenhirState34 : (('s, 'r) _menhir_cell1_app, 'r) _menhir_state
    (** State 34.
        Stack shape : app.
        Start symbol: <undetermined>. *)

  | MenhirState35 : ((('s, 'r) _menhir_cell1_app, 'r) _menhir_cell1_non_app, 'r) _menhir_state
    (** State 35.
        Stack shape : app non_app.
        Start symbol: <undetermined>. *)

  | MenhirState36 : (('s, 'r) _menhir_cell1_expr, 'r) _menhir_state
    (** State 36.
        Stack shape : expr.
        Start symbol: <undetermined>. *)

  | MenhirState38 : (('s, 'r) _menhir_cell1_expr, 'r) _menhir_state
    (** State 38.
        Stack shape : expr.
        Start symbol: <undetermined>. *)

  | MenhirState40 : (('s, 'r) _menhir_cell1_expr, 'r) _menhir_state
    (** State 40.
        Stack shape : expr.
        Start symbol: <undetermined>. *)

  | MenhirState42 : (('s, 'r) _menhir_cell1_expr, 'r) _menhir_state
    (** State 42.
        Stack shape : expr.
        Start symbol: <undetermined>. *)

  | MenhirState44 : ((('s, 'r) _menhir_cell1_non_app, 'r) _menhir_cell1_non_app, 'r) _menhir_state
    (** State 44.
        Stack shape : non_app non_app.
        Start symbol: <undetermined>. *)

  | MenhirState46 : (('s, 'r) _menhir_cell1_expr, 'r) _menhir_state
    (** State 46.
        Stack shape : expr.
        Start symbol: <undetermined>. *)

  | MenhirState48 : (('s, 'r) _menhir_cell1_expr, 'r) _menhir_state
    (** State 48.
        Stack shape : expr.
        Start symbol: <undetermined>. *)

  | MenhirState50 : (('s, 'r) _menhir_cell1_expr, 'r) _menhir_state
    (** State 50.
        Stack shape : expr.
        Start symbol: <undetermined>. *)

  | MenhirState52 : (('s, 'r) _menhir_cell1_expr, 'r) _menhir_state
    (** State 52.
        Stack shape : expr.
        Start symbol: <undetermined>. *)

  | MenhirState54 : (('s, 'r) _menhir_cell1_expr, 'r) _menhir_state
    (** State 54.
        Stack shape : expr.
        Start symbol: <undetermined>. *)

  | MenhirState56 : (('s, 'r) _menhir_cell1_expr, 'r) _menhir_state
    (** State 56.
        Stack shape : expr.
        Start symbol: <undetermined>. *)

  | MenhirState59 : ((('s, 'r) _menhir_cell1_IF, 'r) _menhir_cell1_expr, 'r) _menhir_state
    (** State 59.
        Stack shape : IF expr.
        Start symbol: <undetermined>. *)

  | MenhirState61 : (((('s, 'r) _menhir_cell1_IF, 'r) _menhir_cell1_expr, 'r) _menhir_cell1_expr, 'r) _menhir_state
    (** State 61.
        Stack shape : IF expr expr.
        Start symbol: <undetermined>. *)

  | MenhirState67 : (('s, 'r) _menhir_cell1_field, 'r) _menhir_state
    (** State 67.
        Stack shape : field.
        Start symbol: <undetermined>. *)

  | MenhirState70 : ((('s, 'r) _menhir_cell1_LET _menhir_cell0_VAR, 'r) _menhir_cell1_expr, 'r) _menhir_state
    (** State 70.
        Stack shape : LET VAR expr.
        Start symbol: <undetermined>. *)

  | MenhirState77 : (('s, 'r) _menhir_cell1_LET _menhir_cell0_VAR, 'r) _menhir_state
    (** State 77.
        Stack shape : LET VAR.
        Start symbol: <undetermined>. *)

  | MenhirState83 : (('s, _menhir_box_file) _menhir_cell1_command, _menhir_box_file) _menhir_state
    (** State 83.
        Stack shape : command.
        Start symbol: file. *)

  | MenhirState86 : ('s, _menhir_box_toplevel) _menhir_state
    (** State 86.
        Stack shape : .
        Start symbol: toplevel. *)


and ('s, 'r) _menhir_cell1_app = 
  | MenhirCell1_app of 's * ('s, 'r) _menhir_state * (Syntax.expr)

and ('s, 'r) _menhir_cell1_command = 
  | MenhirCell1_command of 's * ('s, 'r) _menhir_state * (Syntax.toplevel_cmd)

and ('s, 'r) _menhir_cell1_expr = 
  | MenhirCell1_expr of 's * ('s, 'r) _menhir_state * (Syntax.expr)

and ('s, 'r) _menhir_cell1_field = 
  | MenhirCell1_field of 's * ('s, 'r) _menhir_state * (string * Syntax.expr)

and ('s, 'r) _menhir_cell1_non_app = 
  | MenhirCell1_non_app of 's * ('s, 'r) _menhir_state * (Syntax.expr)

and ('s, 'r) _menhir_cell1_COPY = 
  | MenhirCell1_COPY of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_FUN = 
  | MenhirCell1_FUN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LBRACE = 
  | MenhirCell1_LBRACE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LET = 
  | MenhirCell1_LET of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LPAREN = 
  | MenhirCell1_LPAREN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_NOT = 
  | MenhirCell1_NOT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_PERIOD = 
  | MenhirCell1_PERIOD of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_VAR = 
  | MenhirCell1_VAR of 's * ('s, 'r) _menhir_state * (
# 10 "lib/Parser.mly"
       (Syntax.name)
# 287 "lib/Parser.ml"
)

and 's _menhir_cell0_VAR = 
  | MenhirCell0_VAR of 's * (
# 10 "lib/Parser.mly"
       (Syntax.name)
# 294 "lib/Parser.ml"
)

and ('s, 'r) _menhir_cell1_WITH = 
  | MenhirCell1_WITH of 's * ('s, 'r) _menhir_state

and _menhir_box_toplevel = 
  | MenhirBox_toplevel of (Syntax.toplevel_cmd) [@@unboxed]

and _menhir_box_file = 
  | MenhirBox_file of (Syntax.toplevel_cmd list) [@@unboxed]

let _menhir_action_02 =
  fun _1 _2 ->
    (
# 71 "lib/Parser.mly"
                        ( App (_1, _2) )
# 311 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_03 =
  fun _1 _2 ->
    (
# 72 "lib/Parser.mly"
                        ( App (_1, _2) )
# 319 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_04 =
  fun _1 _3 ->
    (
# 88 "lib/Parser.mly"
                     ( ArithOp (Plus, _1, _3) )
# 327 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_05 =
  fun _1 _3 ->
    (
# 89 "lib/Parser.mly"
                    ( ArithOp (Minus, _1, _3) )
# 335 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_06 =
  fun _1 _3 ->
    (
# 90 "lib/Parser.mly"
                     ( ArithOp (Times, _1, _3) )
# 343 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_07 =
  fun _1 _3 ->
    (
# 91 "lib/Parser.mly"
                     ( ArithOp (Divide, _1, _3) )
# 351 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_08 =
  fun _1 _3 ->
    (
# 92 "lib/Parser.mly"
                        ( ArithOp (Remainder, _1, _3) )
# 359 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_09 =
  fun _2 ->
    (
# 95 "lib/Parser.mly"
                        ( Not _2 )
# 367 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_10 =
  fun _1 _3 ->
    (
# 96 "lib/Parser.mly"
                        ( CmpOp (Less, _1, _3) )
# 375 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_11 =
  fun _1 _3 ->
    (
# 97 "lib/Parser.mly"
                        ( CmpOp (Equal, _1, _3) )
# 383 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_12 =
  fun _1 _3 ->
    (
# 98 "lib/Parser.mly"
                        ( CmpOp (Unequal, _1, _3) )
# 391 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_13 =
  fun _1 _3 ->
    (
# 99 "lib/Parser.mly"
                        ( BoolOp (And, _1, _3) )
# 399 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_14 =
  fun _1 _3 ->
    (
# 100 "lib/Parser.mly"
                        ( BoolOp (Or, _1, _3) )
# 407 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_15 =
  fun _1 ->
    (
# 56 "lib/Parser.mly"
                         ( Expr _1 )
# 415 "lib/Parser.ml"
     : (Syntax.toplevel_cmd))

let _menhir_action_16 =
  fun _2 _4 ->
    (
# 57 "lib/Parser.mly"
                         ( Def (_2, _4) )
# 423 "lib/Parser.ml"
     : (Syntax.toplevel_cmd))

let _menhir_action_17 =
  fun _1 ->
    (
# 60 "lib/Parser.mly"
                        ( _1 )
# 431 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_18 =
  fun _1 ->
    (
# 61 "lib/Parser.mly"
                        ( _1 )
# 439 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_19 =
  fun _1 ->
    (
# 62 "lib/Parser.mly"
                        ( _1 )
# 447 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_20 =
  fun _1 ->
    (
# 63 "lib/Parser.mly"
                        ( _1 )
# 455 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_21 =
  fun _2 _4 _6 ->
    (
# 64 "lib/Parser.mly"
                                       ( If (_2, _4, _6) )
# 463 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_22 =
  fun _2 _4 ->
    (
# 65 "lib/Parser.mly"
                                       ( Fun (_2, _4) )
# 471 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_23 =
  fun _2 _4 _6 ->
    (
# 66 "lib/Parser.mly"
                                       ( Let (_2, _4, _6) )
# 479 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_24 =
  fun _1 _3 _5 ->
    (
# 67 "lib/Parser.mly"
                                       ( Assign (_1, _3, _5) )
# 487 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_25 =
  fun _1 _3 ->
    (
# 68 "lib/Parser.mly"
                                       ( Seq (_1, _3) )
# 495 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_26 =
  fun _1 _3 ->
    (
# 103 "lib/Parser.mly"
                                ( (_1, _3) )
# 503 "lib/Parser.ml"
     : (string * Syntax.expr))

let _menhir_action_27 =
  fun () ->
    (
# 106 "lib/Parser.mly"
                                    ( [] )
# 511 "lib/Parser.ml"
     : ((string * Syntax.expr) list))

let _menhir_action_28 =
  fun _1 ->
    (
# 107 "lib/Parser.mly"
                                    ( [_1] )
# 519 "lib/Parser.ml"
     : ((string * Syntax.expr) list))

let _menhir_action_29 =
  fun _1 _3 ->
    (
# 108 "lib/Parser.mly"
                                    ( _1 :: _3 )
# 527 "lib/Parser.ml"
     : ((string * Syntax.expr) list))

let _menhir_action_30 =
  fun () ->
    (
# 48 "lib/Parser.mly"
                             ( [] )
# 535 "lib/Parser.ml"
     : (Syntax.toplevel_cmd list))

let _menhir_action_31 =
  fun _1 _3 ->
    (
# 49 "lib/Parser.mly"
                             ( _1 :: _3 )
# 543 "lib/Parser.ml"
     : (Syntax.toplevel_cmd list))

let _menhir_action_32 =
  fun _1 ->
    (
# 50 "lib/Parser.mly"
                             ( [_1] )
# 551 "lib/Parser.ml"
     : (Syntax.toplevel_cmd list))

let _menhir_action_33 =
  fun _1 ->
    (
# 75 "lib/Parser.mly"
                    ( Var _1 )
# 559 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_34 =
  fun () ->
    (
# 76 "lib/Parser.mly"
                                  ( This )
# 567 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_35 =
  fun () ->
    (
# 77 "lib/Parser.mly"
                           ( Bool true )
# 575 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_36 =
  fun () ->
    (
# 78 "lib/Parser.mly"
                           ( Bool false )
# 583 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_37 =
  fun _1 ->
    (
# 79 "lib/Parser.mly"
                           ( Int _1 )
# 591 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_38 =
  fun () ->
    (
# 80 "lib/Parser.mly"
                                  ( Skip )
# 599 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_39 =
  fun _2 ->
    (
# 81 "lib/Parser.mly"
                          ( _2 )
# 607 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_40 =
  fun _1 _3 ->
    (
# 82 "lib/Parser.mly"
                                  ( Project (_1, _3) )
# 615 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_41 =
  fun _2 ->
    (
# 83 "lib/Parser.mly"
                                  ( Object _2 )
# 623 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_42 =
  fun _2 ->
    (
# 84 "lib/Parser.mly"
                                  ( Copy _2 )
# 631 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_43 =
  fun _1 _3 ->
    (
# 85 "lib/Parser.mly"
                                  ( With (_1, _3) )
# 639 "lib/Parser.ml"
     : (Syntax.expr))

let _menhir_action_44 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 647 "lib/Parser.ml"
     : (unit option))

let _menhir_action_45 =
  fun x ->
    (
# 113 "<standard.mly>"
    ( Some x )
# 655 "lib/Parser.ml"
     : (unit option))

let _menhir_action_46 =
  fun _1 ->
    (
# 53 "lib/Parser.mly"
                             ( _1 )
# 663 "lib/Parser.ml"
     : (Syntax.toplevel_cmd))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | AND ->
        "AND"
    | ARROW ->
        "ARROW"
    | ASSIGN ->
        "ASSIGN"
    | COMMA ->
        "COMMA"
    | COPY ->
        "COPY"
    | DIVIDE ->
        "DIVIDE"
    | ELSE ->
        "ELSE"
    | EOF ->
        "EOF"
    | EQUAL ->
        "EQUAL"
    | FALSE ->
        "FALSE"
    | FUN ->
        "FUN"
    | IF ->
        "IF"
    | IN ->
        "IN"
    | INT _ ->
        "INT"
    | LBRACE ->
        "LBRACE"
    | LESS ->
        "LESS"
    | LET ->
        "LET"
    | LPAREN ->
        "LPAREN"
    | MINUS ->
        "MINUS"
    | NOT ->
        "NOT"
    | OR ->
        "OR"
    | PERIOD ->
        "PERIOD"
    | PLUS ->
        "PLUS"
    | RBRACE ->
        "RBRACE"
    | REMAINDER ->
        "REMAINDER"
    | RPAREN ->
        "RPAREN"
    | SEMICOLON ->
        "SEMICOLON"
    | SEMICOLON2 ->
        "SEMICOLON2"
    | SKIP ->
        "SKIP"
    | THEN ->
        "THEN"
    | THIS ->
        "THIS"
    | TIMES ->
        "TIMES"
    | TRUE ->
        "TRUE"
    | UNEQUAL ->
        "UNEQUAL"
    | VAR _ ->
        "VAR"
    | WITH ->
        "WITH"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37-39"]
  
  let rec _menhir_goto_option_SEMICOLON2_ : type  ttv_stack. (ttv_stack, _menhir_box_toplevel) _menhir_cell1_command -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _tok ->
      match (_tok : MenhirBasics.token) with
      | EOF ->
          let MenhirCell1_command (_menhir_stack, _, _1) = _menhir_stack in
          let _v = _menhir_action_46 _1 in
          MenhirBox_toplevel _v
      | _ ->
          _eRR ()
  
  let rec _menhir_run_88 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_toplevel) _menhir_state -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_command (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | SEMICOLON2 ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let x = () in
          let _ = _menhir_action_45 x in
          _menhir_goto_option_SEMICOLON2_ _menhir_stack _tok
      | EOF ->
          let _ = _menhir_action_44 () in
          _menhir_goto_option_SEMICOLON2_ _menhir_stack _tok
      | _ ->
          _menhir_fail ()
  
  let rec _menhir_run_80_spec_00 : type  ttv_stack. ttv_stack -> _ -> _menhir_box_file =
    fun _menhir_stack _v ->
      MenhirBox_file _v
  
  let rec _menhir_run_84 : type  ttv_stack. (ttv_stack, _menhir_box_file) _menhir_cell1_command -> _ -> _menhir_box_file =
    fun _menhir_stack _v ->
      let MenhirCell1_command (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_31 _1 _3 in
      _menhir_goto_file _menhir_stack _v _menhir_s
  
  and _menhir_goto_file : type  ttv_stack. ttv_stack -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _menhir_box_file =
    fun _menhir_stack _v _menhir_s ->
      match _menhir_s with
      | MenhirState83 ->
          _menhir_run_84 _menhir_stack _v
      | MenhirState00 ->
          _menhir_run_80_spec_00 _menhir_stack _v
      | _ ->
          _menhir_fail ()
  
  let rec _menhir_run_25 : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | WITH ->
          let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState25
      | VAR _v_0 ->
          let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v_0 in
          let _v = _menhir_action_33 _1 in
          _menhir_run_44 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState25 _tok
      | TRUE ->
          let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_44 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState25 _tok
      | THIS ->
          let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_44 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState25 _tok
      | SKIP ->
          let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_44 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState25 _tok
      | PERIOD ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VAR _v_5 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | ASSIGN ->
                  let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
                  let _menhir_stack = MenhirCell1_PERIOD (_menhir_stack, MenhirState25) in
                  let _menhir_stack = MenhirCell0_VAR (_menhir_stack, _v_5) in
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | VAR _v_6 ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let _1 = _v_6 in
                      let _v = _menhir_action_33 _1 in
                      _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState28 _tok
                  | TRUE ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let _v = _menhir_action_35 () in
                      _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState28 _tok
                  | THIS ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let _v = _menhir_action_34 () in
                      _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState28 _tok
                  | SKIP ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let _v = _menhir_action_38 () in
                      _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState28 _tok
                  | NOT ->
                      _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState28
                  | LPAREN ->
                      _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState28
                  | LET ->
                      _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState28
                  | LBRACE ->
                      _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState28
                  | INT _v_11 ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let _1 = _v_11 in
                      let _v = _menhir_action_37 _1 in
                      _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState28 _tok
                  | IF ->
                      _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState28
                  | FUN ->
                      _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState28
                  | FALSE ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let _v = _menhir_action_36 () in
                      _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState28 _tok
                  | COPY ->
                      _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState28
                  | _ ->
                      _eRR ())
              | AND | COMMA | COPY | DIVIDE | ELSE | EOF | EQUAL | FALSE | IN | INT _ | LBRACE | LESS | LPAREN | MINUS | OR | PERIOD | PLUS | RBRACE | REMAINDER | RPAREN | SEMICOLON | SEMICOLON2 | SKIP | THEN | THIS | TIMES | TRUE | UNEQUAL | VAR _ | WITH ->
                  let (_1, _3) = (_v, _v_5) in
                  let _v = _menhir_action_40 _1 _3 in
                  _menhir_goto_non_app _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | LPAREN ->
          let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState25
      | LBRACE ->
          let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState25
      | INT _v_14 ->
          let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v_14 in
          let _v = _menhir_action_37 _1 in
          _menhir_run_44 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState25 _tok
      | FALSE ->
          let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_44 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState25 _tok
      | COPY ->
          let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState25
      | AND | COMMA | DIVIDE | ELSE | EOF | EQUAL | IN | LESS | MINUS | OR | PLUS | RBRACE | REMAINDER | RPAREN | SEMICOLON | SEMICOLON2 | THEN | TIMES | UNEQUAL ->
          let _1 = _v in
          let _v = _menhir_action_17 _1 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_21 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_non_app as 'stack) -> _ -> _ -> ('stack, ttv_result) _menhir_state -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_WITH (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState21 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState21 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState21 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState21 _tok
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState21
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState21
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState21 _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState21 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState21
      | _ ->
          _eRR ()
  
  and _menhir_run_22 : type  ttv_stack ttv_result. (((ttv_stack, ttv_result) _menhir_cell1_non_app, ttv_result) _menhir_cell1_WITH as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PERIOD ->
          let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | COPY | DIVIDE | ELSE | EOF | EQUAL | FALSE | IN | INT _ | LBRACE | LESS | LPAREN | MINUS | OR | PLUS | RBRACE | REMAINDER | RPAREN | SEMICOLON | SEMICOLON2 | SKIP | THEN | THIS | TIMES | TRUE | UNEQUAL | VAR _ | WITH ->
          let MenhirCell1_WITH (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_non_app (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_43 _1 _3 in
          _menhir_goto_non_app _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_23 : type  ttv_stack ttv_result. (ttv_stack, ttv_result) _menhir_cell1_non_app -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_non_app (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_40 _1 _3 in
          _menhir_goto_non_app _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_non_app : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState25 ->
          _menhir_run_44 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState34 ->
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState86 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState83 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState00 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState77 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState05 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState06 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState70 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState09 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState12 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState61 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState59 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState14 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState56 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState54 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState52 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState50 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState48 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState46 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState42 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState40 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState38 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState36 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState30 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState28 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState17 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState21 ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState19 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_44 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_non_app as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | WITH ->
          let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState44
      | PERIOD ->
          let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | COPY | DIVIDE | ELSE | EOF | EQUAL | FALSE | IN | INT _ | LBRACE | LESS | LPAREN | MINUS | OR | PLUS | RBRACE | REMAINDER | RPAREN | SEMICOLON | SEMICOLON2 | SKIP | THEN | THIS | TIMES | TRUE | UNEQUAL | VAR _ ->
          let MenhirCell1_non_app (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_03 _1 _2 in
          _menhir_goto_app _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_app : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | VAR _v_0 ->
          let _menhir_stack = MenhirCell1_app (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v_0 in
          let _v = _menhir_action_33 _1 in
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState34 _tok
      | TRUE ->
          let _menhir_stack = MenhirCell1_app (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState34 _tok
      | THIS ->
          let _menhir_stack = MenhirCell1_app (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState34 _tok
      | SKIP ->
          let _menhir_stack = MenhirCell1_app (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState34 _tok
      | LPAREN ->
          let _menhir_stack = MenhirCell1_app (_menhir_stack, _menhir_s, _v) in
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState34
      | LBRACE ->
          let _menhir_stack = MenhirCell1_app (_menhir_stack, _menhir_s, _v) in
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState34
      | INT _v_5 ->
          let _menhir_stack = MenhirCell1_app (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v_5 in
          let _v = _menhir_action_37 _1 in
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState34 _tok
      | FALSE ->
          let _menhir_stack = MenhirCell1_app (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState34 _tok
      | COPY ->
          let _menhir_stack = MenhirCell1_app (_menhir_stack, _menhir_s, _v) in
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState34
      | AND | COMMA | DIVIDE | ELSE | EOF | EQUAL | IN | LESS | MINUS | OR | PLUS | RBRACE | REMAINDER | RPAREN | SEMICOLON | SEMICOLON2 | THEN | TIMES | UNEQUAL ->
          let _1 = _v in
          let _v = _menhir_action_18 _1 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_35 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_app as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | WITH ->
          let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState35
      | PERIOD ->
          let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | COPY | DIVIDE | ELSE | EOF | EQUAL | FALSE | IN | INT _ | LBRACE | LESS | LPAREN | MINUS | OR | PLUS | RBRACE | REMAINDER | RPAREN | SEMICOLON | SEMICOLON2 | SKIP | THEN | THIS | TIMES | TRUE | UNEQUAL | VAR _ ->
          let MenhirCell1_app (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_02 _1 _2 in
          _menhir_goto_app _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_06 : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState06 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState06 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState06 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState06 _tok
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState06 _tok
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | FUN ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState06 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
      | _ ->
          _eRR ()
  
  and _menhir_run_05 : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_NOT (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState05 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState05 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState05 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState05 _tok
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState05 _tok
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | FUN ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState05 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState05
      | _ ->
          _eRR ()
  
  and _menhir_run_07 : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LET (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _menhir_stack = MenhirCell0_VAR (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | EQUAL ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | VAR _v_0 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _1 = _v_0 in
                  let _v = _menhir_action_33 _1 in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState09 _tok
              | TRUE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_35 () in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState09 _tok
              | THIS ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_34 () in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState09 _tok
              | SKIP ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_38 () in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState09 _tok
              | NOT ->
                  _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
              | LPAREN ->
                  _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
              | LET ->
                  _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
              | LBRACE ->
                  _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
              | INT _v_5 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _1 = _v_5 in
                  let _v = _menhir_action_37 _1 in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState09 _tok
              | IF ->
                  _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
              | FUN ->
                  _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
              | FALSE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_36 () in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState09 _tok
              | COPY ->
                  _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_10 : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LBRACE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState10
      | RBRACE ->
          let _v = _menhir_action_27 () in
          _menhir_run_64 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_run_11 : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_VAR (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | EQUAL ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VAR _v_0 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _1 = _v_0 in
              let _v = _menhir_action_33 _1 in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState12 _tok
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_35 () in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState12 _tok
          | THIS ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_34 () in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState12 _tok
          | SKIP ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_38 () in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState12 _tok
          | NOT ->
              _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState12
          | LPAREN ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState12
          | LET ->
              _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState12
          | LBRACE ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState12
          | INT _v_5 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _1 = _v_5 in
              let _v = _menhir_action_37 _1 in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState12 _tok
          | IF ->
              _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState12
          | FUN ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState12
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_36 () in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState12 _tok
          | COPY ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState12
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_14 : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState14 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState14 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState14 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState14 _tok
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState14 _tok
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
      | FUN ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState14 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
      | _ ->
          _eRR ()
  
  and _menhir_run_15 : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_FUN (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _menhir_stack = MenhirCell0_VAR (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ARROW ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | VAR _v_0 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _1 = _v_0 in
                  let _v = _menhir_action_33 _1 in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState17 _tok
              | TRUE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_35 () in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState17 _tok
              | THIS ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_34 () in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState17 _tok
              | SKIP ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_38 () in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState17 _tok
              | NOT ->
                  _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
              | LPAREN ->
                  _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
              | LET ->
                  _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
              | LBRACE ->
                  _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
              | INT _v_5 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _1 = _v_5 in
                  let _v = _menhir_action_37 _1 in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState17 _tok
              | IF ->
                  _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
              | FUN ->
                  _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
              | FALSE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_36 () in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState17 _tok
              | COPY ->
                  _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_19 : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_COPY (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState19 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState19 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState19 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState19 _tok
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState19
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState19
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState19 _tok
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState19 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState19
      | _ ->
          _eRR ()
  
  and _menhir_run_20 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_COPY as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | WITH ->
          let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState20
      | PERIOD ->
          let _menhir_stack = MenhirCell1_non_app (_menhir_stack, _menhir_s, _v) in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | COPY | DIVIDE | ELSE | EOF | EQUAL | FALSE | IN | INT _ | LBRACE | LESS | LPAREN | MINUS | OR | PLUS | RBRACE | REMAINDER | RPAREN | SEMICOLON | SEMICOLON2 | SKIP | THEN | THIS | TIMES | TRUE | UNEQUAL | VAR _ ->
          let MenhirCell1_COPY (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_42 _2 in
          _menhir_goto_non_app _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_64 : type  ttv_stack ttv_result. (ttv_stack, ttv_result) _menhir_cell1_LBRACE -> _ -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_LBRACE (_menhir_stack, _menhir_s) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_41 _2 in
      _menhir_goto_non_app _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_expr : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState86 ->
          _menhir_run_81 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState83 ->
          _menhir_run_81 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState00 ->
          _menhir_run_81 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState77 ->
          _menhir_run_78 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState05 ->
          _menhir_run_74 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState06 ->
          _menhir_run_72 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState70 ->
          _menhir_run_71 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState09 ->
          _menhir_run_69 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState12 ->
          _menhir_run_63 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState61 ->
          _menhir_run_62 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState59 ->
          _menhir_run_60 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState14 ->
          _menhir_run_58 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState56 ->
          _menhir_run_57 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState54 ->
          _menhir_run_55 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState52 ->
          _menhir_run_53 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState50 ->
          _menhir_run_51 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState48 ->
          _menhir_run_49 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState46 ->
          _menhir_run_47 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState17 ->
          _menhir_run_45 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState42 ->
          _menhir_run_43 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState40 ->
          _menhir_run_41 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState38 ->
          _menhir_run_39 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState36 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState30 ->
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState28 ->
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_81 : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | UNEQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_46 _menhir_stack _menhir_lexbuf _menhir_lexer
      | TIMES ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SEMICOLON ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_50 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LESS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_52 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EOF | SEMICOLON2 ->
          let _1 = _v in
          let _v = _menhir_action_15 _1 in
          _menhir_goto_command _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_46 : type  ttv_stack ttv_result. (ttv_stack, ttv_result) _menhir_cell1_expr -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState46 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState46 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState46 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState46 _tok
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState46
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState46
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState46
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState46
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState46 _tok
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState46
      | FUN ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState46
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState46 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState46
      | _ ->
          _eRR ()
  
  and _menhir_run_30 : type  ttv_stack ttv_result. (ttv_stack, ttv_result) _menhir_cell1_expr -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState30 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState30 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState30 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState30 _tok
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState30
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState30
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState30
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState30
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState30 _tok
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState30
      | FUN ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState30
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState30 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState30
      | _ ->
          _eRR ()
  
  and _menhir_run_48 : type  ttv_stack ttv_result. (ttv_stack, ttv_result) _menhir_cell1_expr -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState48 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState48 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState48 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState48 _tok
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState48
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState48
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState48
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState48
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState48 _tok
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState48
      | FUN ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState48
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState48 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState48
      | _ ->
          _eRR ()
  
  and _menhir_run_36 : type  ttv_stack ttv_result. (ttv_stack, ttv_result) _menhir_cell1_expr -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState36 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState36 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState36 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState36 _tok
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState36
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState36
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState36
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState36
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState36 _tok
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState36
      | FUN ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState36
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState36 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState36
      | _ ->
          _eRR ()
  
  and _menhir_run_38 : type  ttv_stack ttv_result. (ttv_stack, ttv_result) _menhir_cell1_expr -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState38 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState38 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState38 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState38 _tok
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState38
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState38
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState38
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState38
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState38 _tok
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState38
      | FUN ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState38
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState38 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState38
      | _ ->
          _eRR ()
  
  and _menhir_run_50 : type  ttv_stack ttv_result. (ttv_stack, ttv_result) _menhir_cell1_expr -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState50 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState50 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState50 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState50 _tok
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState50
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState50
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState50
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState50
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState50 _tok
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState50
      | FUN ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState50
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState50 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState50
      | _ ->
          _eRR ()
  
  and _menhir_run_42 : type  ttv_stack ttv_result. (ttv_stack, ttv_result) _menhir_cell1_expr -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState42 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState42 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState42 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState42 _tok
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState42
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState42
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState42
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState42
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState42 _tok
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState42
      | FUN ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState42
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState42 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState42
      | _ ->
          _eRR ()
  
  and _menhir_run_52 : type  ttv_stack ttv_result. (ttv_stack, ttv_result) _menhir_cell1_expr -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState52 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState52 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState52 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState52 _tok
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState52
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState52
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState52
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState52
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState52 _tok
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState52
      | FUN ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState52
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState52 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState52
      | _ ->
          _eRR ()
  
  and _menhir_run_54 : type  ttv_stack ttv_result. (ttv_stack, ttv_result) _menhir_cell1_expr -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState54 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState54 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState54 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState54 _tok
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState54
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState54
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState54
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState54
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState54 _tok
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState54
      | FUN ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState54
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState54 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState54
      | _ ->
          _eRR ()
  
  and _menhir_run_40 : type  ttv_stack ttv_result. (ttv_stack, ttv_result) _menhir_cell1_expr -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState40 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState40 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState40 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState40 _tok
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState40
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState40
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState40
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState40
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState40 _tok
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState40
      | FUN ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState40
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState40 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState40
      | _ ->
          _eRR ()
  
  and _menhir_run_56 : type  ttv_stack ttv_result. (ttv_stack, ttv_result) _menhir_cell1_expr -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState56 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState56 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState56 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState56 _tok
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState56
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState56
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState56
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState56
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState56 _tok
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState56
      | FUN ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState56
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState56 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState56
      | _ ->
          _eRR ()
  
  and _menhir_goto_command : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState86 ->
          _menhir_run_88 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState83 ->
          _menhir_run_82 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState00 ->
          _menhir_run_82 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_82 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_file) _menhir_state -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMICOLON2 ->
          let _menhir_stack = MenhirCell1_command (_menhir_stack, _menhir_s, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VAR _v_0 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _1 = _v_0 in
              let _v = _menhir_action_33 _1 in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState83 _tok
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_35 () in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState83 _tok
          | THIS ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_34 () in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState83 _tok
          | SKIP ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_38 () in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState83 _tok
          | NOT ->
              _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState83
          | LPAREN ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState83
          | LET ->
              _menhir_run_75 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState83
          | LBRACE ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState83
          | INT _v_5 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _1 = _v_5 in
              let _v = _menhir_action_37 _1 in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState83 _tok
          | IF ->
              _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState83
          | FUN ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState83
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_36 () in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState83 _tok
          | EOF ->
              let _v = _menhir_action_30 () in
              _menhir_run_84 _menhir_stack _v
          | COPY ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState83
          | _ ->
              _eRR ())
      | EOF ->
          let _1 = _v in
          let _v = _menhir_action_32 _1 in
          _menhir_goto_file _menhir_stack _v _menhir_s
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_75 : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LET (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _menhir_stack = MenhirCell0_VAR (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | EQUAL ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | VAR _v_0 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _1 = _v_0 in
                  let _v = _menhir_action_33 _1 in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState77 _tok
              | TRUE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_35 () in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState77 _tok
              | THIS ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_34 () in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState77 _tok
              | SKIP ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_38 () in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState77 _tok
              | NOT ->
                  _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
              | LPAREN ->
                  _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
              | LET ->
                  _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
              | LBRACE ->
                  _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
              | INT _v_5 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _1 = _v_5 in
                  let _v = _menhir_action_37 _1 in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState77 _tok
              | IF ->
                  _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
              | FUN ->
                  _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
              | FALSE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let _v = _menhir_action_36 () in
                  _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState77 _tok
              | COPY ->
                  _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState77
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_78 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_LET _menhir_cell0_VAR as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | UNEQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_46 _menhir_stack _menhir_lexbuf _menhir_lexer
      | TIMES ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SEMICOLON ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_50 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LESS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_52 _menhir_stack _menhir_lexbuf _menhir_lexer
      | IN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_70 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EOF | SEMICOLON2 ->
          let MenhirCell0_VAR (_menhir_stack, _2) = _menhir_stack in
          let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
          let _4 = _v in
          let _v = _menhir_action_16 _2 _4 in
          _menhir_goto_command _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_70 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_LET _menhir_cell0_VAR, ttv_result) _menhir_cell1_expr -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState70 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState70 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState70 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState70 _tok
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState70
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState70
      | LET ->
          _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState70
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState70
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState70 _tok
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState70
      | FUN ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState70
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState70 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState70
      | _ ->
          _eRR ()
  
  and _menhir_run_74 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_NOT as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | UNEQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_46 _menhir_stack _menhir_lexbuf _menhir_lexer
      | TIMES ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LESS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_52 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | ELSE | EOF | IN | OR | RBRACE | RPAREN | SEMICOLON | SEMICOLON2 | THEN ->
          let MenhirCell1_NOT (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_09 _2 in
          _menhir_goto_boolean _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_boolean : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_20 _1 in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_72 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | UNEQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_46 _menhir_stack _menhir_lexbuf _menhir_lexer
      | TIMES ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SEMICOLON ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_39 _2 in
          _menhir_goto_non_app _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | REMAINDER ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_50 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LESS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_52 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_71 : type  ttv_stack ttv_result. (((ttv_stack, ttv_result) _menhir_cell1_LET _menhir_cell0_VAR, ttv_result) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | UNEQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_46 _menhir_stack _menhir_lexbuf _menhir_lexer
      | TIMES ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SEMICOLON ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_50 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LESS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_52 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | ELSE | EOF | IN | RBRACE | RPAREN | SEMICOLON2 | THEN ->
          let MenhirCell1_expr (_menhir_stack, _, _4) = _menhir_stack in
          let MenhirCell0_VAR (_menhir_stack, _2) = _menhir_stack in
          let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
          let _6 = _v in
          let _v = _menhir_action_23 _2 _4 _6 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_69 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_LET _menhir_cell0_VAR as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | UNEQUAL ->
          _menhir_run_46 _menhir_stack _menhir_lexbuf _menhir_lexer
      | TIMES ->
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SEMICOLON ->
          _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_50 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LESS ->
          _menhir_run_52 _menhir_stack _menhir_lexbuf _menhir_lexer
      | IN ->
          _menhir_run_70 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQUAL ->
          _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_63 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_VAR as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | UNEQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_46 _menhir_stack _menhir_lexbuf _menhir_lexer
      | TIMES ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SEMICOLON ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_50 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LESS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_52 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | RBRACE ->
          let MenhirCell1_VAR (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_26 _1 _3 in
          (match (_tok : MenhirBasics.token) with
          | COMMA ->
              let _menhir_stack = MenhirCell1_field (_menhir_stack, _menhir_s, _v) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | VAR _v ->
                  _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState67
              | RBRACE ->
                  let _v = _menhir_action_27 () in
                  _menhir_run_68 _menhir_stack _menhir_lexbuf _menhir_lexer _v
              | _ ->
                  _eRR ())
          | RBRACE ->
              let _1 = _v in
              let _v = _menhir_action_28 _1 in
              _menhir_goto_fields _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _menhir_fail ())
      | _ ->
          _eRR ()
  
  and _menhir_run_68 : type  ttv_stack ttv_result. (ttv_stack, ttv_result) _menhir_cell1_field -> _ -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_field (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_29 _1 _3 in
      _menhir_goto_fields _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_fields : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState67 ->
          _menhir_run_68 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState10 ->
          _menhir_run_64 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_62 : type  ttv_stack ttv_result. ((((ttv_stack, ttv_result) _menhir_cell1_IF, ttv_result) _menhir_cell1_expr, ttv_result) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | UNEQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_46 _menhir_stack _menhir_lexbuf _menhir_lexer
      | TIMES ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_50 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LESS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_52 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | ELSE | EOF | IN | RBRACE | RPAREN | SEMICOLON | SEMICOLON2 | THEN ->
          let MenhirCell1_expr (_menhir_stack, _, _4) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _, _2) = _menhir_stack in
          let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
          let _6 = _v in
          let _v = _menhir_action_21 _2 _4 _6 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_60 : type  ttv_stack ttv_result. (((ttv_stack, ttv_result) _menhir_cell1_IF, ttv_result) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | UNEQUAL ->
          _menhir_run_46 _menhir_stack _menhir_lexbuf _menhir_lexer
      | TIMES ->
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SEMICOLON ->
          _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_50 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LESS ->
          _menhir_run_52 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQUAL ->
          _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VAR _v_0 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _1 = _v_0 in
              let _v = _menhir_action_33 _1 in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState61 _tok
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_35 () in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState61 _tok
          | THIS ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_34 () in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState61 _tok
          | SKIP ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_38 () in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState61 _tok
          | NOT ->
              _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState61
          | LPAREN ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState61
          | LET ->
              _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState61
          | LBRACE ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState61
          | INT _v_5 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _1 = _v_5 in
              let _v = _menhir_action_37 _1 in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState61 _tok
          | IF ->
              _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState61
          | FUN ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState61
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_36 () in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState61 _tok
          | COPY ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState61
          | _ ->
              _eRR ())
      | DIVIDE ->
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_58 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | UNEQUAL ->
          _menhir_run_46 _menhir_stack _menhir_lexbuf _menhir_lexer
      | TIMES ->
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | THEN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VAR _v_0 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _1 = _v_0 in
              let _v = _menhir_action_33 _1 in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState59 _tok
          | TRUE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_35 () in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState59 _tok
          | THIS ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_34 () in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState59 _tok
          | SKIP ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_38 () in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState59 _tok
          | NOT ->
              _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState59
          | LPAREN ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState59
          | LET ->
              _menhir_run_07 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState59
          | LBRACE ->
              _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState59
          | INT _v_5 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _1 = _v_5 in
              let _v = _menhir_action_37 _1 in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState59 _tok
          | IF ->
              _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState59
          | FUN ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState59
          | FALSE ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_36 () in
              _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState59 _tok
          | COPY ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState59
          | _ ->
              _eRR ())
      | SEMICOLON ->
          _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_50 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LESS ->
          _menhir_run_52 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQUAL ->
          _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_57 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | UNEQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_46 _menhir_stack _menhir_lexbuf _menhir_lexer
      | TIMES ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LESS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_52 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | ELSE | EOF | IN | OR | RBRACE | RPAREN | SEMICOLON | SEMICOLON2 | THEN ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_13 _1 _3 in
          _menhir_goto_boolean _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_55 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | TIMES ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | ELSE | EOF | IN | OR | RBRACE | RPAREN | SEMICOLON | SEMICOLON2 | THEN ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_11 _1 _3 in
          _menhir_goto_boolean _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_53 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | TIMES ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | ELSE | EOF | IN | OR | RBRACE | RPAREN | SEMICOLON | SEMICOLON2 | THEN ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_10 _1 _3 in
          _menhir_goto_boolean _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_51 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | UNEQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_46 _menhir_stack _menhir_lexbuf _menhir_lexer
      | TIMES ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LESS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_52 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | ELSE | EOF | IN | OR | RBRACE | RPAREN | SEMICOLON | SEMICOLON2 | THEN ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_14 _1 _3 in
          _menhir_goto_boolean _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_49 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | UNEQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_46 _menhir_stack _menhir_lexbuf _menhir_lexer
      | TIMES ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SEMICOLON ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_50 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LESS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_52 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | ELSE | EOF | IN | RBRACE | RPAREN | SEMICOLON2 | THEN ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_25 _1 _3 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_47 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | TIMES ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | ELSE | EOF | IN | OR | RBRACE | RPAREN | SEMICOLON | SEMICOLON2 | THEN ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_12 _1 _3 in
          _menhir_goto_boolean _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_45 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_FUN _menhir_cell0_VAR as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | UNEQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_46 _menhir_stack _menhir_lexbuf _menhir_lexer
      | TIMES ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SEMICOLON ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_48 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_50 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LESS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_52 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQUAL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_56 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | ELSE | EOF | IN | RBRACE | RPAREN | SEMICOLON2 | THEN ->
          let MenhirCell0_VAR (_menhir_stack, _2) = _menhir_stack in
          let MenhirCell1_FUN (_menhir_stack, _menhir_s) = _menhir_stack in
          let _4 = _v in
          let _v = _menhir_action_22 _2 _4 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_43 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | TIMES ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | ELSE | EOF | EQUAL | IN | LESS | MINUS | OR | PLUS | RBRACE | RPAREN | SEMICOLON | SEMICOLON2 | THEN | UNEQUAL ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_05 _1 _3 in
          _menhir_goto_arith _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_arith : type  ttv_stack ttv_result. ttv_stack -> _ -> _ -> _ -> (ttv_stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_19 _1 in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_41 : type  ttv_stack ttv_result. (ttv_stack, ttv_result) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_07 _1 _3 in
      _menhir_goto_arith _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_39 : type  ttv_stack ttv_result. ((ttv_stack, ttv_result) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | TIMES ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | ELSE | EOF | EQUAL | IN | LESS | MINUS | OR | PLUS | RBRACE | RPAREN | SEMICOLON | SEMICOLON2 | THEN | UNEQUAL ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_04 _1 _3 in
          _menhir_goto_arith _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_37 : type  ttv_stack ttv_result. (ttv_stack, ttv_result) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_08 _1 _3 in
      _menhir_goto_arith _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_31 : type  ttv_stack ttv_result. (ttv_stack, ttv_result) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_06 _1 _3 in
      _menhir_goto_arith _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_29 : type  ttv_stack ttv_result. (((ttv_stack, ttv_result) _menhir_cell1_non_app, ttv_result) _menhir_cell1_PERIOD _menhir_cell0_VAR as 'stack) -> _ -> _ -> _ -> ('stack, ttv_result) _menhir_state -> _ -> ttv_result =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | TIMES ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer
      | REMAINDER ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIVIDE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | COMMA | ELSE | EOF | EQUAL | IN | LESS | OR | RBRACE | RPAREN | SEMICOLON | SEMICOLON2 | THEN | UNEQUAL ->
          let MenhirCell0_VAR (_menhir_stack, _3) = _menhir_stack in
          let MenhirCell1_PERIOD (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_non_app (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _5 = _v in
          let _v = _menhir_action_24 _1 _3 _5 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  let rec _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_file =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00 _tok
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | LET ->
          _menhir_run_75 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00 _tok
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | FUN ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState00 _tok
      | EOF ->
          let _v = _menhir_action_30 () in
          _menhir_run_80_spec_00 _menhir_stack _v
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | _ ->
          _eRR ()
  
  let rec _menhir_run_86 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_toplevel =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_33 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState86 _tok
      | TRUE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_35 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState86 _tok
      | THIS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_34 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState86 _tok
      | SKIP ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_38 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState86 _tok
      | NOT ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState86
      | LPAREN ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState86
      | LET ->
          _menhir_run_75 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState86
      | LBRACE ->
          _menhir_run_10 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState86
      | INT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _1 = _v in
          let _v = _menhir_action_37 _1 in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState86 _tok
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState86
      | FUN ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState86
      | FALSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_36 () in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState86 _tok
      | COPY ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState86
      | _ ->
          _eRR ()
  
end

let toplevel =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_toplevel v = _menhir_run_86 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v

let file =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_file v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v

# 109 "lib/Parser.mly"
  


# 3246 "lib/Parser.ml"
