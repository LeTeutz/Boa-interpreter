(* open OUnit2
open Libs_core.Syntax

let eq (exp: string) (input: string) =
  assert_equal exp (Libs_core.Eval.test input)

let tests_easy _ =
  eq "3"  "let x = 1 in let y = 2 in x + y";
  eq "6"  "let x = 1 in let y = 2 in x + y + 3";
  eq "4"  "2 + 2";
  eq "12" "(if 2 < 4 then 10 else 100) + 2";
  eq "57" "(fun x -> x * x + x + 1) 7"

let tests_medium _ =
  eq "{x=10, y=8}" "let p = {x = 7, y = 8};;\n p.x := 10;; p\n"

let suite = 
  "Tests" >::: [
    "Easy tests" >:: tests_easy;
    "Medium tests" >:: tests_medium
  ]

let _ = run_test_tt_main suite *)