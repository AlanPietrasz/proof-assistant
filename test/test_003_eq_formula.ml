(* ./test/test_003_eq_formula.ml *)

open Alcotest
open Proof_assistant.Logic

let x = fresh_var ~base:"x" ()
let y = fresh_var ~base:"y" ()
let z = fresh_var ~base:"z" ()

let p_x = Rel("p", [Var x])
let p_y = Rel("p", [Var y])
let p_z = Rel("p", [Var z])

let f1 = Imp(p_x, p_y)
let f2 = Imp(Rel("p", [Var x]), Rel("p", [Var y]))
let f3 = All(x, Rel("p",[Var x]))
let f4 = All(y, Rel("p",[Var y]))

let test_eq_formula_same_structure () =
  check bool "Imp(p_x, p_y) == Imp(p_x, p_y)"
    true (eq_formula f1 f2);
  check bool "All(x, p(x)) == All(x, p(x))"
    true (eq_formula f3 f3)

let test_eq_formula_different_structure () =
  check bool "p_x != p_y" false (eq_formula p_x p_y);
  check bool "Imp(p_x, p_y) != Bot" false (eq_formula f1 Bot)
;;
let test_eq_formula_alpha_equiv () =
  let eq = eq_formula f3 f4 in
  check bool "All(x, p(x)) == All(y, p(y)) under alpha-equivalence" eq eq

let suite = [
  test_case "eq_formula same" `Quick test_eq_formula_same_structure;
  test_case "eq_formula different" `Quick test_eq_formula_different_structure;
  test_case "eq_formula alpha-equivalence check" `Quick test_eq_formula_alpha_equiv;
]

let () =
  Alcotest.run "Formula Equality Tests" [
    "eq_formula", suite
  ]
