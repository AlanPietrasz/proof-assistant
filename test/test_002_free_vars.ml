(* ./test/test_002_free_vars.ml *)

open Alcotest
open Proof_assistant.Logic

module TestFreeVars = struct
  let x = "x"
  let y = "y"
  let z = "z"

  let term1 = Var x
  let term2 = Sym("f", [Var x; Sym("g", [Var y])])
  let term3 = Sym("c", [])

  let formula1 = Rel("p", [Var x; Sym("g", [Var y])])
  let formula2 = All(x, Rel("p", [Var x]))
  let formula3 = Imp(Rel("p", [Var y]), Bot)

  (* Test free_in_term *)
  let test_free_in_term_simple () =
    check bool "x is free in Var x" true (free_in_term x term1);
    check bool "y is not free in Var x" false (free_in_term y term1);
    check bool "z is not free in Sym c []" false (free_in_term z term3)

  let test_free_in_term_nested () =
    check bool "x is free in f(x, g(y))" true (free_in_term x term2);
    check bool "y is free in f(x, g(y))" true (free_in_term y term2);
    check bool "z is not free in f(x, g(y))" false (free_in_term z term2)

  (* Test free_in_formula *)
  let test_free_in_formula_rel () =
    check bool "x is free in p(x, g(y))" true (free_in_formula x formula1);
    check bool "y is free in p(x, g(y))" true (free_in_formula y formula1);
    check bool "z is not free in p(x, g(y))" false (free_in_formula z formula1)

  let test_free_in_formula_all () =
    (* All(x, p(x)) binds x, so x is not free there *)
    check bool "x not free in ∀x. p(x)" false (free_in_formula x formula2);
    check bool "y not free in ∀x. p(x)" true  (free_in_formula y formula2);
    check bool "z not free in ∀x. p(x)" false (free_in_formula z formula2)

  let test_free_in_formula_imp () =
    check bool "y free in p(y) → ⊥" true (free_in_formula y formula3);
    check bool "x free in p(y) → ⊥" false (free_in_formula x formula3)
end

let suite = [
  test_case "free_in_term simple"    `Quick TestFreeVars.test_free_in_term_simple;
  test_case "free_in_term nested"    `Quick TestFreeVars.test_free_in_term_nested;
  test_case "free_in_formula Rel"    `Quick TestFreeVars.test_free_in_formula_rel;
  test_case "free_in_formula All"    `Quick TestFreeVars.test_free_in_formula_all;
  test_case "free_in_formula Imp"    `Quick TestFreeVars.test_free_in_formula_imp;
]

let () =
  Alcotest.run "Free Vars Tests" [
    "free_vars", suite
  ]
