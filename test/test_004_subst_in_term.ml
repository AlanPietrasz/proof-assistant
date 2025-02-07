(* ./test/test_004_subst_in_term.ml *)

open Alcotest
open Proof_assistant.Logic

module TestSubstTerm = struct
  let x = fresh_var ~base:"x" ()
  let y = fresh_var ~base:"y" ()
  let z = fresh_var ~base:"z" ()

  let t_var_x = Var x
  let t_var_y = Var y
  let t_sym_f_xy = Sym("f", [Var x; Var y])
  let t_sym_g_z  = Sym("g", [Var z])

  let test_subst_no_occurrences () =
    (* Substituting x with g(z) in a term that has no 'x' occurrences  *)
    let result = subst_in_term x t_sym_g_z (Var y) in
    check string "y remains y" "y" (string_of_term result)

  let test_subst_in_var () =
    let result = subst_in_term x t_sym_g_z t_var_x in
    check string "x{x->g(z)} => g(z)" "g(z)" (string_of_term result)

  let test_subst_in_nested_sym () =
    (* f(x, y){x->g(z)} => f(g(z), y) *)
    let result = subst_in_term x t_sym_g_z t_sym_f_xy in
    check string "f(x,y){x->g(z)} => f(g(z),y)"
      "f(g(z), y)" (string_of_term result)
end

let suite = [
  test_case "subst_in_term no occurrences" `Quick TestSubstTerm.test_subst_no_occurrences;
  test_case "subst_in_term in var"         `Quick TestSubstTerm.test_subst_in_var;
  test_case "subst_in_term in nested sym"  `Quick TestSubstTerm.test_subst_in_nested_sym;
]

let () =
  Alcotest.run "Subst In Term Tests" [
    "subst_in_term", suite
  ]
