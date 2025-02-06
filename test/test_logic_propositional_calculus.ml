

open Alcotest
open Proof_assistant.Peano
open Proof_assistant.Logic

module LogicPeano = Make(Peano)

open LogicPeano

(** Define test cases *)

let p = Rel("p", [])
let q = Rel("q", [])
let r = Rel("r", [])


let test_implication_identity () =
  let t1 = imp_i p (by_assumption p) in
  let expected = Imp(p, p) in
  check bool "p → p" true (eq_formula (conclusion t1) expected)

let test_nested_implication () =
  let t2 = imp_i p (imp_i q (by_assumption p)) in
  let expected = Imp(p, Imp(q, p)) in
  check bool "p → q → p" true (eq_formula (conclusion t2) expected)

let test_complex_implication () =
  let f1 = Imp(p, Imp(q, r)) in (* p → q → r *)
  let f2 = Imp(p, q) in (* p → q *)
  let c1 = by_assumption f1 in
  let c2 = by_assumption f2 in
  let c3 = by_assumption p in

  let t3 =
    imp_e (imp_e c1 c3) (imp_e c2 c3)
    |> imp_i p
    |> imp_i f2
    |> imp_i f1
  in

  let expected = Imp(f1, Imp(f2, Imp(p, r))) in
  check bool "(p → q → r) → (p → q) → p → r" true (eq_formula (conclusion t3) expected)

let test_bottom_elimination () =
  let t4 = imp_i Bot (bot_e p (by_assumption Bot)) in
  let expected = Imp(Bot, p) in
  check bool "⊥ → p" true (eq_formula (conclusion t4) expected)

(** Register test cases *)
let suite = [
  test_case "Implication Identity: ⊢ p → p" `Quick test_implication_identity;
  test_case "Nested Implication: ⊢ p → q → p" `Quick test_nested_implication;
  test_case "Complex Implication: ⊢ (p → q → r) → (p → q) → p → r" `Quick test_complex_implication;
  test_case "Bottom Elimination: ⊢ ⊥ → p" `Quick test_bottom_elimination;
]

let () =
  Alcotest.run "Logic Propositional Calculus Tests" [
    "Propositional", suite
  ]
