open Alcotest

open Proof_assistant.Logic

(** Pretty print test *)
let neg_f p = Imp(p, Bot)
let and_f p q =
  neg_f (Imp(p, neg_f q))
let p = (Rel("p", []))
let q = (Rel("q", []))
let f_t1 = Imp(Imp(p, Bot), Imp(p, q)) ;;

(* let x = (Var "x") *)
let phi = (Rel("φ", []))
let psi = (Rel("ψ", []))
let f_t2 = 
  Imp(
    All("x", and_f phi psi),
    and_f
      (All("x", phi))
      (All("x", psi))
  )


(** Helper function for pretty-print testing *)
let format_formula f =
  let buf = Buffer.create 50 in
  let fmt = Format.formatter_of_buffer buf in
  pp_print_formula fmt f;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

(** Test cases for pretty-printing *)
let test_negation_printing () =
  let expected = "p → ⊥" in
  check string "Pretty print of ¬p" expected (format_formula (neg_f p))

let test_and_printing () =
  let expected = "(p → q → ⊥) → ⊥" in
  check string "Pretty print of (p ∧ q)" expected (format_formula (and_f p q))

let test_complex_formula_1 () =
  let expected = "(p → ⊥) → p → q" in
  check string "Pretty print of f_t1" expected (format_formula f_t1)

let test_complex_formula_2 () =
  let expected = "(∀x.(φ → ψ → ⊥) → ⊥) → ((∀x.φ) → (∀x.ψ) → ⊥) → ⊥" in
  check string "Pretty print of f_t2" expected (format_formula f_t2)

(** Register test cases *)
let suite = [
  test_case "Negation: ¬p as p → ⊥" `Quick test_negation_printing;
  test_case "Conjunction: p ∧ q as (p → (q → ⊥)) → ⊥" `Quick test_and_printing;
  test_case "Complex formula 1" `Quick test_complex_formula_1;
  test_case "Complex formula 2" `Quick test_complex_formula_2;
]

let () =
  Alcotest.run "Pretty Printing Tests" [
    "Pretty-printing", suite
  ]