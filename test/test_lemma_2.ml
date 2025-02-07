open Proof_assistant.Peano  (* definicja typu axiom, np. EqRefl, EqElim, PlusZ, PlusS, Induction *)

open Proof_assistant.Logic

(* Tworzymy instancję logiki z teorią Peano *)
module LogicPeano = Make(Peano)

(* Dla wygody "otwieramy" moduł L - wtedy reguły i typ theorem są w zasięgu *)
open LogicPeano



(** 
  Lemat 2: ∀n. n + 0 = n

  Dowód przez indukcję:
  - Podstawa: 0 + 0 = 0 (z aksjomatu [PlusZ]).
  - Krok: jeśli n + 0 = n, to S(n) + 0 = S(n):
    + Z aksjomatu [PlusS] mamy S(n)+0 = S(n+0),
    + Z zał. indukcyjnego n+0=n i aksjomatu [EqElim] wnioskujemy S(n+0) = S(n),
    + łącząc oba fakty, mamy S(n)+0 = S(n).
 *)
 let lemma2 : theorem =
  let n = fresh_var ~base:"n" () in
  let phi_n = Rel("=", [ Sym("+", [Var n; Sym("z", []) ]); Var n ]) in
  (* φ(n) ≡ n + 0 = n *)
  let induction_ax = axiom (Induction(n, phi_n)) in
  (* 0 + 0 = 0 => (∀n.n + 0 = n => S(n) + 0 = S(n)) => ∀n.n + 0 = n *)

  (* Dowód bazy indukcyjnej: 0 + 0 = 0 *)

  let base_case = forall_e (axiom PlusZ) (Sym("z", [])) in
  (* 0 + 0 = 0 *)

  (* Dowód kroku indukcyjnego: ∀n.n+0 = n => S(n) + 0 = S(n) *)

  let plusS_inst1 = forall_e (axiom PlusS) (Var n) in
  let plusS_inst2 = forall_e plusS_inst1 (Sym("z", [])) in
  (* S(n)+0 = S(n+0) *)

  let step_assumption = by_assumption phi_n in
  (* {n+0=n} ⊢ n+0=n *)
  let u = fresh_var ~base:"u" () in
  let eqelim_phi =
    Rel("=", [ Sym("+",[ Sym("s",[Var n]); Sym("z",[]) ]);
               Sym("s",[Var u]) ])
  in
  let ax_eqelim = axiom (EqElim(u, eqelim_phi)) in
  (* ax_eqelim: ⊢ ∀y.∀z.y = z => S(n)+0 = S(y) => S(n)+0 = S(z)  *)
  let eqelim_inst1 = forall_e ax_eqelim (Sym("+",[Var n; Sym("z",[])])) in
  let eqelim_inst2 = forall_e eqelim_inst1 (Var n) in
  (* n+0 = n => S(n)+0 = S(n+0) => S(n)+0 = S(n)  *)
  let step_eqelim = imp_e eqelim_inst2 step_assumption in
  (* S(n)+0 = S(n+0) => S(n+0) = S(n). *)
  let step = imp_e step_eqelim plusS_inst2 in
  (* S(n+0)=S(n) *)

  (* Zamykamy założenie "n+0 = n" *)
  let induction_step = imp_i (Rel("=", [ Sym("+",[Var n; Sym("z",[]) ]); Var n])) step in
  (* (n+0 = n) => (S(n)+0 = S(n)) *)

  let step_forall_n = forall_i n induction_step in
  (* ∀n.n+0=n => S(n)+0=S(n) *)

  (* Dowód twierdzenia korzystający z bazy i z kroku *)

  let step_ind1 = imp_e induction_ax base_case in
  let step_ind2 = imp_e step_ind1 step_forall_n in
  (* ∀n. n+0=n *)

  step_ind2
;;

(*
  We can wrap the proof in an Alcotest test to ensure lemma2 concludes
  with the correct formula:  ∀n. (n+0 = n).
*)

open Alcotest

let test_lemma2_conclusion () =
  let concl = conclusion lemma2 in
  (* We expect the conclusion to be ∀n. (n+0=n).
     The naive eq_formula works here because the bound var "n" in lemma2
     and the "n" we build here match textually (and share the same ID
     if they are both created fresh in a single run). If you see
     false negatives, you may need a more robust alpha-equivalence check.
  *)
  let n_test = fresh_var ~base:"n" () in
  let expected = All(n_test, Rel("=", [ Sym("+",[Var n_test; Sym("z",[])]); Var n_test])) in
  check bool "Lemma2 conclusion == ∀n. n+0=n" true (eq_formula concl expected)

let suite = [
  test_case "Lemma2: ∀n. n + 0 = n" `Quick test_lemma2_conclusion;
]

let () =
  Alcotest.run "Lemma2 Test" [
    "Peano Lemma2", suite
  ]