open Peano  (* definicja typu axiom, np. EqRefl, EqElim, PlusZ, PlusS, Induction *)

open Logic

(* Tworzymy instancję logiki z teorią Peano *)
module Logic = Logic.Make(Peano)

(* Dla wygody "otwieramy" moduł L - wtedy reguły i typ theorem są w zasięgu *)
open Logic



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
  let phi_n = Rel("=", [ Sym("+", [Var "n"; Sym("z", []) ]); Var "n" ]) in
  (* φ(n) ≡ n + 0 = n *)
  let induction_ax = axiom (Induction("n", phi_n)) in
  (* 0 + 0 = 0 => (∀n.n + 0 = n => S(n) + 0 = S(n)) => ∀n.n + 0 = n *)

  (* Dowód bazy indukcyjnej: 0 + 0 = 0 *)

  let base_case = forall_e (axiom PlusZ) (Sym("z", [])) in
  (* 0 + 0 = 0 *)

  (* Dowód kroku indukcyjnego: ∀n.n+0 = n => S(n) + 0 = S(n) *)

  let plusS_inst1 = forall_e (axiom PlusS) (Var "n") in
  let plusS_inst2 = forall_e plusS_inst1 (Sym("z", [])) in
  (* S(n)+0 = S(n+0) *)

  let step_assumption = by_assumption phi_n in
  (* {n+0=n} ⊢ n+0=n *)
  let ax_eqelim = axiom (EqElim("u", Rel("=", [ Sym("+", [Sym("s",[Var "n"]); Sym("z", [])]); Sym("s",[Var "u"]) ]))) in
  (* ax_eqelim: ⊢ ∀y.∀z.y = z => S(n)+0 = S(y) => S(n)+0 = S(z)  *)
  let eqelim_inst1 = forall_e ax_eqelim (Sym("+",[Var "n"; Sym("z",[])])) in
  let eqelim_inst2 = forall_e eqelim_inst1 (Var "n") in
  (* n+0 = n => S(n)+0 = S(n+0) => S(n)+0 = S(n)  *)
  let step_eqelim = imp_e eqelim_inst2 step_assumption in
  (* S(n)+0 = S(n+0) => S(n+0) = S(n). *)
  let step = imp_e step_eqelim plusS_inst2 in
  (* S(n+0)=S(n) *)

  (* Zamykamy założenie "n+0 = n" *)
  let induction_step = imp_i (Rel("=", [ Sym("+",[Var "n"; Sym("z",[]) ]); Var "n"])) step in
  (* (n+0 = n) => (S(n)+0 = S(n)) *)

  let step_forall_n = forall_i "n" induction_step in
  (* ∀n.n+0=n => S(n)+0=S(n) *)

  (* Dowód twierdzenia korzystający z bazy i z kroku *)

  let step_ind1 = imp_e induction_ax base_case in
  let step_ind2 = imp_e step_ind1 step_forall_n in
  (* ∀n. n+0=n *)

  step_ind2
;;