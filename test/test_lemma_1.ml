(**
  Lemat 1: ∀x. ∀y. x = y → y = x

  Sketch of the proof:

  1. We want to show x=y → y=x.
     - Assume x=y.
     - From EqRefl we get ∀u. u = u. Instantiate with x to get x = x.
     - Use the eqElim axiom in the style of Lemma2: 
       we define an instance that from (x=y) and (x=x) derives (y=x).
  2. Then generalize over y, then over x.
*)

open Proof_assistant.Peano  (* For the 'EqRefl' and 'EqElim' axioms, etc. *)
open Proof_assistant.Logic

module LogicPeano = Make(Peano)
open LogicPeano

(** Construct the proof of Lemma 1 *)
let lemma1 : theorem =
  let x = fresh_var ~base:"x" () in
  let y = fresh_var ~base:"y" () in

  (* eqRefl gives us: ⊢ ∀u. u = u *)
  let eqrefl_ax = axiom EqRefl in
  (* Instantiate eqRefl with x:  ⊢ x = x *)
  let eqrefl_inst_x = forall_e eqrefl_ax (Var x) in

  (* We'll need an instance of EqElim to go from (x=y) & (x=x) => (y=x).
     EqElim is:   ⊢ ∀Y. ∀Z. (Y = Z) ⇒ φ{u → Y} ⇒ φ{u → Z}.
     We choose 'u' fresh, and define φ so that:
         φ{u → x} = (x=x)
         φ{u → y} = (y=x)
     That leads us to φ = (u = x), because then:
       φ{u → x} = (x = x)
       φ{u → y} = (y = x).
  *)
  let u = fresh_var ~base:"u" () in
  let eqelim_phi = Rel("=", [Var u; Var x]) in
  let eqelim_ax = axiom (EqElim(u, eqelim_phi)) in

  (* Now instantiate eqelim_ax with Y = x, Z = y:
       eqelim_ax : ⊢ ∀Y. ∀Z. (Y=Z) => (u=x){u→Y} => (u=x){u→Z}
                   i.e. ∀Y. ∀Z. Y=Z => Y=x => Z=x
     1) eqelim_inst1 = ∀Z. x=Z => x=x => Z=x
     2) eqelim_inst2 = x=y => x=x => y=x
  *)
  let eqelim_inst1 = forall_e eqelim_ax (Var x) in  (* "x=Z => x=x => Z=x" *)
  let eqelim_inst2 = forall_e eqelim_inst1 (Var y) in
  (* eqelim_inst2 : x=y => x=x => y=x *)

  (* We want to prove: x=y => y=x
     Steps:
       - Assume (x=y).
       - From eqelim_inst2 and that assumption, we get: x=x => y=x
       - Then from x=x (eqrefl_inst_x) we get y=x
  *)
  let assume_x_eq_y = by_assumption (Rel("=", [Var x; Var y])) in
  let step1 = imp_e eqelim_inst2 assume_x_eq_y in
  (* step1 : x=x => y=x *)
  let step2 = imp_e step1 eqrefl_inst_x in
  (* step2 : y=x *)

  (* Discharge assumption (x=y) to form implication x=y => y=x *)
  let lemmabody = imp_i (Rel("=", [Var x; Var y])) step2 in

  (* Now quantify over y, then x:  ∀y. (x=y => y=x)  then  ∀x. ∀y. x=y => y=x *)
  let all_y = forall_i y lemmabody in
  let all_x = forall_i x all_y in
  all_x

(** Alcotest test for Lemma 1 *)
open Alcotest

let test_lemma1_conclusion () =
  let concl = conclusion lemma1 in
  (* Expected formula:  ∀x. ∀y. x=y → y=x  *)
  let x_test = fresh_var ~base:"x" () in
  let y_test = fresh_var ~base:"y" () in
  let expected =
    All(x_test,
      All(y_test,
        Imp(Rel("=", [Var x_test; Var y_test]),
            Rel("=", [Var y_test; Var x_test]))
      )
    )
  in
  check bool "Lemma1 conclusion == ∀x.∀y. (x=y → y=x)"
    true (eq_formula concl expected)

let suite = [
  test_case "Lemma1: ∀x.∀y. x = y → y = x" `Quick test_lemma1_conclusion;
]

let () =
  Alcotest.run "Lemma1 Test" [
    "Peano Lemma1", suite
  ]
