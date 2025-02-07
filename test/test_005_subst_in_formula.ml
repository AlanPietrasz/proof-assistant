(* ./test/test_005_subst_in_formula.ml *)

open Alcotest
open Proof_assistant.Logic

module TestSubstFormula = struct
  let x = fresh_var ~base:"x" ()
  let y = fresh_var ~base:"y" ()

  let fx = Sym("f",[Var x])  (* f(x) *)
  let fy = Sym("f",[Var y])  (* f(y) *)

  let p_x = Rel("p",[Var x])
  let p_fy = Rel("p",[fy])

  let bot = Bot
  let allx_px = All(x, p_x)

  let ally_rxy = All(y, Rel("r",[Var x; Var y]))

  let test_simple_imp_subst () =
    (* (x → f(y)){x -> f(x)} => (f(x) → f(y)) *)
    let substituted = subst_in_formula x fx (Imp(p_x, p_fy)) in
    let expected_str = string_of_formula (Imp(Rel("p",[fx]), p_fy)) in
    check string "Imp(p(x),p(f(y))){x->f(x)} => Imp(p(f(x)),p(f(y)))"
      expected_str (string_of_formula substituted)

  let test_bot_subst () =
    (* ⊥ remains ⊥ under substitution *)
    let substituted = subst_in_formula x fx bot in
    let expected_str = "⊥" in
    check string "Bot{x->f(x)} => Bot" expected_str (string_of_formula substituted)

  let test_all_collision_subst () =
    (* All(x, p(x)){x -> f(y)} is a collision scenario:
       naive approach might produce All(x, p(f(y))) which incorrectly
       captures 'y' if we ever rename 'x' -> 'y' internally, or if 'y' = 'x'.
       Eventually, we want alpha-renaming so that x is replaced only if free. *)
    let substituted = subst_in_formula x fy allx_px in
    let substituted_str = string_of_formula substituted in
    (* With naive substitution, you might get "∀x.p(f(y))". 
       With alpha-correct substitution, you might also get "∀x.p(x)"
       if x is not free. Actually in this example, x is bound, so 
       it might remain "∀x.p(x)" because x is never free. 
       Test whichever behavior you want to enforce. 
       We'll expect the formula *not* to change, because x is bound. *)
    check bool "All(x,p(x)) unchanged if x is bound" true
      (eq_formula substituted allx_px);

    check string "String representation might remain ∀x.p(x)" 
      (string_of_formula allx_px) substituted_str

  let test_all_collision_subst_2 () =
    let substituted = subst_in_formula x fy ally_rxy in
    let substituted_str = string_of_formula substituted in

    check bool "" false
      (eq_formula substituted ally_rxy);

    check string "" 
      "∀y3.r(f(y), y3)" substituted_str
end

let suite = [
  test_case "subst_in_formula simple imp"   `Quick TestSubstFormula.test_simple_imp_subst;
  test_case "subst_in_formula bot"          `Quick TestSubstFormula.test_bot_subst;
  test_case "subst_in_formula collision"    `Quick TestSubstFormula.test_all_collision_subst;
  test_case "subst_in_formula collision 2"  `Quick TestSubstFormula.test_all_collision_subst_2;
]

let () =
  Alcotest.run "Subst In Formula Tests" [
    "subst_in_formula", suite
  ]
