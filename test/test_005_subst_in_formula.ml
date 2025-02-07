(* ./test/test_005_subst_in_formula.ml *)

open Alcotest
open Proof_assistant.Logic

module TestSubstFormula = struct
  (* We reuse x,y from your existing tests. Let's add a few more for clarity. *)
  let x = fresh_var ~base:"x" ()
  let y = fresh_var ~base:"y" ()
  let z = fresh_var ~base:"z" ()
  let w = fresh_var ~base:"w" ()

  (* Some short-hands for building terms and formulas *)
  let varX = Var x
  let varY = Var y
  let varZ = Var z
  let varW = Var w

  let fx = Sym("f",[Var x])       (* f(x) *)
  let fy = Sym("f",[Var y])       (* f(y) *)
  let fz = Sym("f",[Var z])       (* f(z) *)
  let fw = Sym("f",[Var w])       (* f(w) *)

  let p_x  = Rel("p",[varX])
  let p_fy = Rel("p",[fy])

  let bot = Bot
  let allx_px = All(x, p_x)
  let ally_rxy = All(y, Rel("r",[varX; varY]))

  (* ----------------------------------------------------------------- *)
  (* Reuse your original existing tests                                 *)
  (* ----------------------------------------------------------------- *)
  let test_simple_imp_subst () =
    (* (p(x) → p(f(y))){x -> f(x)} => (p(f(x)) → p(f(y))) *)
    let orig = Imp(p_x, p_fy) in
    let substituted = subst_in_formula x fx orig in
    let expected = Imp(Rel("p",[fx]), p_fy) in
    check string
      "Imp(p(x), p(f(y))) with x->f(x) => Imp(p(f(x)), p(f(y)))"
      (string_of_formula expected)
      (string_of_formula substituted)

  let test_bot_subst () =
    (* ⊥ remains ⊥ under substitution *)
    let substituted = subst_in_formula x fx bot in
    check string "Bot{x->f(x)} => Bot"
      "⊥"
      (string_of_formula substituted)

  let test_all_collision_subst () =
    (* All(x, p(x)){x -> f(y)} : x is bound -> should remain All(x,p(x)) 
       Because x inside All(x,...) is not free. *)
    let substituted = subst_in_formula x fy allx_px in
    check bool "All(x,p(x)) unchanged if x is bound" true
      (eq_formula substituted allx_px);

    check string "String representation might remain ∀x.p(x)" 
      (string_of_formula allx_px)
      (string_of_formula substituted)

  let test_all_collision_subst_2 () =
    (* For the formula: All(y, r(x,y))   do x -> f(y)
       - y is a bound var, but y also appears in f(y) => we must rename 
         that bound y to something else, e.g. y'.
       The result should be: ∀y'.r(f(y),y') 
    *)
    let substituted = subst_in_formula x fy ally_rxy in
    let substituted_str = string_of_formula substituted in

    (* We expect the result to not equal the original formula, 
       because we've replaced x with f(y) and forced a rename of the bound y. *)
    check bool
      "Should differ from the original ally_rxy"
      false
      (eq_formula substituted ally_rxy);

    check string
      "Expect ∀y'.r(f(y),y')"
      "∀y'.r(f(y), y')"
      substituted_str

  (* ----------------------------------------------------------------- *)
  (* Additional Thorough Tests                                         *)
  (* ----------------------------------------------------------------- *)

  let test_no_free_occurrences () =
    (* Suppose the formula doesn't contain x at all. e.g. Rel("q",[varY,varZ]). 
       Substitution x-> f(y) should leave it unchanged. *)
    let formula_no_x = Rel("q",[varY; varZ]) in
    let result = subst_in_formula x fy formula_no_x in
    check bool
      "No occurrences of x => formula unchanged"
      true
      (eq_formula formula_no_x result)

  let test_substitute_bound_var () =
    (* If x is bound in All(x, p(x)), then substituting x-> f(z) 
       does nothing because x is NOT free. We tested something similar, 
       but let's do a different shape. *)
    let f = All(x, Imp(Rel("p",[varX]), Rel("q",[varX]))) in
    let result = subst_in_formula x fz f in
    check bool
      "All(x, p(x)->q(x)) remains the same under x->f(z)"
      true
      (eq_formula f result)

  let test_rename_avoid_capture () =
    (* We want a scenario: All(y, Rel("=", [varX; varY])) 
       and we do x-> varY. That means if we didn't rename y, 
       we'd get All(y, Rel("=", [varY; varY])) which is a capturing 
       of the free y in x->y. The correct approach is to rename the bound y. 
       So we expect ∀y'.(=(y,y')) or string "∀y'.=(y, y')"
    *)
    let f = All(y, Rel("=", [varX; varY])) in
    let substituted = subst_in_formula x varY f in
    let s_str = string_of_formula substituted in
    (* The bound 'y' must be changed to something else, e.g. "y'" or "y_1". 
       So the final formula is something like:  ∀y'.=(y,y'). *)
    check bool
      "Original formula should differ from renamed version"
      false
      (eq_formula f substituted);

    (* We'll do a substring check: see if the result contains "=(y, y')" 
       or something similar. The exact name depends on your rename logic, 
       but let's just ensure "y'." appears. *)
    let expected_prefix = "∀y'." in
    let has_prefix = Astring.String.is_prefix ~affix:expected_prefix s_str in
    check bool
      "Should rename bound y => '∀y'.=' prefix in string form"
      true
      has_prefix

  let test_nested_quantifiers () =
    (* A deeper formula: ∀y.∀z. p(x,y,z). We substitute x-> f(z).
       - We see if the second quantifier (z) must get renamed, 
         because the substitution references z. 
       - The first quantifier is y, also distinct from x. 
    *)
    let p_xyz = Rel("p",[varX; varY; varZ]) in
    let f_nested = All(y, All(z, p_xyz)) in
    let result = subst_in_formula x fz f_nested in
    let r_str = string_of_formula result in
    (* Because we do x->f(z), the 'z' in the outer formula is a bound var, 
       but it also appears in the substituting term f(z). That triggers rename 
       of the second quantifier's bound var. 
       So we might end with ∀y.∀z'.p(f(z), y, z') or something similar. *)
    check bool
      "Original formula should differ from substituted version"
      false
      (eq_formula f_nested result);

    check string
      "Check plausible final form, e.g. '∀y.∀z'.p(f(z),y,z')'"
      "∀y.∀z'.p(f(z), y, z')"
      r_str

end

(* ---------------------------------------------------------------------- *)
(* Finally, register them all in the Alcotest suite                       *)
(* ---------------------------------------------------------------------- *)

let suite = [
  (* Existing base tests *)
  test_case "subst_in_formula: simple imp"    `Quick TestSubstFormula.test_simple_imp_subst;
  test_case "subst_in_formula: bot"           `Quick TestSubstFormula.test_bot_subst;
  test_case "subst_in_formula: collision 1"   `Quick TestSubstFormula.test_all_collision_subst;
  test_case "subst_in_formula: collision 2"   `Quick TestSubstFormula.test_all_collision_subst_2;

  (* Extra thorough tests *)
  test_case "no free occurrences of x"        `Quick TestSubstFormula.test_no_free_occurrences;
  test_case "substitute bound var => no-op"   `Quick TestSubstFormula.test_substitute_bound_var;
  test_case "rename avoid capture"            `Quick TestSubstFormula.test_rename_avoid_capture;
  test_case "nested quantifiers rename"       `Quick TestSubstFormula.test_nested_quantifiers;
]

let () =
  Alcotest.run "Subst In Formula Tests" [
    "subst_in_formula", suite
  ]
