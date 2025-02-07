(* logic.ml *)

(** A global counter to generate fresh variable IDs. *)
let global_var_counter = ref 0

(** Representation of a first-order variable. 
    - [id] is a unique integer (for internal use). 
    - [base_name] is the name the user might have given, or e.g. "x" for fresh ones. 

    Two varibles can have the same [base_name] but different [id]s:
    For example, "x" in one scope is not the same as "x" in another scope if they
    were generated separately.

    I maintain the following invariant throughout the program:
    - If variable with [base_name = "x"] is bound in a quantifier, then all free
      occurences of variables with [base_name = "x"] in the body of this quantifier 
      are the same variable (i.e. have the same [id]).
*)
type var = {
  id        : int;
  base_name : string;
}

let fresh_var ?(base="x") () =
  let n = !global_var_counter in
  incr global_var_counter;
  { id = n; base_name = base }

let eq_var v1 v2 = (v1.id = v2.id)

type sym = string

type term =
| Var of var
| Sym of sym * term list

type formula =
| Bot
| Imp of formula * formula
| Rel of sym * term list
| All of var * formula

module type Theory = sig
  type axiom
  val axiom : axiom -> formula
end

(* -------------------------------------------------------------------------- *)
(*                 1. Free-variable checks                                    *)
(* -------------------------------------------------------------------------- *)


(** Check if [x] is free in term [t]. *)
let rec free_in_term x t =
  match t with
  | Var y -> eq_var x y (* or eq_var_name ? *)
  | Sym(_, ts) -> List.exists (free_in_term x) ts

(** Check if [x] is free in formula [phi]. *)
let rec free_in_formula x phi =
  match phi with
  | Bot -> false
  | Imp(phi, psi) -> 
      free_in_formula x phi ||
      free_in_formula x psi
  | Rel(_, ts) -> 
      List.exists (free_in_term x) ts
  | All(y, phi) -> 
      if eq_var x y then false (* or eq_var_name ? *)
      else free_in_formula x phi



(* -------------------------------------------------------------------------- *)
(*       2. Substitution with capture avoidance (parallel version)            *)
(* -------------------------------------------------------------------------- *)


(** For set of variables *)
module VarSet = Set.Make(struct
  type t = var
  let compare v1 v2 = compare v1.id v2.id
end)


(** Utilities to collect all free variables in a term/formula (used for renaming). *)
let rec fv_term t : VarSet.t =
  match t with
  | Var x -> VarSet.singleton x
  | Sym(_, ts) ->
      List.fold_left
        (fun acc t' -> VarSet.union acc (fv_term t'))
        VarSet.empty
        ts

let rec fv_formula phi =
  match phi with
  | Bot -> VarSet.empty
  | Rel(_, ts) ->
      List.fold_left
        (fun acc t' -> VarSet.union acc (fv_term t'))
        VarSet.empty
        ts
  | Imp(phi, psi) ->
      VarSet.union (fv_formula phi) (fv_formula psi)
  | All(x, phi) ->
      VarSet.remove x (fv_formula phi) (* using invariant *)

(** For paralell substitution *)
module VarMap = Map.Make(struct
  type t = var
  let compare v1 v2 = compare v1.base_name v2.base_name (* v1.base_name v2.base_name *)
end)

(** [psubst_in_term map t] replaces each variable in [map] with its image, 
    *in parallel*, in the term [t]. *)
let rec psubst_in_term smap t =
  match t with
  | Var x ->
      begin match VarMap.find_opt x smap with
      | Some t -> t
      | None -> t
      end
  | Sym(f, ts) ->
      Sym(f, List.map (psubst_in_term smap) ts)


module StringSet = Set.Make(String)

(** Helper that picks a fresh var name base that does not clash
    with a set of used base names. *)
let pick_fresh_base (base : string) (used : StringSet.t) : var =
  let rec loop attempt i =
    let candidate =
      if i = 0 then attempt
      else if i = 1 then Printf.sprintf "%s'" attempt
      else if i = 2 then Printf.sprintf "%s''" attempt
      else Printf.sprintf "%s_%d" attempt (i-2)
    in
    if StringSet.mem candidate used then
      loop attempt (i + 1)
    else
      let v = { id = !global_var_counter; base_name = candidate } in
      incr global_var_counter;
      v
  in
  loop base 0

(** [psubst_in_formula smap phi] performs parallel substitution on [phi],
    avoiding variable capture by alpha-renaming bound variables when necessary. *)
let rec psubst_in_formula smap phi =
  let rec go phi =
    match phi with
    | Bot -> Bot
    | Rel(r, ts) ->
        Rel(r, List.map (psubst_in_term smap) ts)
    | Imp(p, q) ->
        Imp(go p, go q)
    | All(y, body) ->
        if VarMap.mem y smap then
          (* The bound var y is in the domain -> skip substitution for it. *)
          let smap' = VarMap.remove y smap in
          All(y, psubst_in_formula smap' body)
        else
          (* We must check if y is free in any term used in smap. 
              If yes, rename y to avoid capturing. *)
          let all_subst_vars =
            VarMap.fold 
              (fun _v t acc -> VarSet.union acc (fv_term t)) 
              smap 
              VarSet.empty
          in
          let free_vars_body = fv_formula body in
          let all_vars_to_avoid = VarSet.union all_subst_vars free_vars_body in

          if VarSet.mem y all_subst_vars then
            (* rename y to avoid capture *)
            rename_and_go y body all_vars_to_avoid
          else
            All(y, go body)

  and rename_and_go (y : var) (body : formula) (vars_to_avoid : VarSet.t) =
    let used_base_names =
      VarSet.fold (fun v acc -> StringSet.add v.base_name acc)
                  vars_to_avoid
                  StringSet.empty
    in

    let y' = pick_fresh_base y.base_name used_base_names in
    (* rename y in body, then proceed *)
    let rename_map = VarMap.singleton y (Var y') in
    let body_renamed = psubst_in_formula rename_map body in
    All(y', go body_renamed)


  in
  go phi

let subst_in_term x t t' =
  psubst_in_term (VarMap.singleton x t) t'
  
let subst_in_formula x t phi =
  psubst_in_formula (VarMap.singleton x t) phi

(* -------------------------------------------------------------------------- *)
(*        3. String/printing support, with infix printing for = and +         *)
(* -------------------------------------------------------------------------- *)

let concat_parentheses s = 
  "(" ^ s ^ ")"

let string_of_var v =
  v.base_name


(** We will treat certain function symbols as infix if they have exactly two sub-terms. *)
let is_infix_fun s =
  match s with
  | "+" | "-" -> true
  | _   -> false
    
(** We will treat certain relation symbols as infix if they have exactly two sub-terms. *)
let is_infix_rel s =
  match s with
  | "=" -> true
  | _   -> false


(** Convert a term to its string representation, using infix notation for
    e.g. [a + b] if [s = "+"]. *)
let rec string_of_term t =
  match t with
  | Var v -> 
      string_of_var v
  | Sym(s, [t1; t2]) when is_infix_fun s ->
      (* (t1 + t2) with parentheses to be unambiguous in bigger expressions. *)
      let left_str  = string_of_term t1 in
      let right_str = string_of_term t2 in
      "(" ^ left_str ^ " " ^ s ^ " " ^ right_str ^ ")"
  | Sym(s, ts) ->
      s ^
      if ts = [] then ""
      else
        List.map string_of_term ts |>
        String.concat ", " |>
        concat_parentheses

let rec string_of_formula f =
  match f with
  | Bot -> "⊥"
  | Rel(r, [t1; t2]) when is_infix_rel r ->
      let left_str  = string_of_term t1 in
      let right_str = string_of_term t2 in
      "(" ^ left_str ^ " " ^ r ^ " " ^ right_str ^ ")"
  | Rel(r, ts) -> 
      r ^
      if ts = [] then ""
      else
        List.map string_of_term ts |>
        String.concat ", " |>
        concat_parentheses
  (* | Var v -> v *)
  | Imp(l, r) ->
      let l_str = string_of_formula l in
      let r_str = string_of_formula r in
        (match l with
        | Imp(_, _) | All(_, _) -> concat_parentheses l_str
        | _ -> l_str) ^ 
        " → " ^ 
        r_str
  | All(v, f) ->
      "∀" ^ string_of_var v ^ "." ^ string_of_formula f

let pp_print_formula fmtr f =
  Format.pp_print_string fmtr (string_of_formula f)

(* -------------------------------------------------------------------------- *)
(*    4. Equality of formulas (alpha-equivalence)                             *)
(* -------------------------------------------------------------------------- *)

      
(** [alpha_eq_term] does structural equality on terms. We do compare IDs to ensure distinct
    variables are not considered equal. *)
let rec alpha_eq_term (t1 : term) (t2 : term) : bool =
  match t1, t2 with
  | Var x, Var y -> x.id = y.id
  | Sym(f1, ts1), Sym(f2, ts2) ->
      f1 = f2 &&
      List.length ts1 = List.length ts2 &&
      List.for_all2 alpha_eq_term ts1 ts2
  | _, _ -> false

(** [alpha_eq_formula φ ψ] checks if φ, ψ are alpha-equivalent. *)
let rec alpha_eq_formula (phi : formula) (psi : formula) : bool =
  match phi, psi with
  | Bot, Bot -> true
  | Rel(r1, ts1), Rel(r2, ts2) ->
      r1 = r2
      && List.length ts1 = List.length ts2
      && List.for_all2 alpha_eq_term ts1 ts2

  | Imp(a1, b1), Imp(a2, b2) ->
      alpha_eq_formula a1 a2 && alpha_eq_formula b1 b2

  | All(x, phi), All(y, psi) ->
      let z = fresh_var ~base:x.base_name () in
      let phi' = subst_in_formula x (Var z) phi in
      let psi' = subst_in_formula y (Var z) psi in
      alpha_eq_formula phi' psi'

  | _, _ -> false

let eq_formula (phi : formula) (psi : formula) : bool =
  alpha_eq_formula phi psi


module Make (T : Theory) = struct

  (** We represent a theorem as a pair ([Γ], φ) meaning "from assumptions Γ
      we derive φ". *)
  type theorem = formula list * formula


  let assumptions thm = fst thm 
  let conclusion thm = snd thm

  let eq_theorem th1 th2 =
    (* TODO: add checking equality of sets of assumptions but for now we
      will check if they are empty  *)
    eq_formula (conclusion th1) (conclusion th2) &&
    (assumptions th1 = [] && assumptions th2 = [])


  let pp_print_theorem fmtr thm =
    let open Format in
    pp_open_hvbox fmtr 2;
    begin match assumptions thm with
    | [] -> ()
    | f :: fs ->
      pp_print_formula fmtr f;
      fs |> List.iter (fun f ->
        pp_print_string fmtr ",";
        pp_print_space fmtr ();
        pp_print_formula fmtr f);
      pp_print_space fmtr ()
    end;
    pp_open_hbox fmtr ();
    pp_print_string fmtr "⊢";
    pp_print_space fmtr ();
    pp_print_formula fmtr (conclusion thm);
    pp_close_box fmtr ();
    pp_close_box fmtr ()

  let difference_of_lists xs ys =
    List.filter (fun x -> not (List.mem x ys)) xs
  
  let by_assumption f = ([f], f)

  let imp_i f thm = 
    let gamma = assumptions thm in
    let phi = conclusion thm in
    let new_assumptions = difference_of_lists gamma [f] in
    (new_assumptions, Imp(f, phi))

  let imp_e th1 th2 = 
    match conclusion th1 with
    | Imp(phi, psi) -> 
      if eq_formula phi (conclusion th2)
        then (difference_of_lists (assumptions th1) (assumptions th2) @ assumptions th2, psi)
        else 
          failwith (Printf.sprintf
            "imp_e: mismatch:\n  antecedent of conclusion of th1 = %s\n  conclusion of th2 = %s\n(They are not alpha-equal!)"
            (string_of_formula phi)
            (string_of_formula (conclusion th2)))
    | _ ->
        failwith (Printf.sprintf
          "imp_e: Theorem th1 does not conclude an implication. Conclusion is: %s"
          (string_of_formula (conclusion th1)))

  let bot_e f thm = 
    match conclusion thm with
    | Bot -> (assumptions thm, f)
    | _ ->
        failwith (Printf.sprintf
          "bot_e: The theorem does not conclude with ⊥. Conclusion is: %s"
          (string_of_formula (conclusion thm)))

  let forall_i x (gamma, phi) =
    (* 1. gather all free variables in phi with the desired base_name. *)
    let x_name = x.base_name in
    let fv_phi = fv_formula phi in
    let candidates =
      VarSet.filter (fun v -> v.base_name = x_name) fv_phi
    in
    (* if VarSet.is_empty candidates then
      failwith (Printf.sprintf
        "forall_i: No free var with base_name = \"%s\" in conclusion %s."
        x_name (string_of_formula phi)); *)
    if VarSet.cardinal candidates > 1 then
      failwith (Printf.sprintf
        "forall_i: Multiple free vars with base_name = \"%s\" in conclusion %s."
        x_name (string_of_formula phi));

    (* 2. Check x is not free in any formula of Γ. *)
    let is_free_in_gamma =
      List.exists (fun fml -> free_in_formula x fml) gamma
    in
    if is_free_in_gamma then
      failwith (Printf.sprintf
        "forall_i: variable \"%s\" is free in assumptions, so we cannot abstract it.\nAssumptions:\n  %s"
        x_name
        (String.concat "\n  " (List.map string_of_formula gamma)));

    (* 3. Return a new theorem: Γ ⊢ ∀v. phi *)
    (gamma, All(x, phi))
  
  let forall_e thm t =
    match conclusion thm with
    | All(x, body) ->
        (assumptions thm, subst_in_formula x t body)
    | _ ->
      failwith (Printf.sprintf
        "forall_e: conclusion is not a universal formula. It is: %s"
        (string_of_formula (conclusion thm)))

  let axiom (ax : T.axiom) : theorem =
    let f = T.axiom ax in
    ([], f)


  let and_i th1 th2 = 
    ignore th1;
    ignore th2;
    failwith "Not implemented (∧I)"
  let and_e1 th = 
    ignore th;
    failwith "Not implemented (∧E1)"
  let and_e2 th = 
    ignore th;
    failwith "Not implemented (∧E2)"

  let top_i () = failwith "Not implemented (⊤I)"

  let or_i1 th f = 
    ignore th;
    ignore f;
    failwith "Not implemented (∨I1)"
  let or_i2 th f = 
    ignore th;
    ignore f;
    failwith "Not implemented (∨I2)"
  let or_e th th1 th2 = 
    ignore th;
    ignore th1;
    ignore th2;
    failwith "Not implemented (∨E)"

  let exists_i th x t = 
    ignore th;
    ignore x;
    ignore t;
    failwith "Not implemented (∃I)"
  let exists_e th x th2 = 
    ignore th;
    ignore x;
    ignore th2;
    failwith "Not implemented (∃E)"

  let eq_elim th1 th2 = 
    ignore th1;
    ignore th2;
    failwith "Not implemented (EqElim)"

end
    