(* logic.ml *)

(** Unique ID for variables so that we never clash after "fresh" generation. *)
let global_var_counter = ref 0

(** Representation of a first-order variable. 
    - [id] is a unique integer (for internal use). 
    - [base_name] is the name the user might have given, or e.g. "x" for fresh ones. 

    Two varibles can have the same [base_name] but different [id]s.
    I maintain the following invariant throughout the program:
    - If variable with [base_name = "x"] is bound in a quantifier, then all free
      occurences of variables with [base_name = "x"] in the body of this quantifier 
      are the same variable (i.e. have the same [id]).
*)
type var = {
  id        : int;
  base_name : string;
}


let eq_var v1 v2 = v1.id = v2.id


(** For paralell substitution *)
module VarMap = Map.Make(struct
  type t = var
  let compare v1 v2 = compare v1.id v2.id (* v1.base_name v2.base_name *)
end)

(** For set of variables *)
module VarSet = Set.Make(struct
  type t = var
  let compare v1 v2 = compare v1.id v2.id
end)

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

let fresh_var ?(base="x") () =
  let n = !global_var_counter in
  incr global_var_counter;
  { id = n; base_name = base }

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
  
(** In order to avoid capturing variables, we may need to rename bound variables. 
    The logic here follows the standard 3-case approach:
    1) If the bound variable is in [smap]'s domain, do nothing (no substitution).
    2) If the bound variable is *not* in the domain but *does not* occur free
       in any substituted term, we just recurse.
    3) If it *does* occur free in some substituted term, we rename it to a fresh var. *)
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
          if VarSet.mem y all_subst_vars then
            (* We rename y -> y_something. Then apply smap to the renamed body. *)
            let y' = fresh_var ~base:(y.base_name^string_of_int !global_var_counter) () in
            let rename_map = VarMap.singleton y (Var y') in
            let body_renamed = psubst_in_formula rename_map body in
            All(y', go body_renamed)
          else
            (* case 2: y is not in smap's domain and also not free in sub. Just recurse. *)
            All(y, go body)
  in
  go phi

let subst_in_term x t t' =
  psubst_in_term (VarMap.singleton x t) t'
  
let subst_in_formula x t phi =
  psubst_in_formula (VarMap.singleton x t) phi

let concat_parentheses s = "(" ^ s ^ ")"

let string_of_var v =
  v.base_name
let rec string_of_term t =
  match t with
  | Var v -> string_of_var v
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

(** alpha_eq_term: structural equality of terms (no binding in terms) *)
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

let pp_print_formula fmtr f =
  Format.pp_print_string fmtr (string_of_formula f)


module Make (T : Theory) = struct

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
    