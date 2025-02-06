type var = string

module Var = struct
  type t = var
  let compare = String.compare
end

module VarMap = Map.Make(Var)

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
  | Var y -> x = y
  | Sym(_, ts) -> List.exists (free_in_term x) ts

(** Check if [x] is free in formula [phi]. *)
let rec free_in_formula x phi =
  match phi with
  | Bot -> false
  | Imp(phi, psi) -> 
    free_in_formula x phi ||
    free_in_formula x psi
  | Rel(_, ts) -> List.exists (free_in_term x) ts
  | All(y, phi) -> 
    if x = y then false
    else free_in_formula x phi

let fresh_var () = 
  failwith "Not implemented"

(** Stub of parallel substitution in term. *)
(* val psubst_in_term : term VarMap.t -> term -> term *)
let psubst_in_term map t =
  ignore map;
  ignore t;
  failwith "Not implemented"
  
(** Stub of parallel substitution in formula. *)
(* val psubst_in_formula : term VarMap.t -> formula -> formula *)
let psubst_in_formula map phi =
  ignore map;
  ignore phi;
  failwith "Not implemented"

let subst_in_term x t t' =
  psubst_in_term (VarMap.singleton x t) t'
  
let subst_in_formula x t phi =
  psubst_in_formula (VarMap.singleton x t) phi

let concat_parentheses s = "(" ^ s ^ ")"

let rec string_of_term t =
  match t with
  | Var v -> v
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
      "∀" ^ v ^ "." ^ string_of_formula f

(** This is not working properly for changing names of variables *)
let eq_formula left right = 
  String.equal (string_of_formula left) (string_of_formula right)


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
        else failwith "Conclusion of th2 does not match the antecedent of conclusion of th1 implication"
    | _ -> failwith "Theorem th1 does not have an implication as its conclusion"

  let bot_e f thm = 
    match conclusion thm with
    | Bot -> (assumptions thm, f)
    | _ -> failwith "The theorem does not conclude with ⊥"

  let forall_i x thm =
    ignore x;
    ignore thm;
    failwith "Not implemented (∀I)"

  let forall_e th tm =
    ignore th;
    ignore tm;
    failwith "Not implemented (∀E)"

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
    