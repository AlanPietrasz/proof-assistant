type formula =
| Var of string
| Bot
| Imp of formula * formula

let rec string_of_formula f =
  match f with
  | Bot -> "⊥"
  | Var v -> v
  | Imp(l, r) ->
      let l_str = string_of_formula l in
      let r_str = string_of_formula r in
        (match l with
        | Bot | Var _ -> l_str
        | Imp(_, _) -> "(" ^ l_str ^ ")")
        ^ " → " ^ r_str


let compare_formulas left right = 
  String.equal (string_of_formula left) (string_of_formula right)

type theorem = formula list * formula

let assumptions thm = fst thm 

let consequence thm = snd thm

let pp_print_formula fmtr f =
  Format.pp_print_string fmtr (string_of_formula f)

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
  pp_print_formula fmtr (consequence thm);
  pp_close_box fmtr ();
  pp_close_box fmtr ()

let by_assumption f = ([f], f)

let difference_of_lists xs ys =
  List.filter (fun x -> not (List.mem x ys)) xs

let imp_i f thm = 
  let new_assumptions = difference_of_lists (assumptions thm) [f] in
    (new_assumptions, Imp(f, consequence thm))

let imp_e th1 th2 = 
  match consequence th1 with
  | Imp(phi, psi) -> 
    if phi = consequence th2
      then (difference_of_lists (assumptions th1) (assumptions th2) @ assumptions th2, psi)
      else failwith "Consequence of th2 does not match the antecedent of th1 implication"
  | _ -> failwith "Theorem th1 does not have an implication as its consequence"

let bot_e f thm = 
  match consequence thm with
  | Bot -> (assumptions thm, f)
  | _ -> failwith "The theorem does not conclude with ⊥"

