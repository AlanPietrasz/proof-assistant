(*
utop logic.cmo
#use "test_logic_propositional_calculus.ml";;
*)

#install_printer Logic.pp_print_formula ;;
#install_printer Logic.pp_print_theorem ;;

open Logic

(** Pretty print test *)

let p = Rel("p", [])
let q = Rel("q", [])
let r = Rel("r", [])

let f = Imp(Imp(p, Bot), Imp(p, q))

;; print_string "========================================================================="
(* ⊢ p → p *)
let t1 = imp_i p (by_assumption p) 

;; print_string "========================================================================="
(* ⊢ p → q → p *)
let t2 = imp_i p (imp_i q (by_assumption p))

;; print_string "========================================================================="
let f1 = Imp(p, Imp(q, r));; (* p → q → r *)
let f2 = Imp(p, q);; (* p → q *)
let c1 = by_assumption f1;; 
let c2 = by_assumption f2;;
let c3 = by_assumption p;;

(* ⊢ (p → q → r) → (p → q) → p → r *)
let t3 =
    imp_e (imp_e c1 c3) (imp_e c2 c3)
    |> imp_i p 
    |> imp_i f2
    |> imp_i f1
    

;; print_string "========================================================================="
let t4 = imp_i Bot (bot_e p (by_assumption Bot))