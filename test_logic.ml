(*
utop logic.cmo
#use "test_logic.ml";;
*)

#install_printer Logic.pp_print_formula ;;
#install_printer Logic.pp_print_theorem ;;

open Logic

let f = Imp(Imp(Var("p"), Bot), Imp(Var("p"), Var("q"))) ;;


let p = (Var "p") 
let q = (Var "q")

let a = imp_i p (by_assumption p) (* |- p -> p *)

let b = imp_i p (imp_i q (by_assumption p)) (* |- p -> q -> p *)

let f1 = Imp(p, Imp(q, (Var "r")));; (* p -> q -> r *)
let f2 = Imp(p, q);; (* p -> q *)
let c1 = by_assumption f1;; 
let c2 = by_assumption f2;;
let c3 = by_assumption p;;

 (* *)

let c' =
    imp_e (imp_e c1 c3) (imp_e c2 c3)
    |> imp_i p 
    |> imp_i f2
    |> imp_i f1
    

let d = imp_i Bot (bot_e p (by_assumption Bot))