(*
utop logic.cmo proof.cmo
#use "proof_test.ml";;
*)


open Logic
open Proof


#install_printer Logic.pp_print_formula ;;
#install_printer Logic.pp_print_theorem ;;

let f = Imp(Var("p"), Imp(Imp(Var("p"), Var("q")), Var("q"))) 
;;

proof [] f
    |> intro "H1"
    |> intro "H2"
    |> apply_assm "H2"
    |> apply_assm "H1"
|> qed


let f1 = Imp(
    Imp(Var("p"), Imp(Var("q"), Var("r"))),
    Imp(
        Imp(Var("p"), Var("q")),
        Imp(Var("p"), Var("r"))
    )
)
;;


proof [] f1
    |> intro "H1"
    |> intro "H2"
    |> intro "H3"
    |> apply_assm "H1"
    |> apply_assm "H3"
    |> apply_assm "H2"
    |> apply_assm "H3"
|> qed

let f2 =
  Imp(
    Imp(
      Imp(
        Imp(Var("p"), Bot),
        Var("p")
      ),
      Var("p")
    ),
    Imp(
      Imp(
        Imp(Var("p"), Bot),
        Bot
      ),
      Var("p")
    )
  )
;;

proof [] f2
  |> intro "H1"
  |> intro "H2"
  |> apply_assm "H1"
  |> intro "H3"
  |> apply_assm "H2"
  |> apply_assm "H3"
|> qed

let f3 =
  Imp(
    Imp(
      Imp(
        Imp(Var("p"), Bot),
        Bot
      ),
      Var("p")
    ),
    Imp(
      Imp(
        Imp(Var("p"), Bot),
        Var("p")
      ),
      Var("p")
    )
  )
;;

proof [] f3
  |> intro "H1"
  |> intro "H2"
  |> apply_assm "H1"
  |> intro "H3"
  |> apply_assm "H3"
  |> apply_assm "H2"
  |> apply_assm "H3"
|> qed

