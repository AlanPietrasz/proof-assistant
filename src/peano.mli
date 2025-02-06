(* peano.mli *)

open Logic

(** Peano: moduł implementujący [Logic.Theory],
    ale w interfejsie chcemy ujawnić konstruktory typu [axiom]. *)

module Peano : sig
  type axiom =
    | EqRefl
    | EqElim of var * formula
    | PlusZ
    | PlusS
    | Induction of var * formula

  (**
     Teraz włączasz do tego modułu „całą resztę” z [Logic.Theory],
     zastępując [type axiom] w [Logic.Theory] przez *ten* [axiom].
  *)
  include Logic.Theory with type axiom := axiom
end