# Proof Assistant

This project is written in **OCaml** as part of a Functional Programming course. It serves as a **Proof Assistant**, supporting logical reasoning and theorem proving in **first-order** logic. The project is modular, allowing for different theories to be implemented and used in conjunction with the core **Logic Module**.

## Features
- **Representation of Formulas**
- **Representation of Theorems**
- **Operations for Deduction Rules**
- **Extensible Theory Framework**
- **Unit Tests with Alcotest**
- **Interactive Testing with UTop**

## Logic Module
The Logic Module provides tools for representing and reasoning about first-order logic formulas and theorems. It supports:


### Representation of Terms and Formulas
Terms and formulas are defined as follows:

```ocaml
type term =
  | Var of string
  | Sym of string * term list

type formula =
| Bot                       (* Bottom (falsehood) *)
| Imp of formula * formula  (* Implication between two formulas *)
| Rel of sym * term list    (* Relation symbol r(t1,...,tn) *)
| All of var * formula      (* Universal quantifier (∀x. φ) *)
```

### Logical Deduction Rules
The following deduction rules are implemented:

#### 1. **By Assumption**
Constructs a theorem where the formula is both the assumption and the consequence:

```ocaml
val by_assumption : formula -> theorem
```
Example:
```
-------(Ax)
{f} ⊢ f
```

#### 2. **Implication Introduction (→I)**
Derives an implication $f \to \phi$ by removing $f$ from the assumptions:

```ocaml
val imp_i : formula -> theorem -> theorem
```
Example:
```
       thm
      Γ ⊢ φ
---------------(→I)
Γ \ {f} ⊢ f → φ
```

#### 3. **Implication Elimination (→E)**
Applies modus ponens to derive $\psi$ from $\phi \to \psi$ and $\phi$:

```ocaml
val imp_e : theorem -> theorem -> theorem
```
Example:
```
thm1      thm2
Γ ⊢ φ → ψ    Δ ⊢ φ
------------------(→E)
Γ ∪ Δ ⊢ ψ
```

#### 4. **Bottom Elimination (⊥E)**
Derives any formula $f$ from a contradiction:

```ocaml
val bot_e : formula -> theorem -> theorem
```
Example:
```
   thm
  Γ ⊢ ⊥
  -----(⊥E)
  Γ ⊢ f
```

---

## Peano Arithmetic as an Example Theory
The **Logic Module** is parameterized by a **Theory Module**, allowing different axiomatic systems to be defined. **Peano Arithmetic** is implemented as an example of such a theory.

### Representation of Peano Arithmetic Axioms
The Peano Axioms are defined as follows:

```ocaml
type axiom =
  | EqRefl                      (* ∀x. x = x *)
  | EqElim of var * formula     (* ∀y.∀z. y = z ⇒ φ{x → y} ⇒ φ{x → z} *)
  | PlusZ                       (* ∀n. 0 + n = n *)
  | PlusS                       (* ∀n.∀m. S(n) + m = S(n + m) *)
  | Induction of var * formula  (* Induction principle *)
```

These axioms allow for the proof of fundamental properties such as:

1. **Identity of Addition**: \( \forall n. n + 0 = n \)
2. **Successor Property**: \( \forall n. \forall m. n + S(m) = S(n + m) \)
3. **Commutativity of Addition**: \( \forall n. \forall m. n + m = m + n \)

Each of these can be formally proven using the inference rules of the **Logic Module**.

---

## Unit Testing
The project includes a suite of **unit tests** using **Alcotest**.

### Running Tests
To run all unit tests, use:
```sh
dune test
```

## Running Interactive Tests in UTop
To interactively explore the **Proof Assistant**, you can use **UTop**:

```sh
dune utop src
```
<!-- Then, inside UTop, load the test script:

```ocaml
#use "test/test_pp_utop.ml";;
``` -->

Then, in UTop:
```ocaml
open Proof_assistant.Logic;;
#install_printer pp_print_formula ;;

open Proof_assistant.Peano;;
module LogicPeano = Make(Peano);;

open LogicPeano;;
#install_printer pp_print_theorem ;;
```

This will install pretty-printing functions and allow you to construct and test proofs interactively.



## Future Plans
This project is an initial implementation of a **Proof Assistant** and will be expanded with:
- **Additional logical constructs** such as conjunction, disjunction, and existential quantification.
- **More advanced theorem proving techniques**.
- **Support for classical logic** by extending the axiom system.
- **User-friendly proof scripting** for easier interaction.

















