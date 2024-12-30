# Functional Programming Final Project

This is a project written in **OCaml** for my Functional Programming class. Currently, it includes the implementation of a **Logic Module**, and more functionality will be added in the future.

## Logic Module
The Logic Module provides tools for representing and reasoning about logical formulas and theorems. It supports:

- **Representation of Formulas**
- **Representation of Theorems**
- **Operations for Deduction Rules**

### Representation of Formulas
The module defines formulas using the following type:

```ocaml
type formula =
| Var of string             (* A variable, represented by a string *)
| Bot                       (* Bottom (falsehood) *)
| Imp of formula * formula  (* Implication between two formulas *)
```

#### Pretty-printing formulas
You can pretty-print formulas using:

```ocaml
val pp_print_formula : Format.formatter -> formula -> unit
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
Derives an implication $ f \to \phi $ by removing $f$ from the assumptions:

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

## Future Plans
This is just the first module of the project. Future updates will include:

- Advanced theorem proving techniques
- Integration of additional logical constructs
- Comprehensive test cases and documentation

Feel free to explore, contribute, or provide feedback!
