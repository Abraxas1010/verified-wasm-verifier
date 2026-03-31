import HeytingLean.LoF.Combinators.BracketAbstraction
import HeytingLean.LoF.Combinators.SKYExec

/-!
# PartialEval — specialization utilities over the SKY compilation layer

This file provides small, composable helpers that treat partial evaluation as:

1. substitute a static environment into a syntax-with-variables (`Bracket.CExp Var`),
2. optionally close the result (if all variables are discharged),
3. run the existing SKY reducer (`SKYExec.reduceFuel`) to obtain a residual normal form.

The goal is *not* to build a full self-applicable `mix` here, but to expose a concrete,
executable specialization primitive that can be reused by later Futamura-style tooling.
-/

namespace HeytingLean
namespace LoF
namespace Combinators

namespace Bracket
namespace CExp

variable {Var : Type}

/-- Embed a closed SKY term into a `CExp Var` (no variables introduced). -/
def ofComb : Comb → CExp Var
  | .K => .K
  | .S => .S
  | .Y => .Y
  | .app f a => .app (ofComb f) (ofComb a)

/-- Specialize a `CExp Var` by substituting some variables with closed SKY terms. -/
def substComb [DecidableEq Var] (static : Var → Option Comb) : CExp Var → CExp Var
  | .var v =>
      match static v with
      | some c => ofComb c
      | none => .var v
  | .K => .K
  | .S => .S
  | .Y => .Y
  | .app f a => .app (substComb static f) (substComb static a)

/-- Merge a partial static environment with a total dynamic environment. -/
def mergeEnv (static : Var → Option Comb) (dynamic : Var → Comb) : Var → Comb :=
  fun v => match static v with
    | some c => c
    | none => dynamic v

@[simp] theorem denote_ofComb (env : Var → Comb) (t : Comb) :
    denote env (ofComb (Var := Var) t) = t := by
  induction t with
  | K => rfl
  | S => rfl
  | Y => rfl
  | app f a ihF ihA =>
      simp [ofComb, denote, ihF, ihA]

theorem denote_substComb [DecidableEq Var]
    (static : Var → Option Comb) (dynamic : Var → Comb) (e : CExp Var) :
    denote dynamic (substComb (Var := Var) static e) = denote (mergeEnv static dynamic) e := by
  induction e with
  | var v =>
      cases h : static v with
      | none =>
          simp [substComb, mergeEnv, denote, h]
      | some c =>
          simp [substComb, mergeEnv, denote, h, denote_ofComb (Var := Var) (env := dynamic) (t := c)]
  | K => rfl
  | S => rfl
  | Y => rfl
  | app f a ihF ihA =>
      simp [substComb, denote, ihF, ihA]

/-- A small structural size metric (useful as a specialization signature feature). -/
def size : CExp Var → Nat
  | .var _ => 1
  | .K => 1
  | .S => 1
  | .Y => 1
  | .app f a => size f + size a + 1

end CExp

namespace PartialEval

open Bracket

variable {Var : Type} [DecidableEq Var]

/-- Specialize and, if the result is closed, run the SKY reducer for `fuel` steps. -/
def specializeReduceFuel? (fuel : Nat) (static : Var → Option Comb) (e : Bracket.CExp Var) :
    Option Comb :=
  match (Bracket.CExp.substComb (Var := Var) static e).erase? with
  | none => none
  | some closed => some (SKYExec.reduceFuel fuel closed)

end PartialEval

end Bracket
end Combinators
end LoF
end HeytingLean
