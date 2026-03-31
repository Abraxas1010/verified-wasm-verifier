import HeytingLean.LoF.Correspondence.LoFPrimarySKYBoolNary
import HeytingLean.LoF.MRSystems.MooreTerminal

/-!
# (M,R) → SKY simulation for Boolean dynamics (Phase E.2, bounded)

This module provides an explicit, **Lean-checked** simulation bridge from a Boolean
transition system

`R : Bool → Bool → Bool`

to SKY term rewriting:

* we compile `R` into a SKY term `toSKYFun2 R : Comb` expecting two Church booleans;
* applying it to encoded booleans reduces to the encoded output;
* iterating the compiled step along a finite input word reduces to the encoded
  state reached by the corresponding fold.

Objectivity boundary:
* This is a **Bool-level** (finite) bridge. It does not claim a general encoding of arbitrary
  `Type`-valued (M,R) dynamics into SKY.
-/

namespace HeytingLean
namespace LoF
namespace MRSystems

open HeytingLean.LoF
open HeytingLean.LoF.Comb

open HeytingLean.LoF.Correspondence
open HeytingLean.LoF.Correspondence.SKYBool
open HeytingLean.LoF.Correspondence.StepsLemmas

namespace BoolSim

/-! ## Compiling Boolean functions to SKY -/

/-- Compile a unary Boolean function to a SKY term expecting one Church boolean. -/
def toSKYFun1 (g : Bool → Bool) : Comb :=
  SKYBool.iteFun (SKYBool.ofBool (g true)) (SKYBool.ofBool (g false))

/-- Compile a binary Boolean function to a SKY term expecting two Church booleans. -/
def toSKYFun2 (f : Bool → Bool → Bool) : Comb :=
  SKYBool.iteFun (toSKYFun1 fun a => f true a) (toSKYFun1 fun a => f false a)

theorem steps_apply_toSKYFun1 (g : Bool → Bool) (a : Bool) :
    Comb.Steps (Comb.app (toSKYFun1 g) (SKYBool.ofBool a)) (SKYBool.ofBool (g a)) := by
  cases a with
  | false =>
      simpa [toSKYFun1] using
        (SKYBool.iteFun_ofBool (b := false)
          (t := SKYBool.ofBool (g true)) (f := SKYBool.ofBool (g false)))
  | true =>
      simpa [toSKYFun1] using
        (SKYBool.iteFun_ofBool (b := true)
          (t := SKYBool.ofBool (g true)) (f := SKYBool.ofBool (g false)))

theorem steps_apply_toSKYFun2 (f : Bool → Bool → Bool) (b a : Bool) :
    Comb.Steps
        (Comb.app (Comb.app (toSKYFun2 f) (SKYBool.ofBool b)) (SKYBool.ofBool a))
        (SKYBool.ofBool (f b a)) := by
  cases b with
  | false =>
      have hOuter :
          Comb.Steps
            (Comb.app (toSKYFun2 f) (SKYBool.ofBool false))
            (toSKYFun1 fun a => f false a) := by
        simpa [toSKYFun2] using
          (SKYBool.iteFun_ofBool (b := false)
            (t := toSKYFun1 fun a => f true a) (f := toSKYFun1 fun a => f false a))
      have h1 :
          Comb.Steps
            (Comb.app (Comb.app (toSKYFun2 f) (SKYBool.ofBool false)) (SKYBool.ofBool a))
            (Comb.app (toSKYFun1 fun a => f false a) (SKYBool.ofBool a)) :=
        steps_app_left (a := SKYBool.ofBool a) hOuter
      exact steps_transitive h1 (steps_apply_toSKYFun1 (g := fun a => f false a) a)
  | true =>
      have hOuter :
          Comb.Steps
            (Comb.app (toSKYFun2 f) (SKYBool.ofBool true))
            (toSKYFun1 fun a => f true a) := by
        simpa [toSKYFun2] using
          (SKYBool.iteFun_ofBool (b := true)
            (t := toSKYFun1 fun a => f true a) (f := toSKYFun1 fun a => f false a))
      have h1 :
          Comb.Steps
            (Comb.app (Comb.app (toSKYFun2 f) (SKYBool.ofBool true)) (SKYBool.ofBool a))
            (Comb.app (toSKYFun1 fun a => f true a) (SKYBool.ofBool a)) :=
        steps_app_left (a := SKYBool.ofBool a) hOuter
      exact steps_transitive h1 (steps_apply_toSKYFun1 (g := fun a => f true a) a)

/-! ## Iterating the compiled step along a finite word -/

/-- Deterministic fold of a Boolean transition `R` along a finite input word. -/
def run (R : Bool → Bool → Bool) : Bool → List Bool → Bool
  | b, [] => b
  | b, a :: w => run R (R b a) w

/-- Build the SKY term corresponding to iterating a 2-argument step function along a word. -/
def applyWordTerm (step : Comb) : Comb → List Comb → Comb
  | b, [] => b
  | b, a :: w => applyWordTerm step (Comb.app (Comb.app step b) a) w

theorem steps_applyWordTerm_state {step b b' : Comb} (hb : Comb.Steps b b') (w : List Comb) :
    Comb.Steps (applyWordTerm step b w) (applyWordTerm step b' w) := by
  induction w generalizing b b' with
  | nil =>
      simpa [applyWordTerm] using hb
  | cons a w ih =>
      -- Lift `hb` under the context `λt. step t a` and iterate.
      have h1 : Comb.Steps (Comb.app (Comb.app step b) a) (Comb.app (Comb.app step b') a) := by
        have h1' : Comb.Steps (Comb.app step b) (Comb.app step b') := steps_app_right (f := step) hb
        exact steps_app_left (a := a) h1'
      simpa [applyWordTerm] using ih (b := Comb.app (Comb.app step b) a) (b' := Comb.app (Comb.app step b') a) h1

/-- End-to-end simulation: iterating the compiled step reduces to the encoded reached state. -/
theorem steps_applyWordTerm_correct (R : Bool → Bool → Bool) (b : Bool) (w : List Bool) :
    Comb.Steps
        (applyWordTerm (toSKYFun2 R) (SKYBool.ofBool b) (w.map SKYBool.ofBool))
        (SKYBool.ofBool (run R b w)) := by
  induction w generalizing b with
  | nil =>
      simpa [applyWordTerm, run] using (Comb.Steps.refl (SKYBool.ofBool b))
  | cons a w ih =>
      -- One step on the head input, then recurse.
      have hStep :
          Comb.Steps
              (Comb.app (Comb.app (toSKYFun2 R) (SKYBool.ofBool b)) (SKYBool.ofBool a))
              (SKYBool.ofBool (R b a)) :=
        steps_apply_toSKYFun2 (f := R) (b := b) (a := a)
      have hLift :
          Comb.Steps
              (applyWordTerm (toSKYFun2 R)
                (Comb.app (Comb.app (toSKYFun2 R) (SKYBool.ofBool b)) (SKYBool.ofBool a))
                (w.map SKYBool.ofBool))
              (applyWordTerm (toSKYFun2 R) (SKYBool.ofBool (R b a)) (w.map SKYBool.ofBool)) :=
        steps_applyWordTerm_state (step := toSKYFun2 R) (b := _)
          (b' := SKYBool.ofBool (R b a)) hStep (w := w.map SKYBool.ofBool)
      -- Now apply the induction hypothesis at the successor state.
      have hIH :
          Comb.Steps
              (applyWordTerm (toSKYFun2 R) (SKYBool.ofBool (R b a)) (w.map SKYBool.ofBool))
              (SKYBool.ofBool (run R (R b a) w)) :=
        ih (b := R b a)
      -- Unfold the source term and combine.
      simpa [applyWordTerm, run] using steps_transitive hLift hIH

end BoolSim

end MRSystems
end LoF
end HeytingLean
