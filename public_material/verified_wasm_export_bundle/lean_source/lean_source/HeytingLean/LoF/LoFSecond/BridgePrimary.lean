import HeytingLean.LoF.LoFPrimary.Normalization
import HeytingLean.LoF.LoFSecond.Normalization

/-!
# LoFSecond.BridgePrimary — conservative extension of the primary calculus

`LoFPrimary` is a two-valued (Boolean) primary-calculus scaffold without re-entry.

`LoFSecond` extends the syntax with an explicit `reentry` constant and switches the semantics to a
Kleene-style 3-valued truth type (`Tri`), allowing a fixed point of negation.

This file proves that `LoFSecond` is a **conservative extension** of `LoFPrimary`:

* there is an embedding `LoFPrimary.Expr n → LoFSecond.Expr n`;
* evaluation commutes under the Boolean→Tri embedding;
* primary rewrite steps map to second-degree rewrite steps.
-/

namespace HeytingLean
namespace LoF
namespace LoFSecond

/-! ## Primary expressions embed into second-degree expressions -/

def Expr.ofPrimary {n : Nat} : LoFPrimary.Expr n → Expr n
  | .void => .void
  | .var i => .var i
  | .mark A => .mark (Expr.ofPrimary A)
  | .juxt A B => .juxt (Expr.ofPrimary A) (Expr.ofPrimary B)

namespace Tri

/-- Embed Boolean truth values into the 3-valued semantics (`false ↦ f`, `true ↦ t`). -/
def ofBool : Bool → Tri
  | false => .f
  | true => .t

@[simp] theorem ofBool_false : ofBool false = .f := rfl
@[simp] theorem ofBool_true : ofBool true = .t := rfl

@[simp] theorem not_ofBool (b : Bool) :
    Tri.not (ofBool b) = ofBool (!b) := by
  cases b <;> rfl

@[simp] theorem or_ofBool (a b : Bool) :
    Tri.or (ofBool a) (ofBool b) = ofBool (a || b) := by
  cases a <;> cases b <;> rfl

end Tri

/-! ## Evaluation commutes on the embedded fragment -/

variable {n : Nat}

def valOfBool (ρ : Fin n → Bool) : Fin n → Tri :=
  fun i => Tri.ofBool (ρ i)

theorem eval_ofPrimary (A : LoFPrimary.Expr n) (ρ : Fin n → Bool) :
    eval (n := n) (Expr.ofPrimary A) (valOfBool (n := n) ρ) =
      Tri.ofBool (LoFPrimary.eval (n := n) A ρ) := by
  induction A with
  | void =>
      rfl
  | var i =>
      rfl
  | mark A ih =>
      simp [Expr.ofPrimary, LoFPrimary.eval, eval, ih]
  | juxt A B ihA ihB =>
      simp [Expr.ofPrimary, LoFPrimary.eval, eval, ihA, ihB]

/-! ## Primary rewrite steps embed into second-degree steps -/

theorem step_ofPrimary {A B : LoFPrimary.Expr n} :
    LoFPrimary.Step A B → Step (Expr.ofPrimary A) (Expr.ofPrimary B) := by
  intro h
  induction h with
  | calling A =>
      simpa [Expr.ofPrimary] using Step.calling (A := Expr.ofPrimary A)
  | crossing A =>
      simpa [Expr.ofPrimary] using Step.crossing (A := Expr.ofPrimary A)
  | void_left A =>
      simpa [Expr.ofPrimary] using Step.void_left (A := Expr.ofPrimary A)
  | void_right A =>
      simpa [Expr.ofPrimary] using Step.void_right (A := Expr.ofPrimary A)
  | juxt_left h ih =>
      simpa [Expr.ofPrimary] using Step.juxt_left (B := Expr.ofPrimary _) ih
  | juxt_right h ih =>
      simpa [Expr.ofPrimary] using Step.juxt_right (A := Expr.ofPrimary _) ih
  | mark_congr h ih =>
      simpa [Expr.ofPrimary] using Step.mark_congr ih

theorem steps_ofPrimary {A B : LoFPrimary.Expr n} :
    LoFPrimary.Steps A B → Steps (Expr.ofPrimary A) (Expr.ofPrimary B) := by
  intro h
  induction h with
  | refl A =>
      exact Steps.refl (Expr.ofPrimary A)
  | trans hstep hsteps ih =>
      exact Steps.trans (step_ofPrimary hstep) ih

end LoFSecond
end LoF
end HeytingLean

