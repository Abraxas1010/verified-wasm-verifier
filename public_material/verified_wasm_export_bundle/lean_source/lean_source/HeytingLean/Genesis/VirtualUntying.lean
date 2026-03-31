import HeytingLean.Genesis.Stabilization

/-!
# Genesis.VirtualUntying

Virtual-logic untying façade over existing stabilization machinery.
-/

namespace HeytingLean.Genesis

open CoGame

/-- Facade alias: depth-truncated unrolling. -/
noncomputable def virtualUnroll (n : Nat) (G : CoGame) : SetTheory.PGame :=
  unroll n G

/-- Facade alias: interpretation of unrolled approximants. -/
def virtualInterpretUnroll (n : Nat) (g : SetTheory.PGame) : LoFExpr0 :=
  interpretUnroll n g

/-- Facade alias: Life approximant expression. -/
def lifeVirtualApproxExpr (n : Nat) : LoFExpr0 :=
  lifeApproxExpr n

/-- Untying at depth zero cuts any loop to Conway zero. -/
@[simp] theorem virtual_unroll_zero (G : CoGame) :
    virtualUnroll 0 G = (0 : SetTheory.PGame) := by
  rfl

/-- Canonical cut law for Life. -/
@[simp] theorem virtual_unroll_zero_life :
    virtualUnroll 0 CoGame.Life = (0 : SetTheory.PGame) := by
  simp [virtualUnroll]

/-- Virtual façade preserves the Life unroll-to-nesting anchor. -/
theorem virtual_interpret_unroll_life_anchor (n : Nat) :
    virtualInterpretUnroll n (virtualUnroll n CoGame.Life) = nesting n := by
  simpa [virtualInterpretUnroll, virtualUnroll] using interpret_unroll_life_anchor n

/-- Virtual façade preserves the Layer-2 nucleus closure law on Life approximants. -/
theorem virtual_unroll_nucleus_layer2 (n : Nat) :
    collapseNucleus (exprSupport (lifeVirtualApproxExpr n))
      =
      collapseNucleus (collapseNucleus (exprSupport (lifeVirtualApproxExpr n))) := by
  simp [lifeVirtualApproxExpr]

end HeytingLean.Genesis
