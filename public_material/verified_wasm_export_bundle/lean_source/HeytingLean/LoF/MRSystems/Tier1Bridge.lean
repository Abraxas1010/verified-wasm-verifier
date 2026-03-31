import HeytingLean.ClosingTheLoop.MR.ClosureOperator
import HeytingLean.LoF.MRSystems.Coalgebra
import HeytingLean.LoF.MRSystems.MooreTerminal

/-!
# Tier-1 (M,R) → coalgebra bridge (Phase E)

The Tier-1 Rosen scaffold (`HeytingLean.ClosingTheLoop.MR`) models:

* a selector space `Selector S` of *admissible* repair maps `Φ : B → H(A,B)`.

This module connects that to the abstract coalgebra core layer (`HeytingLean.LoF.MRSystems.MRCore`)
by forgetting admissibility proofs:

* any Tier-1 selector `Φ` induces a transition function `RΦ : B → A → B`,
  hence a reader coalgebra `B → (A → B)` and (via the Moore functor) a standard coalgebraic
  “behavior under finite input words” semantics.

We also record the key locality fact for the Tier-1 loop-closing operator `closeSelector`:
closing a selector at `b` preserves its *value at `b`*, hence preserves the induced transition
function at state `b`, hence preserves one-step Moore semantics from `b`.

This is the precise (Lean-verifiable) content of the slogan
“Tier-1 closure is a kernel-quotient of a local observation”.
-/

namespace HeytingLean
namespace LoF
namespace MRSystems

open scoped Classical

open HeytingLean.ClosingTheLoop.MR

universe u v

/-! ## Tier-1 selectors as MR cores -/

namespace MRCore

variable {S : MRSystem.{u, v}}

/-! ### Forgetful extraction -/

/-- Forget the admissibility proofs of a Tier-1 selector, producing a raw `MRCore`.

We use the distinguished metabolism `S.f` for the `M` component.
-/
def ofTier1Selector (S : MRSystem.{u, v}) (Φ : Selector S) : MRCore where
  A := S.A
  B := S.B
  M := S.f
  R := fun b => (Φ b).1

@[simp] theorem ofTier1Selector_A (S : MRSystem.{u, v}) (Φ : Selector S) :
    (ofTier1Selector S Φ).A = S.A := rfl

@[simp] theorem ofTier1Selector_B (S : MRSystem.{u, v}) (Φ : Selector S) :
    (ofTier1Selector S Φ).B = S.B := rfl

@[simp] theorem ofTier1Selector_M (S : MRSystem.{u, v}) (Φ : Selector S) :
    (ofTier1Selector S Φ).M = S.f := rfl

@[simp] theorem ofTier1Selector_R (S : MRSystem.{u, v}) (Φ : Selector S) (b : S.B) :
    (ofTier1Selector S Φ).R b = (Φ b).1 := rfl

theorem ofTier1Selector_R_mem_H (S : MRSystem.{u, v}) (Φ : Selector S) (b : S.B) :
    (ofTier1Selector S Φ).R b ∈ S.H := by
  simp [ofTier1Selector]

end MRCore

end MRSystems
end LoF
end HeytingLean

namespace HeytingLean
namespace LoF
namespace MRSystems

open HeytingLean.ClosingTheLoop.MR

universe u v

/-! ## Moore semantics and locality of `closeSelector` -/

namespace Tier1

open MooreFinal

variable {S : MRSystem.{u, v}} {b : S.B} (RI : RightInverseAt S b)

theorem R_at_closeSelector_eq (Φ : Selector S) :
    (MRCore.ofTier1Selector S (closeSelector S b RI Φ)).R b =
      (MRCore.ofTier1Selector S Φ).R b := by
  -- `closeSelector` is definitionally `β (Φ b)`, and it agrees with `Φ` at `b`.
  ext a
  simp [MRCore.ofTier1Selector]

theorem sem_singleton_closeSelector_eq (Φ : Selector S) (a : S.A) :
    (MRCore.ofTier1Selector S (closeSelector S b RI Φ)).semFrom b [a] =
      (MRCore.ofTier1Selector S Φ).semFrom b [a] := by
  -- Reduce both sides to `R b a`, then apply locality of `closeSelector` at `b`.
  let m₁ : MRCore := MRCore.ofTier1Selector S (closeSelector S b RI Φ)
  let m₂ : MRCore := MRCore.ofTier1Selector S Φ
  have hR : m₁.R b a = m₂.R b a :=
    congrArg (fun f => f a) (R_at_closeSelector_eq (S := S) (b := b) RI Φ)
  calc
    m₁.semFrom b [a] = m₁.R b a := by
      simpa [m₁] using (MRCore.semFrom_singleton (m := m₁) (b := b) (a := a))
    _ = m₂.R b a := hR
    _ = m₂.semFrom b [a] := by
      symm
      simpa [m₂] using (MRCore.semFrom_singleton (m := m₂) (b := b) (a := a))

end Tier1

end MRSystems
end LoF
end HeytingLean
