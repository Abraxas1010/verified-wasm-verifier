import Mathlib.Order.Basic
import HeytingLean.Calculus.CalculusLens

/-!
R as a λ‑calculus / type‑level modality (Phase 2, signatures only)

This pass provides a lightweight modality record and a projection
from the calculus nucleus. Heavy type‑theoretic development is deferred.
-/

namespace HeytingLean
namespace Calculus

universe u

structure RModal (α : Type u) [LE α] where
  R : α → α
  idem : ∀ a, R (R a) = R a
  ext  : ∀ a, a ≤ R a

namespace RModal

variable {α : Type u} [LE α]

def Omega (M : RModal α) : Set α := {a | M.R a = a}

@[simp] lemma mem_Omega {M : RModal α} {a : α} :
    a ∈ M.Omega ↔ M.R a = a := Iff.rfl

end RModal

/-! Bridge from a CalculusNucleus to an RModal (losing `map_inf`). -/

def ofCalculusNucleus {α : Type u} [CompleteLattice α]
    (N : Calculus.CalculusNucleus α) : RModal α :=
  { R := N.R
    idem := N.idempotent
    ext := N.extensive }

end Calculus
end HeytingLean
