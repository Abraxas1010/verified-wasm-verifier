import HeytingLean.EpistemicCalculus.Basic
import Mathlib.Order.CompleteLattice.Basic

namespace HeytingLean

variable (V : Type*) [EpistemicCalculus V]

/-- E1: optimistic (top element exists). -/
class Optimistic where
  top : V
  le_top : ∀ x : V, x ≤ top

/-- E2: complete (all joins/meets exist). -/
class Complete extends CompleteLattice V

/-- E3: conservative fusion (no certainty creation). -/
class ConservativeFusion where
  no_certainty_creation :
    ∀ x y : V,
      EpistemicCalculus.unit ≤ x fus y →
        (EpistemicCalculus.unit ≤ x) ∨ (EpistemicCalculus.unit ≤ y)

/-- E4: closed (residuated internal hom). -/
class Closed where
  ihom : V → V → V
  adjunction : ∀ x y z : V, (x fus y ≤ z) ↔ (x ≤ ihom y z)

/-- E5: strongly conservative (fusion is inflationary on left input). -/
class StronglyConservative where
  no_decrease : ∀ x y : V, x ≤ x fus y

/-- E6: idempotent fusion. -/
class IdempotentFusion where
  idem : ∀ x : V, x fus x = x

/-- E7: fallible/revisable. -/
class Fallible where
  revisable : ∀ x y : V, ∃ z : V, x fus z ≤ y

/-- E8: cancellative fusion. -/
class Cancellative where
  cancel : ∀ x y z : V, x fus z ≤ y fus z → x ≤ y

end HeytingLean
