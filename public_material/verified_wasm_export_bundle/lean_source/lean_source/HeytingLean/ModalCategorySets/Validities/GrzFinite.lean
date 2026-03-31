import HeytingLean.ModalCategorySets.Propositional.Axioms
import HeytingLean.ModalCategorySets.Propositional.Core
import Mathlib.Order.Preorder.Finite

namespace HeytingLean.ModalCategorySets.Validities

open HeytingLean.ModalCategorySets.Propositional

universe u v

namespace OrderedFrames

/-- The Kripke frame induced by an order relation. -/
def orderFrame (W : Type u) [LE W] : Frame W where
  rel x y := x ≤ y

/-- Grzegorczyk's axiom is valid on every finite partial order. -/
theorem axiomGrz_valid_on_finite_partialOrder (W : Type u) [PartialOrder W] [Finite W]
    {α : Type v} (p : α) :
    (orderFrame W).Valid (axiomGrz p) := by
  intro val w hBox
  let M : Model W α := mkModel (orderFrame W) val
  by_contra hpw
  let S : Set W := {u | w ≤ u ∧ ¬ satisfies M u (.var p)}
  have hwS : w ∈ S := by
    exact And.intro le_rfl hpw
  have hSfin : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := Exists.intro w hwS
  rcases hSfin.exists_maximal hSnonempty with ⟨u, huS, huMax⟩
  have hwu : w ≤ u := huS.1
  have hNotPu : ¬ satisfies M u (.var p) := huS.2
  have hInner : satisfies M u (.imp (.box (.imp (.var p) (.box (.var p)))) (.var p)) :=
    hBox u hwu
  have hBoxStep : satisfies M u (.box (.imp (.var p) (.box (.var p)))) := by
    intro v huv hpv z hvz
    by_contra hpz
    have huz : u ≤ z := le_trans huv hvz
    have hwz : w ≤ z := le_trans hwu huz
    have hzS : z ∈ S := And.intro hwz hpz
    have hzu : z ≤ u := huMax hzS huz
    have hvu : v ≤ u := le_trans hvz hzu
    have hvuEq : v = u := le_antisymm hvu huv
    exact hNotPu (by simpa [hvuEq] using hpv)
  exact hNotPu (hInner hBoxStep)

end OrderedFrames

end HeytingLean.ModalCategorySets.Validities
