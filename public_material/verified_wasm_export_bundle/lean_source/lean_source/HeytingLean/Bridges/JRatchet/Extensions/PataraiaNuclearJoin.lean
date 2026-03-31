import HeytingLean.PerspectivalPlenum.ReReentryTower
import HeytingLean.Logic.ReflectionProgression
import Mathlib.Order.Nucleus

/-!
# PataraiaNuclearJoin

This module formalizes a pre-ratchet join lane inspired by Pataraia-style
fixed-point constructions (Pataraia 1997; Escardo 2003).

The key implementation move is to treat a pre-ratchet step as an inflationary,
monotone operator on `Nucleus α`, then reflect it into a closure operator on
`Nucleus α` via `nucleusClosure`.
-/

namespace HeytingLean
namespace Bridges
namespace JRatchet
namespace Extensions
namespace PataraiaNuclearJoin

open HeytingLean.Logic
open HeytingLean.PerspectivalPlenum

universe u

variable {α : Type u} [Order.Frame α]

/-- A pre-ratchet step is an extensive and monotone operator on nuclei.

This is the second-order analogue of a prenucleus: idempotence is not required.
-/
structure PreRatchetStep where
  /-- The step action on nuclei. -/
  step : Nucleus α → Nucleus α
  /-- Extensiveness on nuclei. -/
  extensive : ∀ J : Nucleus α, J ≤ step J
  /-- Monotonicity on nuclei. -/
  monotone : Monotone step

/-- Coercion from a pre-ratchet step to its step function. -/
instance : CoeFun (PreRatchetStep (α := α)) (fun _ => Nucleus α → Nucleus α) where
  coe P := P.step

/-- The function underlying a pre-ratchet step is definitionally its `step` field. -/
@[simp] theorem coe_step (P : PreRatchetStep (α := α)) :
    (P.step : Nucleus α → Nucleus α) = P := rfl

/-- Forget idempotence from a true ratchet step. -/
def ofRatchetStep (S : RatchetStep α) : PreRatchetStep (α := α) where
  step := S.step
  extensive := S.extensive
  monotone := S.monotone

/-- Pointwise supremum of two pre-ratchet steps. -/
def preRatchetStepSup (S T : PreRatchetStep (α := α)) : PreRatchetStep (α := α) where
  step J := S.step J ⊔ T.step J
  extensive J := le_sup_of_le_left (S.extensive J)
  monotone := by
    intro J K hJK
    exact sup_le_sup (S.monotone hJK) (T.monotone hJK)

/-- Every nucleus is monotone.

This helper is specialized in this module to avoid depending on external monotonicity lemmas.
-/
theorem nucleusMonotone
    {β : Type u} [SemilatticeInf β] [OrderBot β] (n : Nucleus β) : Monotone n := by
  intro a b hab
  have hInf : a ⊓ b = a := inf_eq_left.mpr hab
  calc
    n a = n (a ⊓ b) := by simp [hInf]
    _ = n a ⊓ n b := _root_.Nucleus.map_inf (n := n) (x := a) (y := b)
    _ ≤ n b := inf_le_right

/-- The reflected nucleus on `Nucleus α` associated to a pre-ratchet step. -/
noncomputable def ratchetStepJoinNucleus (P : PreRatchetStep (α := α)) : Nucleus (Nucleus α) :=
  nucleusClosure (α := Nucleus α) P.step

/-- Join completion of a pre-ratchet step into a true ratchet step.

Construction: reflect `P.step` as a nucleus on `Nucleus α` via `nucleusClosure`.
-/
noncomputable def ratchetStepJoin (P : PreRatchetStep (α := α)) : RatchetStep α where
  step := ratchetStepJoinNucleus (α := α) P
  extensive J := _root_.Nucleus.le_apply (n := ratchetStepJoinNucleus (α := α) P) (x := J)
  monotone := nucleusMonotone (n := ratchetStepJoinNucleus (α := α) P)
  idempotent := by
    intro J
    let n : Nucleus (Nucleus α) := ratchetStepJoinNucleus (α := α) P
    apply le_antisymm
    · exact n.idempotent' J
    · exact (nucleusMonotone (n := n)) (_root_.Nucleus.le_apply (n := n) (x := J))

/-- Upper-bound half of the join specification. -/
theorem ratchetStepJoin_upper (P : PreRatchetStep (α := α)) :
    ∀ J : Nucleus α, P.step J ≤ (ratchetStepJoin (α := α) P).step J := by
  intro J
  simpa [ratchetStepJoin, ratchetStepJoinNucleus] using
    (le_nucleusClosure (α := Nucleus α) P.step J)

/-- Leastness of `ratchetStepJoin` among nucleus-valued upper bounds on `Nucleus α`.

This is the Pataraia-style least fixed-point reflection property used in this codebase.
-/
theorem ratchetStepJoin_leastNucleus
    (P : PreRatchetStep (α := α))
    {n : Nucleus (Nucleus α)}
    (hn : ∀ J : Nucleus α, P.step J ≤ n J) :
    ∀ J : Nucleus α, (ratchetStepJoin (α := α) P).step J ≤ n J := by
  intro J
  have hle : ratchetStepJoinNucleus (α := α) P ≤ n := by
    simpa [ratchetStepJoinNucleus] using
      (nucleusClosure_le_of_mem (α := Nucleus α) (f := P.step) (n := n) hn)
  exact hle J

/-- Combined specification: upper bound plus leastness over nucleus-on-nuclei bounds. -/
theorem ratchetStepJoin_spec
    (P : PreRatchetStep (α := α)) :
    (∀ J : Nucleus α, P.step J ≤ (ratchetStepJoin (α := α) P).step J) ∧
    (∀ n : Nucleus (Nucleus α),
      (∀ J : Nucleus α, P.step J ≤ n J) →
      ∀ J : Nucleus α, (ratchetStepJoin (α := α) P).step J ≤ n J) := by
  constructor
  · exact ratchetStepJoin_upper (α := α) P
  · intro n hn
    exact ratchetStepJoin_leastNucleus (α := α) P hn

/-- Pre-ratchet family supremum (inhabited index) without compatibility witnesses. -/
def ratchetFamilyPreRatchet {ι : Type u} [Inhabited ι]
    (f : ι → RatchetStep α) : PreRatchetStep (α := α) where
  step J := ⨆ i, (f i).step J
  extensive J := by
    exact le_trans ((f default).extensive J) (le_iSup (fun i => (f i).step J) default)
  monotone := by
    intro J K hJK
    refine iSup_le ?_
    intro i
    exact le_iSup_of_le i ((f i).monotone hJK)

/-- Join of a family of ratchet steps, computed without pairwise compatibility assumptions. -/
noncomputable def ratchetFamilyJoin {ι : Type u} [Inhabited ι]
    (f : ι → RatchetStep α) : RatchetStep α :=
  ratchetStepJoin (α := α) (ratchetFamilyPreRatchet (α := α) f)

end PataraiaNuclearJoin
end Extensions
end JRatchet
end Bridges
end HeytingLean
