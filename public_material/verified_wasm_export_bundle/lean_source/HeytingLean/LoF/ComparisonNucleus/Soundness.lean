import Mathlib.Order.Nucleus
import HeytingLean.LoF.ComparisonNucleus.Spec

/-!
# Soundness of the comparison nucleus
-/

namespace HeytingLean
namespace LoF
namespace Comparison

open scoped Classical

universe u v

variable {L : Type u} {Ω : Type v}
variable [CompleteLattice L] [CompleteLattice Ω]

/-- Core closure `R := g ∘ f`. -/
@[simp] def act (S : CompSpec L Ω) (x : L) : L :=
  S.g (S.f x)

lemma act_monotone (S : CompSpec L Ω) : Monotone (act S) := by
  intro x y hxy
  exact S.mon_g (S.mon_f hxy)

/-- The composite `g ∘ f` is extensive: every element lies below its image. -/
lemma act_le (S : CompSpec L Ω) (x : L) : x ≤ act S x := by
  change x ≤ S.g (S.f x)
  exact (S.gc x (S.f x)).mp le_rfl

/-- Applying the composite twice collapses: `act` is idempotent up to ≤. -/
lemma act_idem_le (S : CompSpec L Ω) (x : L) :
    act S (act S x) ≤ act S x := by
  dsimp [act]
  have hx : S.g (S.f x) ≤ S.g (S.f x) := le_rfl
  have hx' : S.f (S.g (S.f x)) ≤ S.f x :=
    (S.gc (S.g (S.f x)) (S.f x)).mpr hx
  exact S.mon_g hx'

/-- Nucleus obtained from the strong hypothesis pack. -/
def nucleusOfGcMeet (S : StrongHyp L Ω) : Nucleus L :=
{ toFun := act (S := (S : CompSpec L Ω))
  map_inf' := by
    intro x y
    dsimp [act]
    have hstrong := S.map_inf x y
    have hg : S.g (S.f (x ⊓ y)) = S.g (S.f x ⊓ S.f y) :=
      congrArg S.g hstrong
    simp [S.gc.u_inf] at hg
    exact hg
  idempotent' := by
    intro x
    exact act_idem_le (S := (S : CompSpec L Ω)) x
  le_apply' := by
    intro x
    exact act_le (S := (S : CompSpec L Ω)) x }

lemma frobenius_map_inf (S : FrobeniusHyp L Ω)
    (x y : L) :
    S.f (act (S := (S : CompSpec L Ω)) x ⊓
         act (S := (S : CompSpec L Ω)) y) = S.f x ⊓ S.f y := by
  have hcollapse_x : S.f (S.g (S.f x)) = S.f x :=
    le_antisymm
      ((S.gc (S.g (S.f x)) (S.f x)).mpr le_rfl)
      (S.mon_f (act_le (S := (S : CompSpec L Ω)) x))
  have hcollapse_y : S.f (S.g (S.f y)) = S.f y :=
    le_antisymm
      ((S.gc (S.g (S.f y)) (S.f y)).mpr le_rfl)
      (S.mon_f (act_le (S := (S : CompSpec L Ω)) y))
  have hf :=
    S.frobenius (x := S.g (S.f x)) (u := S.f y)
  simpa [act, hcollapse_x, hcollapse_y] using hf

/-- Nucleus obtained from the Frobenius/meet-lower-bound hypothesis pack. -/
def nucleusOfGcFrobenius (S : FrobeniusHyp L Ω) : Nucleus L :=
{ toFun := act (S := (S : CompSpec L Ω))
  map_inf' := by
    intro x y
    apply le_antisymm
    · refine le_inf ?hx ?hy
      · exact (act_monotone (S := (S : CompSpec L Ω))) inf_le_left
      · exact (act_monotone (S := (S : CompSpec L Ω))) inf_le_right
    ·
      have hgoal :
          S.f (act (S := (S : CompSpec L Ω)) x ⊓
                act (S := (S : CompSpec L Ω)) y)
            ≤ S.f (x ⊓ y) := by
        have h₁ := frobenius_map_inf (S := S) x y
        have h₂ := S.meet_lb x y
        exact h₁ ▸ h₂
      have hx :=
        (S.gc (act (S := (S : CompSpec L Ω)) x ⊓
                 act (S := (S : CompSpec L Ω)) y) (S.f (x ⊓ y))).mp hgoal
      simpa [act] using hx
  idempotent' := by
    intro x
    exact act_idem_le (S := (S : CompSpec L Ω)) x
  le_apply' := by
    intro x
    exact act_le (S := (S : CompSpec L Ω)) x }

/-- Comparison hypothesis packs. -/
inductive HypPack (L : Type u) (Ω : Type v)
    [CompleteLattice L] [CompleteLattice Ω] : Type _
  | strong : StrongHyp L Ω → HypPack L Ω
  | frobenius : FrobeniusHyp L Ω → HypPack L Ω

namespace HypPack

/-- Underlying spec of a hypothesis pack. -/
def spec {L Ω} [CompleteLattice L] [CompleteLattice Ω]
    (h : HypPack L Ω) : CompSpec L Ω :=
  match h with
  | .strong S => S
  | .frobenius S => S

/-- Nucleus obtained from a hypothesis pack. -/
def nucleus {L Ω} [CompleteLattice L] [CompleteLattice Ω]
    (h : HypPack L Ω) : Nucleus L :=
  match h with
  | .strong S => nucleusOfGcMeet (S := S)
  | .frobenius S => nucleusOfGcFrobenius (S := S)

lemma nucleus_apply {L Ω} [CompleteLattice L] [CompleteLattice Ω]
    (h : HypPack L Ω) (x : L) :
    nucleus (h := h) x = act (spec (h := h)) x := by
  cases h <;> rfl

end HypPack

/-- Fixed points of `R := g ∘ f`. -/
def ΩR (S : CompSpec L Ω) : Type u := {x : L // act S x = x}

lemma act_coe_ΩR {S : CompSpec L Ω} (x : ΩR S) :
    act S x.val = x.val := by
  simpa using x.property

@[simp] lemma g_is_closed (S : CompSpec L Ω) (u : Ω) :
  act S (S.g u) = S.g u := by
  -- ≤ via counit then monotone g
  have h₁ : S.f (S.g u) ≤ u := (S.gc (S.g u) u).mpr le_rfl
  have h₁' : S.g (S.f (S.g u)) ≤ S.g u := S.mon_g h₁
  -- ≥ via unit
  have h₂ : S.g u ≤ S.g (S.f (S.g u)) := (S.gc (S.g u) (S.f (S.g u))).mp le_rfl
  exact le_antisymm h₁' h₂

end Comparison
end LoF
end HeytingLean
