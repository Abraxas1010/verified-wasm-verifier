import HeytingLean.LoF.ComparisonNucleus.Spec
import HeytingLean.LoF.ComparisonNucleus.Soundness
import HeytingLean.LoF.HoTT.Identity
universe u v

namespace HeytingLean
namespace LoF
namespace Comparison

open Order

variable {L : Type u} {Ω : Type v}
variable [CompleteLattice L] [CompleteLattice Ω]

/-- Encoder to Ω using the comparison L→Ω map. -/
def enc (S : CompSpec L Ω) : ΩR S → Ω := fun a => S.f a.val

/-- Decoder from Ω using Ω→L map, closed by `act`. -/
def dec (S : CompSpec L Ω) : Ω → ΩR S :=
  fun u => ⟨ S.g u, g_is_closed S u ⟩

/-- Round-trip identity on the fixed-point core. -/
@[simp] theorem RT1 (S : CompSpec L Ω) :
  (fun a : ΩR S => dec S (enc S a)) = id := by
  funext a
  apply Subtype.ext
  have hx : act S a.val = a.val := a.property
  simpa [act, enc, dec]

/-- HoTT-style (path-level) RT-1: round-trip identity on the fixed-point core
rephrased using the `Id` alias. This is just `RT1` applied to a point. -/
theorem rt1_path (S : CompSpec L Ω) (a : ΩR S) :
  Id (dec S (enc S a)) a := by
  -- `RT1` identifies the round-trip function with `id`, so we specialize at `a`.
  have h := RT1 (S := S)
  exact congrArg (fun f => f a) h

/-- Ω-side interior induced by the Galois connection: `RΩ := f ∘ g`. -/
def RΩ (S : CompSpec L Ω) : Ω → Ω := fun u => S.f (S.g u)

/-- Closed join on Ω: `u ⊔RΩ v := RΩ (u ⊔ v)`. -/
def supΩ (S : CompSpec L Ω) (u v : Ω) : Ω := RΩ S (u ⊔ v)

/-- Closed join on ΩR via the nucleus act. -/
def supR (S : CompSpec L Ω) (a b : ΩR S) : ΩR S :=
  ⟨ act S (a.val ⊔ b.val), by
      -- idempotence + extensivity
      have h₁ := act_idem_le (S := S) (x := a.val ⊔ b.val)
      have h₂ := act_le (S := S) (x := act S (a.val ⊔ b.val))
      exact le_antisymm h₁ h₂ ⟩

/-- `enc` distributes over the closed join on ΩR (≤ direction to the raw join). -/
theorem enc_supR_le (S : CompSpec L Ω) (a b : ΩR S) :
  enc S (supR S a b) ≤ (enc S a) ⊔ (enc S b) := by
  -- f (act t) ≤ f t by counit; and f preserves sup.
  have hf : S.f (a.val ⊔ b.val) = S.f a.val ⊔ S.f b.val :=
    (GaloisConnection.l_sup S.gc)
  have hC2 : S.f (S.g (S.f a.val ⊔ S.f b.val)) ≤ S.f a.val ⊔ S.f b.val :=
    (S.gc (S.g (S.f a.val ⊔ S.f b.val)) (S.f a.val ⊔ S.f b.val)).mpr le_rfl
  simpa [enc, supR, act, hf]

/-- `enc` distributes over the closed join on ΩR, landing in Ω-closed join (equality). -/
@[simp] theorem enc_supR_eq_supΩ (S : CompSpec L Ω) (a b : ΩR S) :
  enc S (supR S a b) = supΩ S (enc S a) (enc S b) := by
  have hf : S.f (a.val ⊔ b.val) = S.f a.val ⊔ S.f b.val :=
    (GaloisConnection.l_sup S.gc)
  simp [enc, supR, act, hf, RΩ, supΩ]

/-- Path-level version of `enc_supR_eq_supΩ` using the `Id` alias. -/
theorem enc_supR_path (S : CompSpec L Ω) (a b : ΩR S) :
  Id (enc S (supR S a b)) (supΩ S (enc S a) (enc S b)) :=
  enc_supR_eq_supΩ (S := S) (a := a) (b := b)

/-! ### Optional closed negation/implication under Heyting morphism hypotheses -/

variable [HeytingAlgebra L] [HeytingAlgebra Ω]

/-- Sufficient conditions for `f` to preserve Heyting operations. -/
structure HeytingMorphHyp (S : CompSpec L Ω) : Prop where
  map_imp : ∀ x y, S.f (x ⇨ y) = (S.f x ⇨ S.f y)

/-- Closed negation on Ω and ΩR. -/
def negΩ (S : CompSpec L Ω) (u : Ω) : Ω := RΩ S (u ⇨ S.f (⊥ : L))
def negR (S : CompSpec L Ω) (a : ΩR S) : ΩR S :=
  ⟨ act S (a.val ⇨ ⊥), by
      have h₁ := act_idem_le (S := S) (x := (a.val ⇨ ⊥))
      have h₂ := act_le (S := S) (x := act S (a.val ⇨ ⊥))
      exact le_antisymm h₁ h₂ ⟩

/-- Closed implication on Ω and ΩR. -/
def impΩ (S : CompSpec L Ω) (u v : Ω) : Ω := RΩ S (u ⇨ v)
def impR (S : CompSpec L Ω) (a b : ΩR S) : ΩR S :=
  ⟨ act S (a.val ⇨ b.val), by
      have h₁ := act_idem_le (S := S) (x := (a.val ⇨ b.val))
      have h₂ := act_le (S := S) (x := act S (a.val ⇨ b.val))
      exact le_antisymm h₁ h₂ ⟩

/-- Encoding preserves closed negation on ΩR assuming `f` preserves negation. -/
@[simp] theorem enc_negR_eq_negΩ (S : CompSpec L Ω)
  (hM : HeytingMorphHyp (S := S)) (a : ΩR S) :
  enc S (negR S a) = negΩ S (enc S a) := by
  -- enc (negR a) = f (act (a ⇨ ⊥)) = RΩ (f (a ⇨ ⊥)) = RΩ (f a ⇨ f ⊥) = RΩ (enc a ⇨ ⊥)
  have hmap := hM.map_imp (x := a.val) (y := (⊥ : L))
  have hmap0 : S.f (a.val ⇨ (⊥ : L)) = S.f a.val ⇨ S.f (⊥ : L) := by
    simpa using hmap
  have hmap' := congrArg (fun t => S.f (S.g t)) hmap0
  simpa [enc, negR, negΩ, act, RΩ] using hmap'

/-- Path-level encoding of closed negation on ΩR. -/
theorem enc_negR_path (S : CompSpec L Ω)
  (hM : HeytingMorphHyp (S := S)) (a : ΩR S) :
  Id (enc S (negR S a)) (negΩ S (enc S a)) :=
  enc_negR_eq_negΩ (S := S) (hM := hM) (a := a)

/-- Encoding preserves closed implication on ΩR assuming `f` preserves implication. -/
@[simp] theorem enc_impR_eq_impΩ (S : CompSpec L Ω)
  (hM : HeytingMorphHyp (S := S)) (a b : ΩR S) :
  enc S (impR S a b) = impΩ S (enc S a) (enc S b) := by
  have hmap := hM.map_imp (x := a.val) (y := b.val)
  simp [enc, impR, impΩ, act, RΩ, hmap]

/-- Path-level encoding of closed implication on ΩR. -/
theorem enc_impR_path (S : CompSpec L Ω)
  (hM : HeytingMorphHyp (S := S)) (a b : ΩR S) :
  Id (enc S (impR S a b)) (impΩ S (enc S a) (enc S b)) :=
  enc_impR_eq_impΩ (S := S) (hM := hM) (a := a) (b := b)

end Comparison
end LoF
end HeytingLean
