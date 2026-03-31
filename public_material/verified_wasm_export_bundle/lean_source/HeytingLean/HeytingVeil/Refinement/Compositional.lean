import HeytingLean.HeytingVeil.Verify.Core

namespace HeytingLean
namespace HeytingVeil
namespace Refinement

open HeytingLean.HeytingVeil.Temporal
open HeytingLean.HeytingVeil.Verify

universe u v

def parallelCompose {S₁ : Type u} {S₂ : Type v}
    (M₁ : Machine S₁) (M₂ : Machine S₂) : Machine (S₁ × S₂) where
  Init := fun p => M₁.Init p.1 ∧ M₂.Init p.2
  Step := fun p q =>
    (M₁.Step p.1 q.1 ∧ q.2 = p.2) ∨ (M₂.Step p.2 q.2 ∧ q.1 = p.1)

def sequentialCompose {S : Type u}
    (M₁ : Machine S) (M₂ : Machine S) : Machine S where
  Init := fun s => M₁.Init s ∧ M₂.Init s
  Step := fun s u => ∃ m : S, M₁.Step s m ∧ M₂.Step m u

theorem compositional_invariant
    {S₁ : Type u} {S₂ : Type v}
    {M₁ : Machine S₁} {M₂ : Machine S₂}
    {Inv₁ : S₁ → Prop} {Inv₂ : S₂ → Prop}
    (cert₁ : InvariantCert M₁ Inv₁)
    (cert₂ : InvariantCert M₂ Inv₂) :
    InvariantCert (parallelCompose M₁ M₂) (fun p => Inv₁ p.1 ∧ Inv₂ p.2) := by
  constructor
  · intro p hp
    exact ⟨cert₁.init_holds _ hp.1, cert₂.init_holds _ hp.2⟩
  · intro p q hp hstep
    rcases hstep with hleft | hright
    · exact ⟨cert₁.step_preserves _ _ hp.1 hleft.1, by simpa [hleft.2] using hp.2⟩
    · exact ⟨by simpa [hright.2] using hp.1, cert₂.step_preserves _ _ hp.2 hright.1⟩

theorem sequential_compositional_invariant
    {S : Type u}
    {M₁ M₂ : Machine S}
    {Inv : S → Prop}
    (cert₁ : InvariantCert M₁ Inv)
    (cert₂ : InvariantCert M₂ Inv) :
    InvariantCert (sequentialCompose M₁ M₂) Inv := by
  constructor
  · intro s hs
    exact cert₁.init_holds s hs.1
  · intro s u hs hstep
    rcases hstep with ⟨m, hsm, hmu⟩
    have hm : Inv m := cert₁.step_preserves s m hs hsm
    exact cert₂.step_preserves m u hm hmu

theorem sequential_assume_guarantee
    {S : Type u}
    {M₁ M₂ : Machine S}
    {Assume Guarantee : S → Prop}
    (assume₁ : InvariantCert M₁ Assume)
    (assume₂ : InvariantCert M₂ Assume)
    (guarantee₁ : InvariantCert M₁ Guarantee)
    (guarantee₂_step :
      ∀ s t : S, Assume s → Guarantee s → M₂.Step s t → Guarantee t) :
    InvariantCert (sequentialCompose M₁ M₂) (fun s => Assume s ∧ Guarantee s) := by
  constructor
  · intro s hs
    exact ⟨assume₁.init_holds s hs.1, guarantee₁.init_holds s hs.1⟩
  · intro s u hs hstep
    rcases hs with ⟨hAssumeS, hGuaranteeS⟩
    rcases hstep with ⟨m, hsm, hmu⟩
    have hAssumeM : Assume m := assume₁.step_preserves s m hAssumeS hsm
    have hGuaranteeM : Guarantee m := guarantee₁.step_preserves s m hGuaranteeS hsm
    have hAssumeU : Assume u := assume₂.step_preserves m u hAssumeM hmu
    have hGuaranteeU : Guarantee u := guarantee₂_step m u hAssumeM hGuaranteeM hmu
    exact ⟨hAssumeU, hGuaranteeU⟩

end Refinement
end HeytingVeil
end HeytingLean
