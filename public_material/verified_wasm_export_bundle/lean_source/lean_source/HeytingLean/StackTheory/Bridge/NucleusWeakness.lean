import HeytingLean.Core.HeytingAlgebra
import HeytingLean.StackTheory.Collective.Identity
import HeytingLean.StackTheory.Primitives.Task

namespace HeytingLean.StackTheory.Bridge

open HeytingLean

variable {Φ : Type*} [DecidableEq Φ]

section

variable [Fintype Φ]

/-- Bennett bridge novelty: once a Heyting order is sent contravariantly to extension inclusion,
weakness becomes antitone on the nucleus-fixed locus. -/
theorem weakness_monotone_on_fixed_points
    {L : Type*} [HeytingAlgebra L]
    (N : Core.Nucleus L)
    (toPol : Core.FixedPointAlgebra L N → Finset (HeytingLean.StackTheory.Program Φ))
    (v : HeytingLean.StackTheory.Vocabulary Φ)
    (hMono :
      ∀ a b : Core.FixedPointAlgebra L N,
        (a : L) ≤ (b : L) →
          HeytingLean.StackTheory.extension v (toPol b) ⊆
            HeytingLean.StackTheory.extension v (toPol a))
    (a b : Core.FixedPointAlgebra L N)
    (hab : (a : L) ≤ (b : L)) :
    HeytingLean.StackTheory.weakness v (toPol b) ≤
      HeytingLean.StackTheory.weakness v (toPol a) := by
  exact Finset.card_le_card (hMono a b hab)

end

section

variable [Fintype Φ]

/-- Bennett bridge novelty: the concrete finite fixed locus of a nucleus acting on policies. -/
abbrev FixedPolicies (N : Core.Nucleus (Finset (HeytingLean.StackTheory.Program Φ))) :=
  { π : Finset (HeytingLean.StackTheory.Program Φ) // N.R π = π }

/-- Bennett bridge novelty: the forgetful encoding from the finite fixed locus back to Bennett
policies is contravariant with respect to extension inclusion. -/
def fixedPolicyEncoding
    (N : Core.Nucleus (Finset (HeytingLean.StackTheory.Program Φ)))
    (ω : FixedPolicies (Φ := Φ) N) :
    Finset (HeytingLean.StackTheory.Program Φ) :=
  ω.1

/-- Bennett bridge novelty: the concrete fixed-policy encoding inherited from a nucleus is
contravariant for Bennett extensions by the basic extension antitonicity lemma. -/
theorem fixedPolicyEncoding_contravariant
    (N : Core.Nucleus (Finset (HeytingLean.StackTheory.Program Φ)))
    (v : HeytingLean.StackTheory.Vocabulary Φ)
    {ω₁ ω₂ : FixedPolicies (Φ := Φ) N}
    (hω : fixedPolicyEncoding N ω₁ ⊆ fixedPolicyEncoding N ω₂) :
    HeytingLean.StackTheory.extension v (fixedPolicyEncoding N ω₂) ⊆
      HeytingLean.StackTheory.extension v (fixedPolicyEncoding N ω₁) := by
  exact HeytingLean.StackTheory.ext_mono v _ _ hω

/-- Bennett bridge novelty: the concretely constructed encoding from nucleus-fixed policies to
ordinary policies yields an actual weakness monotonicity theorem, not just a parameterized one. -/
theorem weakness_monotone_on_fixed_policies
    (N : Core.Nucleus (Finset (HeytingLean.StackTheory.Program Φ)))
    (v : HeytingLean.StackTheory.Vocabulary Φ)
    {ω₁ ω₂ : FixedPolicies (Φ := Φ) N}
    (hω : fixedPolicyEncoding N ω₁ ⊆ fixedPolicyEncoding N ω₂) :
    HeytingLean.StackTheory.weakness v (fixedPolicyEncoding N ω₂) ≤
      HeytingLean.StackTheory.weakness v (fixedPolicyEncoding N ω₁) := by
  exact Finset.card_le_card (fixedPolicyEncoding_contravariant N v hω)

/-- Bennett bridge novelty: a collective policy that is simultaneously a nucleus-fixed point in
the policy powerset. This packages the Bennett collective-identity condition with the Heyting
fixed-locus condition into a single bridge object. -/
structure StableCollectivePolicy
    (N : Core.Nucleus (Set (HeytingLean.StackTheory.Program Φ)))
    {m : ℕ} (v : HeytingLean.StackTheory.Vocabulary Φ)
    (parts : Fin m → HeytingLean.StackTheory.VTask v) where
  policy : Finset (HeytingLean.StackTheory.Program Φ)
  collective : policy ∈ HeytingLean.StackTheory.collectivePolicies v parts
  fixed : N.R (policy : Set (HeytingLean.StackTheory.Program Φ)) =
    (policy : Set (HeytingLean.StackTheory.Program Φ))

/-- Bennett bridge novelty: two stable collective policies with nonempty intersection generate a
nontrivial meet in the fixed-point algebra `Ω_R`. This is the explicit bridge from Bennett's
collective identity to nontriviality of `inf` in the Heyting fixed locus. -/
theorem collective_identity_yields_nontrivial_meet_in_fixed_locus
    (N : Core.Nucleus (Set (HeytingLean.StackTheory.Program Φ)))
    {m : ℕ} (v : HeytingLean.StackTheory.Vocabulary Φ)
    (parts : Fin m → HeytingLean.StackTheory.VTask v)
    (a b : StableCollectivePolicy N v parts)
    (hMeet : (a.policy ∩ b.policy).Nonempty) :
    HeytingLean.StackTheory.hasCollectiveIdentity v parts ∧
      ∃ ωa ωb : HeytingLean.Core.FixedPointAlgebra (Set (HeytingLean.StackTheory.Program Φ)) N,
        ((HeytingLean.Core.FixedPointAlgebra.inf ωa ωb :
          HeytingLean.Core.FixedPointAlgebra (Set (HeytingLean.StackTheory.Program Φ)) N) :
            Set (HeytingLean.StackTheory.Program Φ)) ≠ ⊥ := by
  refine ⟨⟨a.policy, a.collective⟩, ?_⟩
  refine ⟨⟨(a.policy : Set (HeytingLean.StackTheory.Program Φ)), a.fixed⟩,
    ⟨(b.policy : Set (HeytingLean.StackTheory.Program Φ)), b.fixed⟩, ?_⟩
  intro hBot
  rcases hMeet with ⟨p, hp⟩
  have hpSet :
      p ∈ (((HeytingLean.Core.FixedPointAlgebra.inf
        ⟨(a.policy : Set (HeytingLean.StackTheory.Program Φ)), a.fixed⟩
        ⟨(b.policy : Set (HeytingLean.StackTheory.Program Φ)), b.fixed⟩ :
          HeytingLean.Core.FixedPointAlgebra (Set (HeytingLean.StackTheory.Program Φ)) N) :
            Set (HeytingLean.StackTheory.Program Φ))) := by
    simpa [HeytingLean.Core.FixedPointAlgebra.inf] using hp
  rw [hBot] at hpSet
  exact hpSet.elim

end

section

/-- Bennett bridge novelty: if a policy encoding lands in the fixed locus of a nucleus,
then the intersection of two stable policies is stable as well. -/
theorem stable_policy_closed_inf
    {L : Type*} [HeytingAlgebra L]
    (N : Core.Nucleus L)
    (encode : Finset (HeytingLean.StackTheory.Program Φ) → L)
    (hEncodeInf :
      ∀ π ρ,
        encode (π ∩ ρ) = encode π ⊓ encode ρ)
    {π ρ : Finset (HeytingLean.StackTheory.Program Φ)}
    (hπ : N.R (encode π) = encode π)
    (hρ : N.R (encode ρ) = encode ρ) :
    N.R (encode (π ∩ ρ)) = encode (π ∩ ρ) := by
  rw [hEncodeInf, N.meet_preserving, hπ, hρ]

end

end HeytingLean.StackTheory.Bridge
