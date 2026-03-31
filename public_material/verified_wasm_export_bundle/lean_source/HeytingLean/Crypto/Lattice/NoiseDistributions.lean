import HeytingLean.Crypto.Lattice.Distributions
import HeytingLean.Crypto.Lattice.Problems
import HeytingLean.Crypto.Lattice.CBD
import HeytingLean.Crypto.RNG.Seeded

namespace HeytingLean
namespace Crypto
namespace Lattice

/-!
# Deterministic noise distribution shapes (v1.2 foundations)

This file records **shape-only** deterministic samplers aligned with the interfaces used by
Kyber/ML-KEM and Dilithium/ML-DSA-style distributions.

Important:
- These are deterministic façades for testing and future refinement.
- We do **not** claim statistical properties (e.g. closeness to true CBD) in this layer.
- Proof obligations here are intentionally trivial (totality + seeded reproducibility).
-/

namespace NoiseDist

open HeytingLean.Crypto.Lattice

/-- Centered-binomial sampler shape (deterministic, seed-indexed). -/
structure CenteredBinomialShape where
  η : Nat
  n : Nat
  q : Nat
  sample : Dist.Seed → Fin n → ZMod q

theorem CenteredBinomialShape.sample_total (S : CenteredBinomialShape) (seed : Dist.Seed) (i : Fin S.n) :
    ∃ x, S.sample seed i = x :=
  ⟨S.sample seed i, rfl⟩

theorem CenteredBinomialShape.sample_reproducible (S : CenteredBinomialShape)
    {seed₁ seed₂ : Dist.Seed} (h : seed₁ = seed₂) (i : Fin S.n) :
    S.sample seed₁ i = S.sample seed₂ i := by
  simp [h]

/-- Adapter: use the existing deterministic `Dist.centeredBinomial` bitstream sampler. -/
def centeredBinomialFromDist (η n q : Nat) : CenteredBinomialShape where
  η := η
  n := n
  q := q
  sample := fun seed i =>
    let arr := Dist.centeredBinomial η seed n
    (arr[i.1]'(by
      -- `centeredBinomial` produces an array of length `n`.
      have hsize : arr.size = n := by
        simpa [arr] using (Dist.centeredBinomial_size (eta := η) (s := seed) (n := n))
      exact Nat.lt_of_lt_of_eq i.2 hsize.symm) : Int)

theorem centeredBinomialFromDist_coeffBound_le {η n q : Nat} (hη : 0 < η) [NeZero q] (hq : 2 * η < q)
    (seed : Dist.Seed) (i : Fin n) :
    coeffBound (q := q) ((centeredBinomialFromDist η n q).sample seed i) ≤ η := by
  let arr := Dist.centeredBinomial η seed n
  have hsize : arr.size = n := by simpa [arr] using (Dist.centeredBinomial_size (eta := η) (s := seed) (n := n))
  have hx : Int.natAbs (arr[i.1]'(Nat.lt_of_lt_of_eq i.2 hsize.symm)) ≤ η :=
    Dist.centeredBinomial_get_natAbs_le (eta := η) (s := seed) (n := n) i
  -- Cast bounded `Int` noise into `ZMod q` and apply the centered bound lemma.
  simpa [centeredBinomialFromDist, arr] using
    (HeytingLean.Crypto.Lattice.CBD.coeffBound_int_cast_le (q := q) (p := { eta := η, hpos := hη })
      (x := (arr[i.1]'(Nat.lt_of_lt_of_eq i.2 hsize.symm) : Int)) (hx := hx) (hq := hq))

/-- Uniform sampler shape (deterministic, seed-indexed). -/
structure UniformModShape where
  n : Nat
  q : Nat
  sample : Dist.Seed → Fin n → ZMod q

theorem UniformModShape.sample_total (S : UniformModShape) (seed : Dist.Seed) (i : Fin S.n) :
    ∃ x, S.sample seed i = x :=
  ⟨S.sample seed i, rfl⟩

theorem UniformModShape.sample_reproducible (S : UniformModShape)
    {seed₁ seed₂ : Dist.Seed} (h : seed₁ = seed₂) (i : Fin S.n) :
    S.sample seed₁ i = S.sample seed₂ i := by
  simp [h]

/-- Adapter: use the existing deterministic `Dist.uniformMod` sampler. -/
def uniformModFromDist (n q : Nat) : UniformModShape where
  n := n
  q := q
  sample := fun seed i =>
    ((Dist.uniformMod q seed n)[i.1]! : Int)

end NoiseDist

end Lattice
end Crypto
end HeytingLean
