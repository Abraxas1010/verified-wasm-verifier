import HeytingLean.Crypto.Lattice.NTT
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-!
# ML-KEM NTT correctness (algebraic form)

This module proves an **algebraic** NTT correctness statement for the ML-KEM modulus polynomial
`X^256 + 1` over `ZMod 3329`:

- `invNTT (NTT f) = f` (NTT and invNTT are inverses);
- `invNTT (NTT f * NTT g) = f * g` (multiplication correctness, where `*` on the NTT side is
  pointwise multiplication in the product ring).

We implement the NTT as a **Chinese Remainder Theorem (CRT)** ring isomorphism:

1. Use `cyclotomic_eq_prod_X_sub_primitiveRoots` to factor `Φ_256(X) = X^128 + 1` into linear
   factors over `ZMod 3329`, using the existence of a primitive 256th root (`ζ = 17`).
2. Substitute `X ↦ X^2` to obtain a factorization of `X^256 + 1 = Φ_256(X^2)` into 128 quadratic
   factors `X^2 - μ`, one for each primitive 256th root `μ`.
3. Apply the CRT to obtain a ring equivalence between `R/(X^256 + 1)` and the product of the
   quadratic quotients.

This is the “spec-level” correctness result needed to justify NTT-domain pointwise multiplication.
Connecting this ring isomorphism to the *concrete iterative NTT algorithm* (bit-reversal, twiddle
tables, etc.) is a further verification task.
-/

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace NTTCorrectness

open scoped BigOperators Polynomial Function
open Polynomial

def q : Nat := NTT.q
abbrev K : Type := ZMod q
abbrev R : Type := Polynomial K

instance : Fact (Nat.Prime q) := by
  dsimp [q, NTT.q]
  exact ⟨by native_decide⟩
instance : IsDomain K := by infer_instance

theorem zeta_orderOf : orderOf (NTT.zeta) = 256 := by
  classical
  have hn : 0 < (256 : Nat) := by decide
  refine orderOf_eq_of_pow_and_pow_div_prime hn NTT.zeta_pow_256 ?_
  intro p hp hp_dvd
  have hp2 : p = 2 := by
    have : p ∣ (2 : Nat) ^ (8 : Nat) := by
      simpa [show (256 : Nat) = 2 ^ (8 : Nat) by decide] using hp_dvd
    have : p ∣ (2 : Nat) :=
      Nat.Prime.dvd_of_dvd_pow hp this
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
  subst hp2
  simpa using NTT.zeta_pow_128_ne_one

theorem zeta_isPrimitiveRoot : IsPrimitiveRoot (NTT.zeta) 256 := by
  exact (IsPrimitiveRoot.iff_orderOf).2 zeta_orderOf

theorem cyclotomic_256_eq (K : Type) [CommRing K] :
    cyclotomic 256 K = (X ^ (128 : Nat) + 1 : K[X]) := by
  -- For `p = 2`, the geometric sum is `1 + X^(2^7)`.
  simpa [show (256 : Nat) = 2 ^ (8 : Nat) by decide, Nat.pow_succ, Nat.pow_zero, Nat.pow_one,
    Finset.sum_range_succ, pow_zero, pow_one, add_comm, add_left_comm, add_assoc] using
    (Polynomial.cyclotomic_prime_pow_eq_geom_sum (R := K) (p := 2) (n := 7) Nat.prime_two)

theorem modulusPoly_eq (K : Type) [CommRing K] :
    (X ^ (256 : Nat) + 1 : K[X]) = (cyclotomic 256 K).comp (X ^ (2 : Nat)) := by
  -- `X^256 + 1 = (X^128 + 1).comp (X^2)` and `X^256 = (X^2)^128`.
  rw [cyclotomic_256_eq (K := K)]
  simp only [add_comp, one_comp, X_pow_comp]
  have hx : (X ^ (256 : Nat) : K[X]) = (X ^ (2 : Nat) : K[X]) ^ (128 : Nat) := by
    -- `pow_mul` is oriented as `X^(2*128) = (X^2)^128`.
    simpa [show (256 : Nat) = 2 * (128 : Nat) by decide, pow_mul] using
      (pow_mul (X : K[X]) (2 : Nat) (128 : Nat))
  simp [hx, add_comm]

noncomputable def roots256 : Finset K :=
  primitiveRoots 256 K

noncomputable def quad (μ : K) : R :=
  (X ^ (2 : Nat) - C μ)

noncomputable def quadIdeal (μ : K) : Ideal R :=
  Ideal.span ({quad μ} : Set R)

theorem isCoprime_quad {a b : K} (hab : a ≠ b) :
    IsCoprime (quad a) (quad b) := by
  classical
  have hba : (b - a) ≠ (0 : K) := sub_ne_zero.mpr hab.symm
  refine ⟨C ((b - a)⁻¹), -C ((b - a)⁻¹), ?_⟩
  have : (quad a) - (quad b) = C (b - a) := by
    simp [quad, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  calc
    C ((b - a)⁻¹) * quad a + (-C ((b - a)⁻¹)) * quad b
        = C ((b - a)⁻¹) * (quad a - quad b) := by ring
    _ = C ((b - a)⁻¹) * C (b - a) := by simp [this]
    _ = C (((b - a)⁻¹) * (b - a)) := by simp [map_mul]
    _ = 1 := by
      have hmul : (b - a)⁻¹ * (b - a) = (1 : K) :=
        inv_mul_cancel₀ hba
      simp [hmul]

theorem pairwise_coprime_quadIdeals :
    Pairwise (IsCoprime on fun μ : roots256 => quadIdeal (μ : K)) := by
  classical
  intro μ ν hμν
  have hab : (μ : K) ≠ (ν : K) := by
    intro h
    apply hμν
    ext
    exact h
  have hcop : IsCoprime (quad (μ : K)) (quad (ν : K)) :=
    isCoprime_quad hab
  have hsup :
      quadIdeal (μ : K) ⊔ quadIdeal (ν : K) = ⊤ := by
    simpa [quadIdeal] using
      (Ideal.sup_eq_top_iff_isCoprime (x := quad (μ : K)) (y := quad (ν : K))).2 hcop
  refine ⟨⊤, ⊤, ?_⟩
  simp [hsup]

theorem modulusPoly_factorization :
    (X ^ (256 : Nat) + 1 : R) = ∏ μ ∈ roots256, quad μ := by
  classical
  have hz : cyclotomic 256 K = ∏ μ ∈ primitiveRoots 256 K, (X - C μ) :=
    Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots (K := K) zeta_isPrimitiveRoot
  have hcomp : ∀ μ : K, ((X - C μ : R).comp (X ^ (2 : Nat))) = quad μ := by
    intro μ
    simp [quad]
  have hfact :
      (cyclotomic 256 K).comp (X ^ (2 : Nat)) = ∏ μ ∈ primitiveRoots 256 K, quad μ := by
    calc
      (cyclotomic 256 K).comp (X ^ (2 : Nat))
          = (∏ μ ∈ primitiveRoots 256 K, (X - C μ : R)).comp (X ^ (2 : Nat)) := by
              simp [hz]
      _ = ∏ μ ∈ primitiveRoots 256 K, quad μ := by
            have hpc :
                (∏ μ ∈ primitiveRoots 256 K, (X - C μ : R)).comp (X ^ (2 : Nat)) =
                  ∏ μ ∈ primitiveRoots 256 K, ((X - C μ : R).comp (X ^ (2 : Nat))) :=
              Polynomial.prod_comp (s := primitiveRoots 256 K)
                (p := fun μ : K => (X - C μ : R)) (q := (X ^ (2 : Nat) : R))
            have hrewrite :
                (∏ μ ∈ primitiveRoots 256 K, ((X - C μ : R).comp (X ^ (2 : Nat)))) =
                  ∏ μ ∈ primitiveRoots 256 K, quad μ := by
              refine Finset.prod_congr rfl ?_
              intro μ _hμ
              exact hcomp μ
            exact hpc.trans hrewrite
  calc
    (X ^ (256 : Nat) + 1 : R) = (cyclotomic 256 K).comp (X ^ (2 : Nat)) := modulusPoly_eq (K := K)
    _ = ∏ μ ∈ roots256, quad μ := by
          simpa [roots256] using hfact

theorem modulusIdeal_eq_iInf_quadIdeal :
    Ideal.span ({(X ^ (256 : Nat) + 1 : R)} : Set R) =
      ⨅ μ : roots256, quadIdeal (μ : K) := by
  classical
  have hInf :
      (⨅ μ : roots256, Ideal.span ({quad (μ : K)} : Set R)) =
        Ideal.span {∏ μ : roots256, quad (μ : K)} := by
    refine Ideal.iInf_span_singleton ?_
    intro μ ν hμν
    have hab : (μ : K) ≠ (ν : K) := by
      intro h
      apply hμν
      ext
      exact h
    exact isCoprime_quad hab
  have hGenAttach : (∏ μ ∈ roots256.attach, quad (μ : K)) = (X ^ (256 : Nat) + 1 : R) := by
    calc
      (∏ μ ∈ roots256.attach, quad (μ : K)) = ∏ μ ∈ roots256, quad μ := by
        simpa using (Finset.prod_attach (s := roots256) (f := fun μ : K => quad μ))
      _ = (X ^ (256 : Nat) + 1 : R) := modulusPoly_factorization.symm
  have hInf' :
      (⨅ μ : roots256, Ideal.span ({quad (μ : K)} : Set R)) =
        Ideal.span ({(X ^ (256 : Nat) + 1 : R)} : Set R) := by
    simpa [hGenAttach] using hInf
  simpa [quadIdeal] using hInf'.symm

noncomputable abbrev Rq : Type :=
  R ⧸ Ideal.span ({(X ^ (256 : Nat) + 1 : R)} : Set R)

noncomputable abbrev NTTDomain : Type :=
  ∀ μ : roots256, R ⧸ quadIdeal (μ : K)

noncomputable def nttEquiv : Rq ≃+* NTTDomain := by
  classical
  let f : roots256 → Ideal R :=
    fun μ => quadIdeal (μ : K)
  have hf : Pairwise (IsCoprime on f) := by
    simpa [f] using pairwise_coprime_quadIdeals
  have hEq : (Ideal.span ({(X ^ (256 : Nat) + 1 : R)} : Set R)) = ⨅ μ, f μ := by
    simpa [f] using modulusIdeal_eq_iInf_quadIdeal
  exact (Ideal.quotEquivOfEq hEq).trans (Ideal.quotientInfRingEquivPiQuotient f hf)

noncomputable def NTT : Rq →+* NTTDomain :=
  nttEquiv.toRingHom

noncomputable def invNTT : NTTDomain →+* Rq :=
  nttEquiv.symm.toRingHom

theorem invNTT_NTT (x : Rq) : invNTT (NTT x) = x := by
  simp [NTT, invNTT]

theorem invNTT_mul (x y : Rq) : invNTT (NTT x * NTT y) = x * y := by
  have h := congrArg nttEquiv.symm (nttEquiv.map_mul x y)
  have h' : nttEquiv.symm (nttEquiv x * nttEquiv y) = x * y :=
    h.symm.trans (nttEquiv.symm_apply_apply (x * y))
  dsimp [NTT, invNTT]
  exact h'

end NTTCorrectness
end Lattice
end Crypto
end HeytingLean
