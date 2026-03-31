import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

open scoped BigOperators

namespace HeytingLean
namespace Crypto
namespace NECP
namespace DivisorArithmetic

/-- The full `p`-primary contribution of `n`, extracted via its `p`-adic valuation. -/
def smoothPrimePower (p n : Nat) : Nat :=
  p ^ padicValNat p n

/-- Finite-basis smooth part of `n`: only the primes listed in `basis` are retained. -/
def smoothPart (basis : Finset Nat) (n : Nat) : Nat :=
  ∏ p ∈ basis with Nat.Prime p, smoothPrimePower p n

/-- Covering range used to compare any finite basis with the canonical bounded prime support of `n`. -/
def cover (basis : Finset Nat) (n : Nat) : Nat :=
  max (n + 1) (basis.sup id + 1)

@[simp] theorem smoothPrimePower_apply (p n : Nat) :
    smoothPrimePower p n = p ^ padicValNat p n :=
  rfl

@[simp] theorem smoothPart_empty (n : Nat) :
    smoothPart ∅ n = 1 := by
  simp [smoothPart]

theorem smoothPrimePower_dvd (p n : Nat) :
    smoothPrimePower p n ∣ n := by
  simpa [smoothPrimePower] using pow_padicValNat_dvd (p := p) (n := n)

theorem mem_cover_filter (basis : Finset Nat) (n p : Nat)
    (hp : p ∈ basis.filter Nat.Prime) :
    p ∈ (Finset.range (cover basis n)).filter Nat.Prime := by
  rcases Finset.mem_filter.mp hp with ⟨hp_basis, hp_prime⟩
  refine Finset.mem_filter.mpr ?_
  refine ⟨?_, hp_prime⟩
  apply Finset.mem_range.mpr
  have hp_le : p ≤ basis.sup id := by
    simpa using (Finset.le_sup hp_basis : id p ≤ basis.sup id)
  have hp_lt : p < basis.sup id + 1 := Nat.lt_succ_of_le hp_le
  exact lt_of_lt_of_le hp_lt (Nat.le_max_right _ _)

theorem smoothPart_dvd (basis : Finset Nat) (n : Nat) :
    smoothPart basis n ∣ n := by
  by_cases hn : n = 0
  · subst hn
    simp [smoothPart]
  · have hsubset :
        basis.filter Nat.Prime ⊆ (Finset.range (cover basis n)).filter Nat.Prime := by
        intro p hp
        exact mem_cover_filter basis n p hp
    have hprod :
        smoothPart basis n ∣ smoothPart (Finset.range (cover basis n)) n := by
      exact Finset.prod_dvd_prod_of_subset
        (basis.filter Nat.Prime)
        ((Finset.range (cover basis n)).filter Nat.Prime)
        (fun p => smoothPrimePower p n)
        hsubset
    have hcover_gt : n < cover basis n := by
      exact lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_max_left _ _)
    have hfull : smoothPart (Finset.range (cover basis n)) n = n := by
      simpa [smoothPart, smoothPrimePower] using
        Nat.prod_pow_prime_padicValNat n hn (cover basis n) hcover_gt
    exact dvd_trans hprod (dvd_of_eq hfull)

theorem smoothPart_range_succ_eq_self {n : Nat} (hn : n ≠ 0) :
    smoothPart (Finset.range (n + 1)) n = n := by
  simpa [smoothPart, smoothPrimePower] using
    Nat.prod_pow_prime_padicValNat n hn (n + 1) (Nat.lt_succ_self n)

theorem smoothPrimePower_ne_zero {p n : Nat} (hp : p.Prime) :
    smoothPrimePower p n ≠ 0 := by
  simp [smoothPrimePower, hp.ne_zero]

theorem smoothPart_ne_zero (basis : Finset Nat) (n : Nat) :
    smoothPart basis n ≠ 0 := by
  classical
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro p hp
  exact smoothPrimePower_ne_zero (Finset.mem_filter.mp hp).2

theorem smoothPrimePower_factorization {p n : Nat} (hp : p.Prime) :
    (smoothPrimePower p n).factorization = Finsupp.single p (padicValNat p n) := by
  simpa [smoothPrimePower] using hp.factorization_pow (k := padicValNat p n)

theorem smoothPart_factorization (basis : Finset Nat) (n : Nat) :
    (smoothPart basis n).factorization =
      ∑ p ∈ basis.filter Nat.Prime, Finsupp.single p (padicValNat p n) := by
  classical
  rw [smoothPart, Nat.factorization_prod]
  · refine Finset.sum_congr rfl ?_
    intro p hp
    exact smoothPrimePower_factorization (Finset.mem_filter.mp hp).2
  · intro p hp
    exact smoothPrimePower_ne_zero (Finset.mem_filter.mp hp).2

theorem smoothPart_factorization_apply_prime (basis : Finset Nat) (n p : Nat) (hp : p.Prime) :
    (smoothPart basis n).factorization p = if p ∈ basis then padicValNat p n else 0 := by
  classical
  have happly := congrArg (fun f => f p) (smoothPart_factorization basis n)
  calc
    (smoothPart basis n).factorization p
        = ∑ c ∈ basis.filter Nat.Prime, (Finsupp.single c (padicValNat c n)) p := by
            simpa using happly
    _ = if p ∈ basis then padicValNat p n else 0 := by
      by_cases hmem : p ∈ basis
      · have hp_basis : p ∈ basis.filter Nat.Prime := Finset.mem_filter.mpr ⟨hmem, hp⟩
        have hsum :
            ∑ c ∈ basis.filter Nat.Prime, (Finsupp.single c (padicValNat c n)) p =
              (Finsupp.single p (padicValNat p n)) p := by
          exact Finset.sum_eq_single_of_mem p hp_basis (fun b hb hbne => by
            simp [Finsupp.single_eq_of_ne hbne.symm])
        simpa [hmem] using hsum
      · have hp_basis : p ∉ basis.filter Nat.Prime := by
          simp [hmem]
        have hsum :
            ∑ c ∈ basis.filter Nat.Prime, (Finsupp.single c (padicValNat c n)) p = 0 := by
          exact Finset.sum_eq_zero (fun i hi => by
            have hi_ne : i ≠ p := by
              intro hip
              apply hmem
              exact hip.symm ▸ (Finset.mem_filter.mp hi).1
            simp [Finsupp.single_eq_of_ne hi_ne.symm])
        simpa [hmem] using hsum

/-- On ordinary divisibility, `smoothPart` is deflationary. On the dual divisibility order,
this is the inflationary law used by the abstract nucleus formalization. -/
theorem smoothPart_deflationary (basis : Finset Nat) (n : Nat) :
    smoothPart basis n ∣ n :=
  smoothPart_dvd basis n

theorem smoothPart_padicVal (basis : Finset Nat) (n p : Nat) (hp : p.Prime) :
    padicValNat p (smoothPart basis n) = if p ∈ basis then padicValNat p n else 0 := by
  rw [← Nat.factorization_def (smoothPart basis n) hp]
  exact smoothPart_factorization_apply_prime basis n p hp

theorem padicValNat_gcd_eq_min {p a b : Nat} (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat p (Nat.gcd a b) = min (padicValNat p a) (padicValNat p b) := by
  rw [← Nat.factorization_def (Nat.gcd a b) hp, Nat.factorization_gcd ha hb]
  change min (a.factorization p) (b.factorization p) = min (padicValNat p a) (padicValNat p b)
  rw [Nat.factorization_def a hp, Nat.factorization_def b hp]

theorem smoothPart_idempotent (basis : Finset Nat) (n : Nat) :
    smoothPart basis (smoothPart basis n) = smoothPart basis n := by
  apply (Nat.eq_iff_prime_padicValNat_eq
    (smoothPart basis (smoothPart basis n))
    (smoothPart basis n)
    (smoothPart_ne_zero basis (smoothPart basis n))
    (smoothPart_ne_zero basis n)).2
  intro p hp
  rw [smoothPart_padicVal basis (smoothPart basis n) p hp,
    smoothPart_padicVal basis n p hp]
  by_cases hmem : p ∈ basis
  · have hinner := smoothPart_padicVal basis n p hp
    simp [hmem] at hinner
    simpa [hmem] using hinner
  · simp [hmem]

theorem smoothPart_gcd (basis : Finset Nat) {a b : Nat} (ha : a ≠ 0) (hb : b ≠ 0) :
    smoothPart basis (Nat.gcd a b) = Nat.gcd (smoothPart basis a) (smoothPart basis b) := by
  have hsa : smoothPart basis a ≠ 0 := smoothPart_ne_zero basis a
  have hsb : smoothPart basis b ≠ 0 := smoothPart_ne_zero basis b
  apply (Nat.eq_iff_prime_padicValNat_eq
    (smoothPart basis (Nat.gcd a b))
    (Nat.gcd (smoothPart basis a) (smoothPart basis b))
    (smoothPart_ne_zero basis (Nat.gcd a b))
    (Nat.gcd_ne_zero_left hsa)).2
  intro p hp
  rw [smoothPart_padicVal basis (Nat.gcd a b) p hp,
    padicValNat_gcd_eq_min hp hsa hsb,
    padicValNat_gcd_eq_min hp ha hb,
    smoothPart_padicVal basis a p hp,
    smoothPart_padicVal basis b p hp]
  by_cases hmem : p ∈ basis <;> simp [hmem]

@[simp] theorem smoothPart_singleton (p n : Nat) :
    smoothPart ({p} : Finset Nat) n = if p.Prime then smoothPrimePower p n else 1 := by
  by_cases hp : p.Prime
  · rw [smoothPart]
    have hfilter : ({p} : Finset Nat).filter Nat.Prime = ({p} : Finset Nat) := by
      simp [hp]
    rw [hfilter]
    rw [Finset.prod_singleton]
    simp [hp]
  · rw [smoothPart]
    have hfilter : ({p} : Finset Nat).filter Nat.Prime = (∅ : Finset Nat) := by
      simp [hp]
    rw [hfilter]
    simp [hp]

/-- Arithmetic basis evolution: adjoining one candidate prime is the join operation on plain
divisibility, namely the `lcm` of the old smooth part and the singleton smooth part. -/
theorem smoothPart_insert_lcm (basis : Finset Nat) (p n : Nat) :
    smoothPart (insert p basis) n =
      Nat.lcm (smoothPart basis n) (smoothPart ({p} : Finset Nat) n) := by
  have hBasis : smoothPart basis n ≠ 0 := smoothPart_ne_zero basis n
  have hSingle : smoothPart ({p} : Finset Nat) n ≠ 0 := smoothPart_ne_zero ({p} : Finset Nat) n
  apply (Nat.eq_iff_prime_padicValNat_eq
    (smoothPart (insert p basis) n)
    (Nat.lcm (smoothPart basis n) (smoothPart ({p} : Finset Nat) n))
    (smoothPart_ne_zero (insert p basis) n)
    (Nat.lcm_ne_zero hBasis hSingle)).2
  intro q hq
  rw [smoothPart_padicVal (insert p basis) n q hq,
    ← Nat.factorization_def (Nat.lcm (smoothPart basis n) (smoothPart ({p} : Finset Nat) n)) hq,
    Nat.factorization_lcm hBasis hSingle,
    Finsupp.sup_apply,
    smoothPart_factorization_apply_prime basis n q hq,
    smoothPart_factorization_apply_prime ({p} : Finset Nat) n q hq]
  by_cases hqp : q = p
  · subst hqp
    by_cases hqb : q ∈ basis <;> simp [hqb]
  · by_cases hqb : q ∈ basis <;> simp [hqb, hqp]

section WorkedExamples

example : smoothPart ({2, 3, 5, 11} : Finset Nat) 1519 = 1 := by
  native_decide

example : smoothPart ({2, 3, 5, 11, 31} : Finset Nat) 1519 = 31 := by
  native_decide

example : smoothPart ({2, 3, 5, 7, 11, 31} : Finset Nat) 1519 = 1519 := by
  native_decide

example : smoothPart ({2, 3, 11} : Finset Nat) 1518 = 66 := by
  native_decide

example : smoothPart ({2, 3, 11, 23} : Finset Nat) 1518 = 1518 := by
  native_decide

example :
    smoothPart (insert 31 ({2, 3, 5, 11} : Finset Nat)) 1519 =
      Nat.lcm (smoothPart ({2, 3, 5, 11} : Finset Nat) 1519)
        (smoothPart ({31} : Finset Nat) 1519) := by
  simpa using smoothPart_insert_lcm ({2, 3, 5, 11} : Finset Nat) 31 1519

end WorkedExamples

end DivisorArithmetic
end NECP
end Crypto
end HeytingLean
