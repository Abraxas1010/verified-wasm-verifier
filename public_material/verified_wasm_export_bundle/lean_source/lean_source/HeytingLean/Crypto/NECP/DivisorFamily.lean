import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Order
import HeytingLean.Crypto.NECP.PrincipalNucleus
import HeytingLean.Crypto.NECP.DivisorArithmetic

open scoped BigOperators

namespace HeytingLean
namespace Crypto
namespace NECP
namespace DivisorFamily

universe u

section Family

variable {ι : Type u} [DecidableEq ι] {bounds : ι → Nat}

/-- A finite ambient divisor family records the visible prime exponents, each with its own bound. -/
abbrev ExponentFamily (bounds : ι → Nat) := ∀ i, Fin (bounds i + 1)

/-- NECP smooth-part nuclei are inflationary only in the dual divisibility order. -/
abbrev DualExponentFamily (bounds : ι → Nat) := OrderDual (ExponentFamily bounds)

/-- Zero out all coordinates outside the currently visible basis. -/
def keepBasis (basis : Finset ι) (e : ExponentFamily bounds) : ExponentFamily bounds :=
  fun i => if i ∈ basis then e i else 0

@[simp] theorem keepBasis_apply (basis : Finset ι) (e : ExponentFamily bounds) (i : ι) :
    keepBasis basis e i = if i ∈ basis then e i else 0 :=
  by simp [keepBasis]

theorem keepBasis_le (basis : Finset ι) (e : ExponentFamily bounds) :
    keepBasis basis e ≤ e := by
  intro i
  by_cases hi : i ∈ basis
  · simp [keepBasis, hi]
  · simp [keepBasis, hi]

theorem keepBasis_idempotent (basis : Finset ι) (e : ExponentFamily bounds) :
    keepBasis basis (keepBasis basis e) = keepBasis basis e := by
  funext i
  by_cases hi : i ∈ basis <;> simp [keepBasis, hi]

theorem keepBasis_sup (basis : Finset ι) (e₁ e₂ : ExponentFamily bounds) :
    keepBasis basis (e₁ ⊔ e₂) = keepBasis basis e₁ ⊔ keepBasis basis e₂ := by
  funext i
  by_cases hi : i ∈ basis <;> simp [keepBasis, hi]

/-- Pointwise smooth-part map on the dual divisor family. -/
def smoothPart (basis : Finset ι) (e : DualExponentFamily bounds) : DualExponentFamily bounds :=
  keepBasis basis e

/-- The smooth-part operator is a genuine nucleus on the dual finite divisor carrier. -/
noncomputable def smoothPartNucleus (basis : Finset ι) :
    NuclearFrame (DualExponentFamily bounds) where
  toFun := smoothPart basis
  map_inf' x y := by
    show keepBasis basis (x ⊔ y) = keepBasis basis x ⊔ keepBasis basis y
    exact keepBasis_sup basis x y
  idempotent' x := by
    exact le_of_eq (by
      show smoothPart basis (smoothPart basis x) = smoothPart basis x
      exact keepBasis_idempotent basis x)
  le_apply' x := by
    intro i
    by_cases hi : i ∈ basis
    · simp [smoothPart, keepBasis, hi]
    · simp [smoothPart, keepBasis, hi]

@[simp] theorem smoothPartNucleus_apply (basis : Finset ι) (e : DualExponentFamily bounds) :
    smoothPartNucleus basis e = smoothPart basis e :=
  rfl

/-- Coordinates outside the visible basis are exactly the fixed-point obstruction. -/
theorem smoothPartNucleus_fixed_iff (basis : Finset ι) (e : DualExponentFamily bounds) :
    smoothPartNucleus basis e = e ↔ ∀ i, i ∉ basis → e i = 0 := by
  constructor
  · intro h i hi
    have hcoord := congrFun h i
    simp [smoothPartNucleus, smoothPart, keepBasis, hi] at hcoord
    exact hcoord.symm
  · intro h
    funext i
    by_cases hi : i ∈ basis
    · simp [smoothPartNucleus, smoothPart, keepBasis, hi]
    · simp [smoothPartNucleus, smoothPart, keepBasis, hi, h i hi]

/-- Adding one more visible prime is the coordinatewise merge of the old smooth-part and the
singleton smooth-part. -/
theorem keepBasis_insert_sup (basis : Finset ι) (i : ι) (e : ExponentFamily bounds) :
    keepBasis (insert i basis) e = keepBasis basis e ⊔ keepBasis ({i} : Finset ι) e := by
  funext j
  by_cases hj : j = i
  · subst hj
    by_cases hmem : j ∈ basis
    · simp [keepBasis, hmem]
    · have hzero : (0 : Fin (bounds j + 1)) ≤ e j := by simp
      simp [keepBasis, hmem]
  · by_cases hmem : j ∈ basis
    · simp [keepBasis, hmem, Finset.mem_singleton, hj]
    · simp [keepBasis, hmem, Finset.mem_singleton, hj]

/-- Carrier-accurate basis evolution law on the current dual exponent-family surface.
Because the frame order is dualized, adjoining one coordinate is evaluated pointwise as the
coordinatewise join of the prior smooth part and the singleton-coordinate smooth part. -/
@[simp] theorem basisEvolution_smoothPart_apply (basis : Finset ι) (i : ι)
    (e : DualExponentFamily bounds) :
    smoothPartNucleus (bounds := bounds) (insert i basis) e =
      keepBasis basis e ⊔ keepBasis ({i} : Finset ι) e := by
  simpa [smoothPartNucleus, smoothPart] using
    keepBasis_insert_sup (bounds := bounds) basis i e

/-- Evaluate a finite divisor family back to a natural number along a chosen ambient prime list. -/
def evalNat [Fintype ι] (primes : ι → Nat) (e : ExponentFamily bounds) : Nat :=
  ∏ i, primes i ^ (e i : Nat)

end Family

section ArithmeticBridge

variable {ι : Type u} {bounds : ι → Nat}
variable [DecidableEq ι] [Fintype ι]

/-- Finset-restricted evaluation surface for arithmetic bridge theorems. -/
def evalNatOn (s : Finset ι) (primes : ι → Nat) (e : ExponentFamily bounds) : Nat :=
  ∏ i ∈ s, primes i ^ (e i : Nat)

@[simp] theorem evalNatOn_empty (primes : ι → Nat) (e : ExponentFamily bounds) :
    evalNatOn (bounds := bounds) ∅ primes e = 1 := by
  simp [evalNatOn]

@[simp] theorem evalNatOn_insert (s : Finset ι) (i : ι) (hi : i ∉ s)
    (primes : ι → Nat) (e : ExponentFamily bounds) :
    evalNatOn (bounds := bounds) (insert i s) primes e =
      primes i ^ (e i : Nat) * evalNatOn (bounds := bounds) s primes e := by
  simpa [evalNatOn] using
    (Finset.prod_insert (s := s) (a := i) (f := fun j => primes j ^ (e j : Nat)) hi)

@[simp] theorem evalNatOn_univ (primes : ι → Nat) (e : ExponentFamily bounds) :
    evalNatOn (bounds := bounds) Finset.univ primes e = evalNat primes e := by
  simp [evalNatOn, evalNat]

theorem evalNat_keepBasis (basis : Finset ι) (primes : ι → Nat) (e : ExponentFamily bounds) :
    evalNat primes (keepBasis basis e) = evalNatOn (bounds := bounds) basis primes e := by
  classical
  calc
    evalNat primes (keepBasis basis e)
        = ∏ i, (if i ∈ basis then primes i ^ (e i : Nat) else 1) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            by_cases hmem : i ∈ basis <;> simp [evalNat, keepBasis, hmem]
    _ = ∏ i ∈ Finset.univ.filter (fun i => i ∈ basis), primes i ^ (e i : Nat) := by
          rw [← Finset.prod_filter]
    _ = evalNatOn (bounds := bounds) basis primes e := by
          simp [evalNatOn]

theorem padicVal_evalNatOn_prime (primes : ι → Nat)
    (hprime : ∀ i, Nat.Prime (primes i))
    (hinj : Function.Injective primes)
    (s : Finset ι) (e : ExponentFamily bounds) (q : Nat) (hq : q.Prime) :
    padicValNat q (evalNatOn (bounds := bounds) s primes e) =
      ∑ i ∈ s, if q = primes i then (e i : Nat) else 0 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  induction s using Finset.induction_on with
  | empty =>
      simp [evalNatOn]
  | @insert i s hi hs =>
      rw [evalNatOn_insert (bounds := bounds) s i hi primes e]
      have hpow_ne_zero : primes i ^ (e i : Nat) ≠ 0 := by
        exact pow_ne_zero _ (Nat.Prime.ne_zero (hprime i))
      have hrest_ne_zero : evalNatOn (bounds := bounds) s primes e ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr ?_
        intro j hj
        exact pow_ne_zero _ (Nat.Prime.ne_zero (hprime j))
      rw [padicValNat.mul hpow_ne_zero hrest_ne_zero, hs]
      by_cases hqi : q = primes i
      · have hpow_self : padicValNat q (primes i ^ (e i : Nat)) = (e i : Nat) := by
          subst hqi
          simpa using (padicValNat.prime_pow (p := primes i) (n := (e i : Nat)))
        have hnot : ∀ j ∈ s, q ≠ primes j := by
          intro j hj hEq
          have hji : j = i := hinj (hEq.symm.trans hqi)
          exact hi (hji ▸ hj)
        rw [hpow_self]
        simp [hnot, hi, hqi]
      · have hpow_zero : padicValNat q (primes i ^ (e i : Nat)) = 0 := by
          haveI : Fact (primes i).Prime := ⟨hprime i⟩
          simpa [hqi] using padicValNat_prime_prime_pow (p := q) (q := primes i) (e i : Nat) hqi
        simp [hpow_zero, hqi, hi]

theorem smoothPart_evalNat (basis : Finset ι) (primes : ι → Nat)
    (hprime : ∀ i, Nat.Prime (primes i))
    (hinj : Function.Injective primes)
    (e : ExponentFamily bounds) :
    DivisorArithmetic.smoothPart (basis.image primes) (evalNat primes e) =
      evalNat primes (keepBasis basis e) := by
  classical
  have hEvalNeZero : evalNat primes e ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    exact pow_ne_zero _ (Nat.Prime.ne_zero (hprime i))
  rw [evalNat_keepBasis (bounds := bounds) basis primes e]
  apply (Nat.eq_iff_prime_padicValNat_eq
    (DivisorArithmetic.smoothPart (basis.image primes) (evalNat primes e))
    (evalNatOn (bounds := bounds) basis primes e)
    (DivisorArithmetic.smoothPart_ne_zero _ _)
    (by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro i hi
      exact pow_ne_zero _ (Nat.Prime.ne_zero (hprime i)))).2
  intro q hq
  rw [DivisorArithmetic.smoothPart_padicVal _ _ _ hq,
    ← evalNatOn_univ (bounds := bounds) primes e,
    padicVal_evalNatOn_prime (bounds := bounds) primes hprime hinj basis e q hq,
    padicVal_evalNatOn_prime (bounds := bounds) primes hprime hinj Finset.univ e q hq]
  by_cases hmem : q ∈ basis.image primes
  · rcases Finset.mem_image.mp hmem with ⟨i, hiBasis, hqi⟩
    have hsumBasis :
        (∑ j ∈ basis, if q = primes j then (e j : Nat) else 0) = (e i : Nat) := by
      have hnot : ∀ j ∈ basis, j ≠ i → q ≠ primes j := by
        intro j hj hji hEq
        exact hji (hinj (hEq.symm.trans hqi.symm))
      rw [Finset.sum_eq_single_of_mem i hiBasis]
      · simp [hqi]
      · intro j hj hji
        simp [hnot j hj hji]
    have hsumUniv :
        (∑ j ∈ Finset.univ, if q = primes j then (e j : Nat) else 0) = (e i : Nat) := by
      have hnot : ∀ j ∈ Finset.univ, j ≠ i → q ≠ primes j := by
        intro j hj hji hEq
        exact hji (hinj (hEq.symm.trans hqi.symm))
      rw [Finset.sum_eq_single_of_mem i (by simp)]
      · simp [hqi]
      · intro j hj hji
        simp [hnot j hj hji]
    simp [hmem, hsumBasis, hsumUniv]
  · have hsumBasis :
      (∑ j ∈ basis, if q = primes j then (e j : Nat) else 0) = 0 := by
        exact Finset.sum_eq_zero (fun j hj => by
          have : q ≠ primes j := by
            intro hEq
            apply hmem
            exact Finset.mem_image.mpr ⟨j, hj, hEq.symm⟩
          simp [this])
    simp [hmem, hsumBasis]

end ArithmeticBridge

section WorkedExample

def workedPrimes : Fin 6 → Nat
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 5
  | ⟨3, _⟩ => 7
  | ⟨4, _⟩ => 11
  | ⟨5, _⟩ => 31

def workedBounds : Fin 6 → Nat
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 1

def workedExponents : ExponentFamily workedBounds
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => 1

def workedBasis : Finset (Fin 6) :=
  Finset.univ.filter fun i => i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 ∨ i.1 = 4

def worked31 : Fin 6 := ⟨5, by decide⟩

/-- Ambient support includes the hidden primes `7` and `31`, so the published smooth-part on
Vladimir's visible basis is trivial. -/
example : evalNat workedPrimes workedExponents = 1519 := by
  native_decide

example : evalNat workedPrimes (smoothPart workedBasis workedExponents) = 1 := by
  native_decide

example :
    evalNat workedPrimes (smoothPart (insert worked31 workedBasis) workedExponents) = 31 := by
  native_decide

example :
    keepBasis (insert worked31 workedBasis) workedExponents =
      keepBasis workedBasis workedExponents ⊔
        keepBasis ({worked31} : Finset (Fin 6)) workedExponents := by
  simpa using keepBasis_insert_sup (bounds := workedBounds) workedBasis worked31 workedExponents

end WorkedExample

end DivisorFamily
end NECP
end Crypto
end HeytingLean
