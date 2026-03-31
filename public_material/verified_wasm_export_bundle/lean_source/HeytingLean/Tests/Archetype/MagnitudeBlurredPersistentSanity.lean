import HeytingLean.Metrics.Magnitude.BlurredPersistent

namespace HeytingLean
namespace Tests
namespace Archetype

open Metrics.Magnitude

private instance boolUnitMetricSpaceBlurred : MetricMagnitudeSpace Bool where
  toFintype := inferInstance
  decEq := inferInstance
  dist := fun x y => if x = y then 0 else 1
  dist_self := by
    intro x
    simp
  dist_symm := by
    intro x y
    by_cases hxy : x = y
    · simp [hxy]
    · simp [hxy, eq_comm]

example (n t : Nat) :
    blurredInclusion (α := Bool) n (Nat.le_refl t) = id := by
  exact blurredInclusion_refl (α := Bool) n t

example {n : Nat} (f : MagnitudeChain Bool (n + 2) → ℤ)
    (τ : BlurredChain (α := Bool) n 10) :
    blurredDifferentialRaw (α := Bool) n 10 (magnitudeDifferential (n + 1) f) τ = 0 := by
  exact blurredDifferentialRaw_squared (α := Bool) n 10 f τ

example (n t : Nat)
    (f : BlurredChain (α := Bool) (n + 2) t → ℤ)
    (hzero :
      ZeroAbove (α := Bool) (n := n + 1) t
        (magnitudeDifferential (n + 1)
          (extendBlurred (α := Bool) (n := n + 2) (t := t) f)))
    (τ : BlurredChain (α := Bool) n t) :
    blurredDifferential (α := Bool) n t
      (blurredDifferential (α := Bool) (n + 1) t f) τ = 0 := by
  exact blurredDifferential_squared (α := Bool) n t f hzero τ

def boolChain01 : MagnitudeChain Bool 1 :=
  ⟨fun i => if i.1 = 0 then true else false, by
    intro i
    have hi : (i : Nat) = 0 := Nat.lt_one_iff.mp i.is_lt
    simp⟩

def boolVR01 : VRChain (α := Bool) 1 1 :=
  ⟨boolChain01, by
    intro i j
    change (if (boolChain01.1 i) = (boolChain01.1 j) then 0 else 1) ≤ 1
    by_cases hij : (boolChain01.1 i) = (boolChain01.1 j) <;> simp [hij]⟩

example : chainLength (vrToBlurredScaled (α := Bool) 1 1 boolVR01).1 ≤ 1 := by
  exact (vrToBlurredScaled (α := Bool) 1 1 boolVR01).2

example (t : Nat) :
    Nonempty (BlurredChain (α := Bool) 1 t ≃ VRChain (α := Bool) 1 t) := by
  exact ⟨blurred_eq_vr_l1_degreeOne (α := Bool) t⟩

def boolLp11 : LPChain (α := Bool) 1 1 1 := by
  simpa using (vrToLpScaled (α := Bool) 1 1 1 boolVR01)

example :
    chainLength ((lpChain_one_equiv_blurred (α := Bool) 1 1 boolLp11).1) ≤ 1 := by
  simpa using ((lpChain_one_equiv_blurred (α := Bool) 1 1 boolLp11).2)

example (t : Nat) :
    Nonempty (VRChain (α := Bool) 1 t ≃ LInfPairChain (α := Bool) 1 t) := by
  exact ⟨vrEquivLInfPairChain (α := Bool) 1 t⟩

example : LInfConsecutiveChain (α := Bool) 1 1 := by
  exact vrToLInfConsecutive (α := Bool) 1 1 boolVR01

example (n s t : Nat) (hst : s ≤ t)
    (f : BlurredChain (α := Bool) (n + 1) t → ℤ)
    (hvanish : VanishesAbove (α := Bool) (n := n + 1) s t f) :
    blurredRestrict (α := Bool) n hst (blurredDifferential (α := Bool) n t f) =
      blurredDifferential (α := Bool) n s
        (blurredRestrict (α := Bool) (n + 1) hst f) := by
  exact blurred_persistence_commutes (α := Bool) n hst f hvanish

example (n s t : Nat)
    (f : BlurredChain (α := Bool) n t → ℤ)
    (hvanish : VanishesAbove (α := Bool) n s t f) :
    ZeroAbove (α := Bool) n s (extendBlurred (α := Bool) (n := n) (t := t) f) := by
  exact zeroAbove_extendBlurred_of_vanishesAbove (α := Bool) n s t f hvanish

example (n s t : Nat) (f : BlurredChain (α := Bool) n t → ℤ) :
    VanishesAbove (α := Bool) n s t f ↔
      ZeroAbove (α := Bool) n s (extendBlurred (α := Bool) (n := n) (t := t) f) := by
  exact vanishesAbove_iff_zeroAbove_extendBlurred (α := Bool) n s t f

end Archetype
end Tests
end HeytingLean
