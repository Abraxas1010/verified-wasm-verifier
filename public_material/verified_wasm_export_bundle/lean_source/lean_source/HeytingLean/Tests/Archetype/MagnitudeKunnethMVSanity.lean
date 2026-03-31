import HeytingLean.Metrics.Magnitude.KunnethMV

namespace HeytingLean
namespace Tests
namespace Archetype

open Metrics.Magnitude

example (n : Nat) (F : KunnethInput Bool (Fin 3) n)
    (x : ProductChain Bool (Fin 3) n) :
    ∃ f g : ℤ, kunnethMap (α := Bool) (β := Fin 3) n F x = f * g := by
  exact kunnethMap_mul n F x

example : bettiFromComplex (productComplexF2 boolMagnitudeComplexF2 fin3MagnitudeComplexF2 3) 0 =
    bettiConvolution boolMagnitudeComplexF2 fin3MagnitudeComplexF2 0 := by
  native_decide

example : bettiFromComplex (productComplexF2 boolMagnitudeComplexF2 fin3MagnitudeComplexF2 3) 1 =
    bettiConvolution boolMagnitudeComplexF2 fin3MagnitudeComplexF2 1 := by
  native_decide

example : bettiFromComplex (productComplexF2 boolMagnitudeComplexF2 fin3MagnitudeComplexF2 3) 2 =
    bettiConvolution boolMagnitudeComplexF2 fin3MagnitudeComplexF2 2 := by
  native_decide

example {γ : Type} [Fintype γ] [DecidableEq γ] (C : MagnitudeCover γ) (f : γ → ℤ) :
    mvConnecting C (diagonalPair C f) = 0 := by
  funext x
  simp [mvConnecting, diagonalPair, restrictU, restrictV]

example {γ : Type} [Fintype γ] [DecidableEq γ]
    (C : MagnitudeCover γ) (fg : (C.U → ℤ) × (C.V → ℤ))
    (hker : mvConnecting C fg = 0) :
    ∃ h : γ → ℤ, diagonalPair C h = fg := by
  exact mv_exact_at_direct_sum C fg hker

example {γ : Type} [Fintype γ] [DecidableEq γ] (n : Nat)
    (C : MagnitudeCover (MagnitudeChain γ n))
    (fg : (C.U → ℤ) × (C.V → ℤ))
    (hker : mvConnecting C fg = 0) :
    ∃ h : MagnitudeChain γ n → ℤ, diagonalPair C h = fg := by
  exact mv_exact_at_chain_degree n C fg hker

end Archetype
end Tests
end HeytingLean
