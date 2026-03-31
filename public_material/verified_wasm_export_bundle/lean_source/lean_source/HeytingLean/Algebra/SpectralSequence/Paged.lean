import HeytingLean.Algebra.SpectralSequence.Basic

namespace HeytingLean
namespace Algebra
namespace SpectralSequence

universe u

/-- A differential complex indexed by page and degree. -/
structure PagedComplex where
  E : Nat → Nat → Type u
  zero : ∀ r n, E r n
  d : ∀ r n, E r (n + 1) → E r n
  d_zero : ∀ r n, d r n (zero r (n + 1)) = zero r n
  d_squared : ∀ r n (x : E r (n + 2)), d r n (d r (n + 1) x) = zero r n

/-- Convergence at page `r₀`: all later-page differentials are zero maps. -/
def PageConverges (PC : PagedComplex) (r₀ : Nat) : Prop :=
  ∀ r n, r₀ ≤ r → ∀ x : PC.E r (n + 1), PC.d r n x = PC.zero r n

/-- Promote a differential complex to a constant-in-page paged complex. -/
def DifferentialComplex.toConstantPaged (C : DifferentialComplex) : PagedComplex where
  E := fun _ n => C.E n
  zero := fun _ n => C.zero n
  d := fun _ n => C.d n
  d_zero := fun _ n => C.d_zero n
  d_squared := fun _ n => C.d_squared n

/-- Convergence of a constant paged complex is exactly vanishing differential. -/
theorem constantPaged_converges_iff_d_zero (C : DifferentialComplex) :
    PageConverges (C.toConstantPaged) 0 ↔
      ∀ n (x : C.E (n + 1)), C.d n x = C.zero n := by
  constructor
  · intro h
    intro n x
    simpa [DifferentialComplex.toConstantPaged, PageConverges] using h 0 n (Nat.zero_le 0) x
  · intro h
    intro r n hr x
    simpa [DifferentialComplex.toConstantPaged, PageConverges] using h n x

/-- If the differential is identically zero in a constant-page model, convergence follows. -/
theorem degeneration_from_zero_differential (C : DifferentialComplex)
    (r₀ : Nat) (h : ∀ n (x : C.E (n + 1)), C.d n x = C.zero n) :
    PageConverges (C.toConstantPaged) r₀ := by
  intro r n hr x
  simpa [DifferentialComplex.toConstantPaged] using h n x

end SpectralSequence
end Algebra
end HeytingLean
