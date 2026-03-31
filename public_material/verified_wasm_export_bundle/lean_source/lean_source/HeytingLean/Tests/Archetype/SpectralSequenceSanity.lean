import HeytingLean.Algebra.SpectralSequence.README

def trivialDifferentialComplex : HeytingLean.Algebra.SpectralSequence.DifferentialComplex where
  E := fun _ => Nat
  zero := fun _ => 0
  d := fun _ _ => 0
  d_zero := by intro n; rfl
  d_squared := by intro n x; rfl

example (n : Nat) :
    HeytingLean.Algebra.SpectralSequence.IsCycle trivialDifferentialComplex n
      (trivialDifferentialComplex.d (n + 1) (trivialDifferentialComplex.zero (n + 2))) := by
  exact
    HeytingLean.Algebra.SpectralSequence.boundary_is_cycle trivialDifferentialComplex n
      ⟨trivialDifferentialComplex.zero (n + 2), rfl⟩
