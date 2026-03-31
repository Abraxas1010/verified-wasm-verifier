namespace HeytingLean
namespace Algebra
namespace SpectralSequence

universe u

/-- A graded differential complex indexed by `Nat`. -/
structure DifferentialComplex where
  E : Nat → Type u
  zero : ∀ n, E n
  d : ∀ n, E (n + 1) → E n
  d_zero : ∀ n, d n (zero (n + 1)) = zero n
  d_squared : ∀ n (x : E (n + 2)), d n (d (n + 1) x) = zero n

def IsCycle (C : DifferentialComplex) (n : Nat) (x : C.E (n + 1)) : Prop :=
  C.d n x = C.zero n

def IsBoundary (C : DifferentialComplex) (n : Nat) (x : C.E (n + 1)) : Prop :=
  ∃ y : C.E (n + 2), C.d (n + 1) y = x

theorem boundary_is_cycle (C : DifferentialComplex) (n : Nat) {x : C.E (n + 1)}
    (hx : IsBoundary C n x) :
    IsCycle C n x := by
  rcases hx with ⟨y, rfl⟩
  exact C.d_squared n y

def filtrationLevel (level : Nat → Nat) (n : Nat) : Nat := level n

theorem filtrationLevel_eval (level : Nat → Nat) (n : Nat) :
    filtrationLevel level n = level n := rfl

end SpectralSequence
end Algebra
end HeytingLean
