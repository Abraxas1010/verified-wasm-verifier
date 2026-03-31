import HeytingLean.IteratedVirtual.BendingEnergy

/-!
# IteratedVirtual.BendingEnergyMinimization

Phase‑8 (research-scale) follow-on for `BendingEnergy.lean`:

We add a **constrained minimization** statement for the discrete bending energy

`E(p, N) = ∑_{k < N} ‖Δ² p(k)‖²`.

Rather than invoking continuous variational calculus, we use a strict-only discrete argument:

- `E(p,N) ≥ 0` always.
- There is a canonical **affine extension** determined by the first two points `p 0` and `p 1`
  with `Δ²=0`, hence energy `0`.
- Any other curve with energy `0` and the same first two points must agree with this affine extension
  on the prefix (uniqueness of the minimizer under these boundary constraints).
-/

namespace HeytingLean
namespace IteratedVirtual

section Algebra

variable {V : Type} [AddCommGroup V]

/-- The affine extension determined by two boundary values `a = p 0` and `b = p 1`. -/
def affineFrom01 (a b : V) : Nat → V :=
  fun k => a + k • (b - a)

@[simp] theorem affineFrom01_zero (a b : V) : affineFrom01 (V := V) a b 0 = a := by
  simp [affineFrom01]

@[simp] theorem affineFrom01_one (a b : V) : affineFrom01 (V := V) a b 1 = b := by
  simp [affineFrom01]

@[simp] theorem firstDiff_affineFrom01 (a b : V) (k : Nat) :
    firstDiff (affineFrom01 (V := V) a b) k = (b - a) := by
  -- `(a + (k+1)•d) - (a + k•d) = d`
  simp [firstDiff, affineFrom01, add_sub_add_left_eq_sub, succ_nsmul]

@[simp] theorem secondDiff_affineFrom01 (a b : V) (k : Nat) :
    secondDiff (affineFrom01 (V := V) a b) k = 0 := by
  have hleft : firstDiff (affineFrom01 (V := V) a b) (k + 1) - firstDiff (affineFrom01 (V := V) a b) k = 0 := by
    calc
      firstDiff (affineFrom01 (V := V) a b) (k + 1) - firstDiff (affineFrom01 (V := V) a b) k =
          (b - a) - (b - a) := by simp
      _ = 0 := sub_self _
  have hA :
      firstDiff (affineFrom01 (V := V) a b) (k + 1) - firstDiff (affineFrom01 (V := V) a b) k =
        secondDiff (affineFrom01 (V := V) a b) k :=
    firstDiff_sub_firstDiff (p := affineFrom01 (V := V) a b) (k := k)
  exact Eq.trans (Eq.symm hA) hleft

end Algebra

section Energy

variable {V : Type} [NormedAddCommGroup V]

theorem bendingEnergy_affineFrom01_eq_zero (a b : V) (N : Nat) :
    bendingEnergy (affineFrom01 (V := V) a b) N = 0 := by
  apply (bendingEnergy_eq_zero_iff_secondDiff_eq_zero (p := affineFrom01 (V := V) a b) (N := N)).2
  intro k hk
  simp [secondDiff_affineFrom01 (V := V) (a := a) (b := b) (k := k)]

/-!
## Minimization with boundary constraints

We treat “boundary constraints” as specifying `p 0 = a` and `p 1 = b`.
Under these constraints, the unique minimizer is the affine extension `affineFrom01 a b`.
-/

theorem bendingEnergy_minimizer_affineFrom01 (a b : V) (N : Nat) (p : Nat → V)
    (h0 : p 0 = a) (h1 : p 1 = b) :
    bendingEnergy (affineFrom01 (V := V) a b) N ≤ bendingEnergy p N := by
  -- The affine extension has energy `0`, and bending energy is always nonnegative.
  subst a
  subst b
  simpa [bendingEnergy_affineFrom01_eq_zero (V := V) (a := p 0) (b := p 1) (N := N)] using
    (bendingEnergy_nonneg (p := p) (N := N))

theorem eq_affineFrom01_of_bendingEnergy_eq_zero_and_boundary (a b : V) (N : Nat) (p : Nat → V)
    (h0 : p 0 = a) (h1 : p 1 = b) (hE : bendingEnergy p N = 0) :
    ∀ k : Nat, k ≤ N + 1 → p k = affineFrom01 (V := V) a b k := by
  intro k hk
  have haff :=
    affine_on_prefix_of_bendingEnergy_eq_zero (p := p) (N := N) hE k hk
  have hfd : firstDiff p 0 = (b - a) := by
    simp [firstDiff, h0, h1]
  simpa [affineFrom01, h0, hfd] using haff

theorem bendingEnergy_minimizer_unique (a b : V) (N : Nat) (p : Nat → V)
    (h0 : p 0 = a) (h1 : p 1 = b)
    (hmin : bendingEnergy p N ≤ bendingEnergy (affineFrom01 (V := V) a b) N) :
    ∀ k : Nat, k ≤ N + 1 → p k = affineFrom01 (V := V) a b k := by
  have hle0 : bendingEnergy p N ≤ 0 := by
    simpa [bendingEnergy_affineFrom01_eq_zero (V := V) (a := a) (b := b) (N := N)] using hmin
  have hE0 : bendingEnergy p N = 0 :=
    le_antisymm hle0 (bendingEnergy_nonneg (p := p) (N := N))
  exact eq_affineFrom01_of_bendingEnergy_eq_zero_and_boundary (V := V) a b N p h0 h1 hE0

end Energy

end IteratedVirtual
end HeytingLean
