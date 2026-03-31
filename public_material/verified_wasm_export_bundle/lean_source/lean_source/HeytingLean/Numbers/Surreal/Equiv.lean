import HeytingLean.Numbers.SurrealCore

namespace HeytingLean
namespace Numbers
namespace Surreal

open HeytingLean.Numbers.SurrealCore

/-- Canonical equivalence: two pre-games are equivalent when their canonical forms agree. -/
def approx (x y : PreGame) : Prop :=
  canonicalize x = canonicalize y

@[simp] theorem approx_iff (x y : PreGame) :
    approx x y <-> canonicalize x = canonicalize y := Iff.rfl

@[simp] theorem approx_refl (x : PreGame) : approx x x := by
  unfold approx
  simp

theorem approx_symm {x y : PreGame} : approx x y -> approx y x := by
  intro h
  unfold approx at *
  simpa using h.symm

theorem approx_trans {x y z : PreGame} :
    approx x y -> approx y z -> approx x z := by
  intro hxy hyz
  unfold approx at *
  simpa [hxy] using hyz

/-- Setoid for canonical equivalence. -/
def approxSetoid : Setoid PreGame where
  r := approx
  iseqv := by
    refine { refl := ?refl, symm := ?symm, trans := ?trans }
    case refl =>
      intro x
      exact approx_refl x
    case symm =>
      intro x y
      exact approx_symm
    case trans =>
      intro x y z
      exact approx_trans

/-- Surreal quotient by canonical equivalence (auxiliary quotient type). -/
abbrev SurrealQ := Quotient approxSetoid

/-- Canonicalization descends to the quotient. -/
noncomputable def canonicalizeQ (x : SurrealQ) : SurrealQ :=
  Quotient.liftOn x
    (fun g => Quotient.mk (s := approxSetoid) (canonicalize g))
    (by
      intro a b hab
      change approx a b at hab
      apply Quot.sound
      change approx (canonicalize a) (canonicalize b)
      unfold approx at hab ⊢
      simpa [canonicalize_idem] using congrArg canonicalize hab)

@[simp] theorem canonicalizeQ_eq (x : SurrealQ) :
    canonicalizeQ (canonicalizeQ x) = canonicalizeQ x := by
  refine Quotient.inductionOn x ?_
  intro a
  change Quotient.mk (s := approxSetoid) (canonicalize (canonicalize a)) =
    Quotient.mk (s := approxSetoid) (canonicalize a)
  apply Quot.sound
  change canonicalize (canonicalize (canonicalize a)) = canonicalize (canonicalize a)
  simp [canonicalize_idem]

@[simp] theorem canonicalizeQ_idem (x : SurrealQ) :
    canonicalizeQ (canonicalizeQ x) = canonicalizeQ x := by
  exact canonicalizeQ_eq x

@[simp] theorem canonicalizeQ_mk (g : PreGame) :
    canonicalizeQ (Quotient.mk (s := approxSetoid) g) =
      Quotient.mk (s := approxSetoid) (canonicalize g) := by
  rfl

/-! ## Uniqueness of canonical forms -/

/-- If two pre-games are already canonical and equivalent under `approx`, then they are equal. -/
theorem approx_unique_of_canonical {x y : PreGame}
    (hx : canonicalize x = x) (hy : canonicalize y = y)
    (hxy : approx x y) : x = y := by
  unfold approx at hxy
  simpa [hx, hy] using hxy

end Surreal
end Numbers
end HeytingLean
