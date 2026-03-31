import HeytingLean.Numbers.Surreal.Equiv
import HeytingLean.Numbers.Surreal.BridgeToPGamePreservation

namespace HeytingLean
namespace Numbers
namespace Surreal

open HeytingLean.Numbers.SurrealCore

/-!
# Quotient-core semantic bridge for `SurrealQ`

This module provides a high-leverage transfer layer:
- a canonical `PreGame` representative for `SurrealQ`,
- a semantic projection `toIGameQ`,
- quotient operations defined directly from `SurrealCore` arithmetic, and
- lifted `toIGame` laws for those operations.

The intent is to make representative-level strengthening and transfinite integration
reuse a single semantic surface.
-/

/-- Canonical core representative for a quotient surreal. -/
noncomputable def coreRepr (x : SurrealQ) : PreGame :=
  Quotient.liftOn x canonicalize (by
    intro a b hab
    exact hab)

@[simp] theorem coreRepr_mk (g : PreGame) :
    coreRepr (Quotient.mk (s := approxSetoid) g) = canonicalize g := by
  rfl

/-- Semantic projection for quotient surreals via the canonical core representative. -/
noncomputable def toIGameQ (x : SurrealQ) : IGame :=
  SurrealCore.PreGame.toIGame (coreRepr x)

@[simp] theorem toIGameQ_mk (g : PreGame) :
    toIGameQ (Quotient.mk (s := approxSetoid) g) = SurrealCore.PreGame.toIGame (canonicalize g) := by
  rfl

/-- Quotient zero via structural core semantics. -/
noncomputable def zeroQCore : SurrealQ :=
  Quotient.mk (s := approxSetoid) (canonicalize SurrealCore.nullCut)

/-- Quotient addition via structural core semantics. -/
noncomputable def addQCore (x y : SurrealQ) : SurrealQ :=
  Quotient.mk (s := approxSetoid) (canonicalize (SurrealCore.add (coreRepr x) (coreRepr y)))

/-- Quotient negation via structural core semantics. -/
noncomputable def negQCore (x : SurrealQ) : SurrealQ :=
  Quotient.mk (s := approxSetoid) (canonicalize (SurrealCore.neg (coreRepr x)))

/-- Quotient multiplication via structural core semantics. -/
noncomputable def mulQCore (x y : SurrealQ) : SurrealQ :=
  Quotient.mk (s := approxSetoid) (canonicalize (SurrealCore.mul (coreRepr x) (coreRepr y)))

@[simp] theorem canonicalizeQ_zeroQCore :
    canonicalizeQ zeroQCore = zeroQCore := by
  simp [zeroQCore, canonicalizeQ, canonicalize_idem]

@[simp] theorem canonicalizeQ_addQCore (x y : SurrealQ) :
    canonicalizeQ (addQCore x y) = addQCore x y := by
  simp [addQCore, canonicalizeQ, canonicalize_idem]

@[simp] theorem canonicalizeQ_negQCore (x : SurrealQ) :
    canonicalizeQ (negQCore x) = negQCore x := by
  simp [negQCore, canonicalizeQ, canonicalize_idem]

@[simp] theorem canonicalizeQ_mulQCore (x y : SurrealQ) :
    canonicalizeQ (mulQCore x y) = mulQCore x y := by
  simp [mulQCore, canonicalizeQ, canonicalize_idem]

theorem toIGameQ_addQCore (x y : SurrealQ) :
    toIGameQ (addQCore x y) = toIGameQ x + toIGameQ y := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  simpa [addQCore, toIGameQ, coreRepr, canonicalize] using
    (SurrealCore.PreGame.toIGame_add (canonicalize a) (canonicalize b))

theorem toIGameQ_negQCore (x : SurrealQ) :
    toIGameQ (negQCore x) = -toIGameQ x := by
  refine Quotient.inductionOn x ?_
  intro a
  simpa [negQCore, toIGameQ, coreRepr, canonicalize] using
    (SurrealCore.PreGame.toIGame_neg (canonicalize a))

theorem toIGameQ_mulQCore (x y : SurrealQ) :
    toIGameQ (mulQCore x y) = toIGameQ x * toIGameQ y := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  simpa [mulQCore, toIGameQ, coreRepr, canonicalize] using
    (SurrealCore.PreGame.toIGame_mul (canonicalize a) (canonicalize b))

theorem toIGameQ_zeroQCore :
    toIGameQ zeroQCore = 0 := by
  change SurrealCore.PreGame.toIGame (canonicalize SurrealCore.nullCut) = 0
  simp [canonicalize, SurrealCore.PreGame.toIGame_nullCut]

theorem toIGameQ_mul_zeroQCore_left (x : SurrealQ) :
    toIGameQ (mulQCore zeroQCore x) = 0 := by
  simp [toIGameQ_mulQCore, toIGameQ_zeroQCore]

theorem toIGameQ_mul_zeroQCore_right (x : SurrealQ) :
    toIGameQ (mulQCore x zeroQCore) = 0 := by
  simp [toIGameQ_mulQCore, toIGameQ_zeroQCore]

theorem toIGameQ_add_zeroQCore_left (x : SurrealQ) :
    toIGameQ (addQCore zeroQCore x) = toIGameQ x := by
  simp [toIGameQ_addQCore, toIGameQ_zeroQCore]

theorem toIGameQ_add_zeroQCore_right (x : SurrealQ) :
    toIGameQ (addQCore x zeroQCore) = toIGameQ x := by
  simp [toIGameQ_addQCore, toIGameQ_zeroQCore]

theorem toIGameQ_mul_addQCore_equiv (x y z : SurrealQ) :
    toIGameQ (mulQCore x (addQCore y z)) ≈
      toIGameQ (addQCore (mulQCore x y) (mulQCore x z)) := by
  simpa [toIGameQ_mulQCore, toIGameQ_addQCore] using
    (IGame.mul_add_equiv (toIGameQ x) (toIGameQ y) (toIGameQ z))

theorem toIGameQ_add_mulQCore_equiv (x y z : SurrealQ) :
    toIGameQ (mulQCore (addQCore x y) z) ≈
      toIGameQ (addQCore (mulQCore x z) (mulQCore y z)) := by
  simpa [toIGameQ_mulQCore, toIGameQ_addQCore] using
    (IGame.add_mul_equiv (toIGameQ x) (toIGameQ y) (toIGameQ z))

theorem toIGameQ_mulQCore_assoc_equiv (x y z : SurrealQ) :
    toIGameQ (mulQCore (mulQCore x y) z) ≈
      toIGameQ (mulQCore x (mulQCore y z)) := by
  simpa [toIGameQ_mulQCore] using
    (IGame.mul_assoc_equiv (toIGameQ x) (toIGameQ y) (toIGameQ z))

theorem toIGameQ_mulQCore_comm (x y : SurrealQ) :
    toIGameQ (mulQCore x y) = toIGameQ (mulQCore y x) := by
  simp [toIGameQ_mulQCore, mul_comm]

theorem toIGameQ_addQCore_comm (x y : SurrealQ) :
    toIGameQ (addQCore x y) = toIGameQ (addQCore y x) := by
  simp [toIGameQ_addQCore, add_comm]

theorem toIGameQ_addQCore_assoc (x y z : SurrealQ) :
    toIGameQ (addQCore (addQCore x y) z) = toIGameQ (addQCore x (addQCore y z)) := by
  simp [toIGameQ_addQCore, add_assoc]

theorem toIGameQ_add_left_negQCore_equiv_zero (x : SurrealQ) :
    toIGameQ (addQCore (negQCore x) x) ≈ 0 := by
  simpa [toIGameQ_addQCore, toIGameQ_negQCore] using
    (IGame.neg_add_equiv (toIGameQ x))

theorem toIGameQ_add_right_negQCore_equiv_zero (x : SurrealQ) :
    toIGameQ (addQCore x (negQCore x)) ≈ 0 := by
  simpa [toIGameQ_addQCore, toIGameQ_negQCore, add_comm] using
    (IGame.neg_add_equiv (toIGameQ x))

theorem toIGameQ_add_left_cancelQCore_equiv (x y : SurrealQ) :
    toIGameQ (addQCore (negQCore x) (addQCore x y)) ≈ toIGameQ y := by
  have hstep1 :
      toIGameQ (addQCore (negQCore x) (addQCore x y)) =
        -toIGameQ x + (toIGameQ x + toIGameQ y) := by
    simp [toIGameQ_addQCore, toIGameQ_negQCore]
  have hstep2 :
      (-toIGameQ x + (toIGameQ x + toIGameQ y)) =
        ((-toIGameQ x + toIGameQ x) + toIGameQ y) := by
    ac_rfl
  calc
    toIGameQ (addQCore (negQCore x) (addQCore x y))
        = ((-toIGameQ x + toIGameQ x) + toIGameQ y) := hstep1.trans hstep2
    _ ≈ (0 + toIGameQ y) := by
          exact IGame.add_congr (IGame.neg_add_equiv (toIGameQ x)) AntisymmRel.rfl
    _ = toIGameQ y := by simp

theorem toIGameQ_add_right_cancelQCore_equiv (x y : SurrealQ) :
    toIGameQ (addQCore x (addQCore (negQCore x) y)) ≈ toIGameQ y := by
  have hstep1 :
      toIGameQ (addQCore x (addQCore (negQCore x) y)) =
        toIGameQ x + (-toIGameQ x + toIGameQ y) := by
    simp [toIGameQ_addQCore, toIGameQ_negQCore]
  have hstep2 :
      (toIGameQ x + (-toIGameQ x + toIGameQ y)) =
        ((toIGameQ x + -toIGameQ x) + toIGameQ y) := by
    ac_rfl
  have hcancel : toIGameQ x + -toIGameQ x ≈ 0 := by
    simpa [add_comm] using (IGame.neg_add_equiv (toIGameQ x))
  calc
    toIGameQ (addQCore x (addQCore (negQCore x) y))
        = ((toIGameQ x + -toIGameQ x) + toIGameQ y) := hstep1.trans hstep2
    _ ≈ (0 + toIGameQ y) := by
          exact IGame.add_congr hcancel AntisymmRel.rfl
    _ = toIGameQ y := by simp

end Surreal
end Numbers
end HeytingLean
