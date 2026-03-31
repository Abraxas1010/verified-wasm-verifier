/-
  Certified nucleus helpers.

  HeytingLean's LoF infrastructure already uses Mathlib's `Nucleus` (an inflationary,
  idempotent, inf-preserving endomorphism). This file provides MLTT-style wrappers
  around fixed points, using `Certified` to carry the proof that a value is fixed.
-/

import Mathlib.Order.Nucleus
import HeytingLean.Certified.Basic

namespace HeytingLean
namespace Nucleus

open HeytingLean.Certified

universe u

/-- A "certified nucleus" is exactly Mathlib's `Nucleus`. -/
abbrev CertifiedNucleus (X : Type u) [SemilatticeInf X] : Type u :=
  _root_.Nucleus X

/-- Fixed point predicate for a nucleus. -/
def IsFixedPoint {X : Type u} [SemilatticeInf X] (n : CertifiedNucleus X) (x : X) : Prop :=
  n x = x

/-- Certified fixed point: value with proof it is fixed. -/
abbrev CertifiedFixedPoint {X : Type u} [SemilatticeInf X] (n : CertifiedNucleus X) : Type u :=
  Certified X (IsFixedPoint n)

namespace CertifiedFixedPoint

/-- Extract the fixed point value (proof erased). -/
@[inline] def extract {X : Type u} [SemilatticeInf X] {n : CertifiedNucleus X}
    (fp : CertifiedFixedPoint n) : X :=
  fp.val

end CertifiedFixedPoint

/-- Nucleus closure operation with certificate: `x ↦ n x` is always a fixed point. -/
def close {X : Type u} [SemilatticeInf X] (n : CertifiedNucleus X) (x : X) : CertifiedFixedPoint n :=
  ⟨n x, by
    simp [IsFixedPoint]⟩

end Nucleus
end HeytingLean
