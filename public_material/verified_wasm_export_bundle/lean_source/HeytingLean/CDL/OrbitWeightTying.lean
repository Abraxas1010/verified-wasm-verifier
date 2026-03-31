import HeytingLean.CDL.LaxAlgebraComonoid

/-!
# CDL: orbit-based weight tying + iterated comultiplication

This file packages two CDL-aligned “weight sharing” mechanisms used in HeytingLean:

1. **Orbit-based tying**: given an `R`-normalization on syntax/terms, the quotient by
   `t ≈_R u :↔ R t = R u` is a canonical index set for shared parameters.
2. **Comonoid-based tying**: given a comonoid `(P, ε, Δ)`, repeated use of a cell produces
   parameter objects like `P × P × ...`, and `Δ` (iterated) provides the tying map.
-/

namespace HeytingLean
namespace CDL

universe u

/-! ## 1) Orbit-based tying -/

namespace Orbit

universe v

variable {ProofTerm : Type u}

/-- `R`-equivalence: two terms are equivalent if they have the same `R`-normal form. -/
def REq (R : ProofTerm → ProofTerm) : ProofTerm → ProofTerm → Prop :=
  fun t u => R t = R u

theorem REq_refl (R : ProofTerm → ProofTerm) (t : ProofTerm) : REq R t t := rfl

theorem REq_symm (R : ProofTerm → ProofTerm) {t u : ProofTerm} : REq R t u → REq R u t := by
  intro h
  simpa [REq] using h.symm

theorem REq_trans (R : ProofTerm → ProofTerm) {t u v : ProofTerm} : REq R t u → REq R u v → REq R t v := by
  intro h₁ h₂
  simpa [REq] using h₁.trans h₂

abbrev QuotOrbit (R : ProofTerm → ProofTerm) : Type u :=
  Quot (REq R)

/-- Weights indexed by the `R`-orbit/quotient. -/
abbrev Weights (R : ProofTerm → ProofTerm) (Param : Type v) : Type (max u v) :=
  QuotOrbit (R := R) → Param

/-- Embed a term by looking up its orbit index. -/
def embed (R : ProofTerm → ProofTerm) {Param : Type v} (W : Weights (ProofTerm := ProofTerm) R Param)
    (t : ProofTerm) : Param :=
  W (Quot.mk (REq R) t)

theorem embed_respects_R (R : ProofTerm → ProofTerm) {Param : Type v} (W : Weights (ProofTerm := ProofTerm) R Param)
    {t u : ProofTerm} (h : REq R t u) : embed (ProofTerm := ProofTerm) R W t = embed (ProofTerm := ProofTerm) R W u := by
  have hq : (Quot.mk (REq R) t : QuotOrbit (R := R)) = Quot.mk (REq R) u :=
    Quot.sound h
  simp [embed, hq]

end Orbit

/-! ## 2) Comonoid-based tying (iterated `Δ`) -/

namespace Comult

open HeytingLean.CDL

/-- Right-associated “power” of products, used to represent repeated parameter stacking. -/
def PowProd (P : Type u) : Nat → Type u
  | 0 => PUnit.{u + 1}
  | n + 1 => PowProd P n × P

/-- Iterated comultiplication `Δ` producing `n` copies (encoded as `PowProd`). -/
def iterDelta {P : Type u} (C : ComonoidStruct P) : ∀ n : Nat, P → PowProd (P := P) n
  | 0, _ => PUnit.unit
  | n + 1, p =>
    let pq := C.comult p
    (iterDelta C n pq.1, pq.2)

@[simp] theorem PowProd_zero (P : Type u) : PowProd (P := P) 0 = PUnit.{u + 1} := rfl

@[simp] theorem iterDelta_zero {P : Type u} (C : ComonoidStruct P) (p : P) :
    iterDelta C 0 p = PUnit.unit := rfl

@[simp] theorem iterDelta_one {P : Type u} (C : ComonoidStruct P) (p : P) :
    iterDelta C 1 p = (PUnit.unit, p) := by
  simp [iterDelta, PowProd, ComonoidStruct.comult_snd (C := C)]

end Comult

end CDL
end HeytingLean
