import HeytingLean.LoF.Bauer.DoubleNegation
import HeytingLean.LoF.Combinators.Heyting.NucleusRangeOps
import HeytingLean.LoF.Combinators.Topos.ClosureVsTruncation
import HeytingLean.LoF.Combinators.Topos.ClosedSievesHeyting
import HeytingLean.LoF.Combinators.Topos.SieveNucleus

/-!
# DenseTopologyLoFOps — Phase G.2: Heyting ops on closed sieves match LoF ops

This file completes the previously “scoped” verification item **G.2**:

> “Heyting ops on closed sieves match LoF ops.”

The precise, Lean-verifiable statement implemented here is:

* For the **dense** Grothendieck topology, `J.close` is **double negation** on sieves, hence
  the type of `J`-closed sieves is equivalent to the **Boolean core** of Heyting-regular sieves.
* Under coercion back to ambient sieves, the Heyting operations on `ClosedSieve J X` agree with the
  expected LoF reading:
  - `juxt` ↦ `⊔` (join, with `J.close`/`¬¬` regularization in the dense case),
  - `mark` ↦ `ᶜ` (negation, since `close ⊥ = ⊥` for the dense topology),
  - `→` ↦ `⇨` (Heyting implication), which in the range is inherited from the ambient frame.

This is the standard “Booleanization / double-negation topology” mechanism.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Topos

open CategoryTheory
open Order

open HeytingLean.LoF.Bauer

namespace DenseTopology

universe v u
variable {C : Type u} [Category.{v} C]

/-- On sieves, the dense-topology closure nucleus is definitionally the double-negation nucleus. -/
lemma sieveNucleus_dense_eq_doubleNeg (X : C) :
    sieveNucleus (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X =
      doubleNegNucleus (Sieve X) := by
  classical
  ext S
  simp [sieveNucleus, doubleNegNucleus,
    DenseTopology.close_eq_doubleNeg (C := C) (S := S)]

/-- For the dense topology, closed sieves are exactly the Heyting-regular (“classical core”) sieves. -/
noncomputable def closedSieveEquivClassicalCore (X : C) :
    ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X ≃
      ClassicalCore (Sieve X) := by
  simpa [ClosedSieve, sieveNucleus_dense_eq_doubleNeg (C := C) (X := X)] using
    (rangeDoubleNegEquivClassicalCore (α := Sieve X))

/-- Coercion of `⊥` in `ClosedSieve dense X` is the empty sieve. -/
lemma coe_bot (X : C) :
    ((⊥ : ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X) : Sieve X) =
      (⊥ : Sieve X) := by
  -- Coe `⊥` is `close ⊥` in the range-of-nucleus presentation.
  -- For the dense topology, `close ⊥ = ⊥`.
  simpa using congrArg (fun (S : Sieve X) => S) (DenseTopology.close_bot (C := C) (X := X))

/-- In `ClosedSieve dense X`, Heyting implication is inherited from the ambient sieve frame. -/
lemma coe_himp {X : C}
    (S T : ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X) :
    ((S ⇨ T :
        ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X) : Sieve X) =
      (S : Sieve X) ⇨ (T : Sieve X) := by
  simpa using
    (Heyting.Nucleus.coe_himp (n := sieveNucleus (C := C)
      (GrothendieckTopology.dense : GrothendieckTopology C) X) (a := S) (b := T))

/-- In `ClosedSieve dense X`, coercion of join is double-negation (dense closure) of the ambient join. -/
lemma coe_sup {X : C}
    (S T : ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X) :
    ((S ⊔ T :
        ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X) : Sieve X) =
      ((S : Sieve X) ⊔ (T : Sieve X))ᶜᶜ := by
  -- `⊔` in the range is `close` of ambient `⊔`, and for the dense topology `close = ¬¬`.
  change
      (sieveNucleus (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X)
          ((S : Sieve X) ⊔ (T : Sieve X)) =
        ((S : Sieve X) ⊔ (T : Sieve X))ᶜᶜ
  simp [sieveNucleus, DenseTopology.close_eq_doubleNeg (C := C) (S := (S : Sieve X) ⊔ (T : Sieve X))]

/-- In `ClosedSieve dense X`, coercion of negation agrees with ambient negation on sieves. -/
lemma coe_compl {X : C}
    (S : ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X) :
    ((Sᶜ :
        ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X) : Sieve X) =
      (S : Sieve X)ᶜ := by
  -- In any Heyting algebra, `aᶜ = a ⇨ ⊥`.  Use `coe_himp` + `coe_bot`.
  have h1 :
      (Sᶜ :
          ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X) =
        S ⇨ (⊥ :
          ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X) :=
    (himp_bot (a := S)).symm
  have h1' :
      ((Sᶜ :
          ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X) : Sieve X) =
        ((S ⇨ (⊥ :
            ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X) :
          ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X) : Sieve X) :=
    congrArg
      (fun T :
        ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X => (T : Sieve X))
      h1
  calc
    ((Sᶜ :
        ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X) : Sieve X)
        =
        ((S ⇨ (⊥ :
            ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X) :
          ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X) : Sieve X) := h1'
    _   = (S : Sieve X) ⇨
          ((⊥ :
            ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X) : Sieve X) := by
            simpa using
              coe_himp (C := C) (X := X) (S := S)
                (T := (⊥ :
                  ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) X))
    _   = (S : Sieve X) ⇨ (⊥ : Sieve X) := by
            simp [coe_bot (C := C) (X := X)]
    _   = (S : Sieve X)ᶜ := by
            exact himp_bot (a := (S : Sieve X))

end DenseTopology

end Topos
end Combinators
end LoF
end HeytingLean
