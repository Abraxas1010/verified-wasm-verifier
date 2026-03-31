import HeytingLean.Crypto.ConstructiveHardness.ContextualityPhysical

/-!
# (B) Constructor existence: task-possible / task-impossible

This file provides the constructor-theoretic “physical layer” vocabulary:

* a type of constructors `Ctor`;
* an “implements/achieves” predicate `implements : Ctor → Prop → Prop`; and
* possibility as existence of a constructor: `possible P := ∃ c, implements c P`.

Crucially, we require **soundness**:

    implements c P → P

so that “possible” implies logical satisfiability. This matches the Constructor-Theory intent:
physical possibility is stronger than truth, not the other way around.

We also include a minimal monotonicity law so that “achieving P” also “achieves Q” whenever
`P → Q`.
-/

namespace HeytingLean
namespace Crypto
namespace ConstructiveHardness

-- Bring the CryptoSheaf/Quantum contextuality vocabulary (`Context`, `EmpiricalModel`, …).
open HeytingLean.LoF.CryptoSheaf.Quantum

/-- Constructor-theoretic interface on propositions (statement-first).

`implements c P` should be read as “constructor `c` achieves the specification `P`”.

This is deliberately abstract: concretely modeling physics will live in later layers.
-/
structure PropCT where
  Ctor : Type
  implements : Ctor → Prop → Prop
  sound : ∀ {c : Ctor} {P : Prop}, implements c P → P
  implements_mono :
    ∀ (c : Ctor) {P Q : Prop}, (P → Q) → implements c P → implements c Q

namespace PropCT

variable (CT : PropCT)

/-- A proposition is “physically possible” when some constructor achieves it. -/
def possible (P : Prop) : Prop :=
  ∃ c : CT.Ctor, CT.implements c P

/-- A proposition is “physically impossible” when no constructor achieves it. -/
def impossible (P : Prop) : Prop :=
  ¬ possible (CT := CT) P

lemma possible_sound {P : Prop} : CT.possible P → P := by
  intro h
  rcases h with ⟨c, hc⟩
  exact CT.sound hc

lemma possible_mono {P Q : Prop} (hPQ : P → Q) : CT.possible P → CT.possible Q := by
  intro hP
  rcases hP with ⟨c, hcP⟩
  refine ⟨c, ?_⟩
  exact CT.implements_mono c hPQ hcP

/-- The “possible” operator induced by a `PropCT` is a `PhysicalModality`. -/
def toPhysicalModality : PhysicalModality where
  toFun := CT.possible
  mono := by
    intro P Q hPQ
    exact CT.possible_mono hPQ
  sound := by
    intro P hP
    exact CT.possible_sound hP

/-!
## Contextuality ⇒ constructor-theoretic impossibility (general)

Given a `PropCT`, we can read `CT.possible P` as “there exists a constructor achieving P”.
Then contextuality (`¬P`) implies `¬ CT.possible P` by soundness.

This specializes to `P := HasGlobalSection ...` for any empirical model.
-/

theorem contextuality_implies_no_constructor
    (X : Context) (cover : Finset Context)
    (e : EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) :
    NoGlobalSection X cover e coverSubX →
      CT.impossible (GlobalSectionTask X cover e coverSubX) := by
  intro hNo
  -- Use the generic “physical modality” bridge (A) with the modality induced by `CT`.
  have : ¬ (CT.toPhysicalModality.toFun (GlobalSectionTask X cover e coverSubX)) :=
    contextuality_implies_physImpossible
      (Φ := CT.toPhysicalModality)
      (X := X) (cover := cover) (e := e) (coverSubX := coverSubX) hNo
  -- Unfold to the named `impossible` predicate.
  simpa [PropCT.impossible, PropCT.possible, PropCT.toPhysicalModality] using this

end PropCT

end ConstructiveHardness
end Crypto
end HeytingLean
