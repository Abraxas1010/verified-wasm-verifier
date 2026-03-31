import HeytingLean.ATheory.AssemblyCore
import HeytingLean.ATheory.CopyNumberSelection
import HeytingLean.ATheory.Paper.AssemblyIndex
import HeytingLean.ATheory.Paper.AssemblyBounds
import HeytingLean.ATheory.Paper.AssemblyQuotient
import HeytingLean.ATheory.Paper.HypergraphSpace
import HeytingLean.ATheory.Paper.MolecularSpace
import HeytingLean.ATheory.Paper.StringPermSpace
import HeytingLean.Bridges.Assembly.AssemblyBirth
import HeytingLean.Metrics.AssemblyComplexity

/-
# AssemblyCompliance tests

Small compile-only checks for the Assembly Theory layer:
* a tiny finite alphabet and simple rules;
* concrete objects and their structural assembly indices;
* Assembly functional and selection predicate on a finite set.
-/

namespace HeytingLean
namespace Tests
namespace Assembly

open HeytingLean.ATheory
open HeytingLean.ATheory.Paper
open HeytingLean.Bridges
open HeytingLean.Metrics

private def eqSetoid (α : Type*) : Setoid α :=
  Setoid.mk (· = ·)
    ⟨by intro x; rfl,
     by intro x y h; simpa using h.symm,
     by intro x y z hxy hyz; exact hxy.trans hyz⟩

/-- Tiny alphabet of primitive parts for tests. -/
inductive Part
  | A | B | C
deriving DecidableEq

/-- Simple rule set where composition is always allowed but ignores its inputs.
This keeps the test logic simple and ensures the types are exercised. -/
def demoRules : Rules Part where
  compose _ _ := {}

/-- A few example assembly objects built from the finite alphabet. -/
def objA  : Obj Part := Obj.base Part.A
def objAB : Obj Part := Obj.join (Obj.base Part.A) (Obj.base Part.B)
def objABA : Obj Part :=
  Obj.join (Obj.base Part.A) (Obj.join (Obj.base Part.B) (Obj.base Part.A))

-- A reuse-heavy object: the subtree `Obj.join A B` appears twice.
def objABAB : Obj Part :=
  Obj.join objAB objAB

/-- Sanity examples: structural assembly indices via `joinCount`. -/
example : syntacticIndex demoRules objA = 0 := rfl
example : syntacticIndex demoRules objAB = 1 := rfl
example : syntacticIndex demoRules objABA = 2 := rfl

-- Reuse-aware index: `objABAB` requires only two distinct joins (`AB`, then `ABAB`).
example : syntacticIndex demoRules objABAB = 2 := rfl

/-!
Paper-style path/index sanity

The paper-facing `AssemblySpace/AssemblyPath/AssemblyIndex` definitions are upstreamed under
`HeytingLean.ATheory.Paper`.
-/

example :
    ATheory.Paper.AssemblySpace.AssemblyIndex.assemblyIndex
        (S := ATheory.Paper.ObjSyntax.space (Atom := Part))
        (hC := ATheory.Paper.ObjSyntax.space.closed (Atom := Part))
        (Obj.join (Obj.base Part.A) (Obj.base Part.B))
      ≤ Obj.joinCount (Obj.join (Obj.base Part.A) (Obj.base Part.B)) := by
  simpa using
    (ATheory.Paper.ObjSyntax.space.assemblyIndex_le_joinCount (Atom := Part)
      (o := Obj.join (Obj.base Part.A) (Obj.base Part.B)))

-- In the syntax-tree model, the paper-style minimal index coincides with `dagJoinCount`.
example :
    ATheory.Paper.AssemblySpace.AssemblyIndex.assemblyIndex
        (S := ATheory.Paper.ObjSyntax.space (Atom := Part))
        (hC := ATheory.Paper.ObjSyntax.space.closed (Atom := Part))
        objABAB
      = Obj.dagJoinCount objABAB := by
  simpa using
    (ATheory.Paper.ObjSyntax.space.assemblyIndex_eq_dagJoinCount (Atom := Part)
      (o := objABAB))

/-! Hypergraph view (Extension 3) sanity checks -/

open ATheory.Paper.BHypergraph in
def objSyntaxHyper (Atom : Type*) : ATheory.Paper.BHypergraph.Graph :=
  ofAssemblySpace (ATheory.Paper.ObjSyntax.space (Atom := Atom))

open ATheory.Paper.BHypergraph in
example :
    ATheory.Paper.BHypergraph.HyperIndex.hyperIndex
        (H := objSyntaxHyper Part)
        (hC := by
          -- `Closed` is definitional via `toAssemblySpace`.
          simpa [objSyntaxHyper, ATheory.Paper.BHypergraph.Closed,
            ATheory.Paper.BHypergraph.toAssemblySpace, ATheory.Paper.BHypergraph.ofAssemblySpace]
            using (ATheory.Paper.ObjSyntax.space.closed (Atom := Part)))
        objABAB
      = Obj.dagJoinCount objABAB := by
  -- By definition, `hyperIndex` is `assemblyIndex`, and in the syntax space
  -- `assemblyIndex = dagJoinCount`.
  simpa [objSyntaxHyper, ATheory.Paper.BHypergraph.HyperIndex.hyperIndex,
    ATheory.Paper.BHypergraph.toAssemblySpace, ATheory.Paper.BHypergraph.ofAssemblySpace]
    using (ATheory.Paper.ObjSyntax.space.assemblyIndex_eq_dagJoinCount (Atom := Part) (o := objABAB))

/-! Extension 4: bounds sanity checks -/

example : Nat.log 2 (Obj.size objABAB) ≤ Obj.dagJoinCount objABAB := by
  have ho : Obj.size objABAB > 1 := by
    have hs : Obj.size objABAB = 4 := by
      simp [HeytingLean.ATheory.Obj.size, objABAB, objAB]
    have : (4 : Nat) > 1 := by decide
    rw [hs]
    exact this
  exact (ATheory.Paper.AssemblyBounds.dagJoinCount_bounds (α := Part) (o := objABAB) ho).1

example : Obj.dagJoinCount objABAB ≤ Obj.size objABAB - 1 := by
  have ho : Obj.size objABAB > 1 := by
    have hs : Obj.size objABAB = 4 := by
      simp [HeytingLean.ATheory.Obj.size, objABAB, objAB]
    have : (4 : Nat) > 1 := by decide
    rw [hs]
    exact this
  exact (ATheory.Paper.AssemblyBounds.dagJoinCount_bounds (α := Part) (o := objABAB) ho).2

/-! Molecular assembly (Extension 1) sanity checks -/

open ATheory.Paper.Molecular in
def testBond1 : Bond Part := ⟨0, Part.A, Part.B⟩

open ATheory.Paper.Molecular in
def testBond2 : Bond Part := ⟨1, Part.B, Part.C⟩

-- A simple two-bond molecule: A—B—C
open ATheory.Paper.Molecular in
def molABC : Obj (Bond Part) := Obj.join (Obj.base testBond1) (Obj.base testBond2)

-- The syntax-level index equals dagJoinCount.
example :
    ATheory.Paper.AssemblySpace.AssemblyIndex.assemblyIndex
        (S := ATheory.Paper.ObjSyntax.space (Atom := ATheory.Paper.Molecular.Bond Part))
        (hC := ATheory.Paper.ObjSyntax.space.closed (Atom := ATheory.Paper.Molecular.Bond Part))
        (molABC)
      = Obj.dagJoinCount molABC := by
  exact ATheory.Paper.Molecular.assemblyIndex_syntax_eq_dagJoinCount (Atom := Part) molABC

-- The quotient-level index is bounded by dagJoinCount.
example :
    ATheory.Paper.AssemblySpace.AssemblyIndex.assemblyIndex
        (S := ATheory.Paper.Molecular.molSpace (Atom := Part))
        (hC := ATheory.Paper.Molecular.closed (Atom := Part))
        (Quotient.mk (ATheory.Paper.Molecular.evalIsoSetoid (Atom := Part)) molABC)
      ≤ Obj.dagJoinCount molABC := by
  exact ATheory.Paper.Molecular.assemblyIndex_mol_le_dagJoinCount (Atom := Part) molABC

-- Goal B sanity: in a rule+equivalence “string” model, the semantic index is bounded by the
-- reuse-aware DAG count of a chosen syntax presentation.
example :
    ATheory.Paper.AssemblySpace.AssemblyIndex.assemblyIndex
        (S := ATheory.Paper.StringPerm.space (Atom := Part))
        (hC := ATheory.Paper.StringPerm.space.closed (Atom := Part))
        (ATheory.Paper.StringPerm.flatten (Atom := Part) objABAB)
      ≤ Obj.dagJoinCount objABAB := by
  simpa using
    (ATheory.Paper.StringPerm.assemblyIndex_flatten_le_dagJoinCount (Atom := Part)
      (o := objABAB))

-- Extension 2 sanity: quotient assembly index is bounded by the original index.
example :
    ATheory.Paper.AssemblySpace.AssemblyIndex.assemblyIndex
        (S := (ATheory.Paper.AssemblySpace.quotient
          (S := ATheory.Paper.ObjSyntax.space (Atom := Part))
          (eqSetoid (Obj Part))))
        (hC := ATheory.Paper.AssemblySpace.Closed.quotient
          (S := ATheory.Paper.ObjSyntax.space (Atom := Part))
          (ATheory.Paper.ObjSyntax.space.closed (Atom := Part))
          (eqSetoid (Obj Part)))
        (Quotient.mk (eqSetoid (Obj Part)) objABAB)
      ≤
      ATheory.Paper.AssemblySpace.AssemblyIndex.assemblyIndex
        (S := ATheory.Paper.ObjSyntax.space (Atom := Part))
        (hC := ATheory.Paper.ObjSyntax.space.closed (Atom := Part))
        objABAB := by
  simpa using
    (ATheory.Paper.AssemblySpace.AssemblyIndex.assemblyIndex_quotient_le
      (S := ATheory.Paper.ObjSyntax.space (Atom := Part))
      (hC := ATheory.Paper.ObjSyntax.space.closed (Atom := Part))
      (r := eqSetoid (Obj Part))
      (z := objABAB))

/-!
Assembly ↔ Birth bridge checks

These are compile-only sanity checks ensuring the reachability-interior packaging
(`IntReentry`) and the resulting `ibirth` specialization are usable.

Note: `ibirth` is always ≤ 1 for an idempotent interior nucleus.
-/

open Bridges.Assembly in
example :
    ObjBridge.objectBirth (Atom := Part) demoRules (Obj.base Part.A) = 0 := by
  simpa [objA] using
    (ObjBridge.objectBirth_base_zero (Atom := Part) (R := demoRules) (a := Part.A))

open Bridges.Assembly in
example :
    ObjBridge.objectBirth (Atom := Part) demoRules objAB ≤ 1 := by
  -- This follows from the general `ibirth_le_one` bound.
  simpa [ObjBridge.objectBirth] using
    (ASpace.setBirth_le_one (G := ObjBridge.assemblyGraph (Atom := Part) demoRules)
      (U := ObjBridge.objToSet (Atom := Part) objAB))

/-- A simple index function reusing `syntacticIndex`. -/
def idx (o : Obj Part) : Nat :=
  syntacticIndex demoRules o

/-- A simple weight function assigning larger weights to more complex objects. -/
def mu (o : Obj Part) : Nat :=
  match o with
  | Obj.base _      => 1
  | Obj.join _ _    => 2

/-- Assembly functional can be evaluated on these example objects. -/
example : Assembly idx mu objABA = (mu objABA : ℝ) * (idx objABA + 1 : ℝ) := rfl

/- A simple finite set of objects as a `Finset`. -/
def objSet : Finset (Obj Part) :=
  {objA, objAB}

/-- Selection predicate can be instantiated on these example objects. -/
example : selected 1 1 objSet idx mu ∨ ¬ selected 1 1 objSet idx mu := by
  -- This is a trivial classical case split; the main purpose is to ensure
  -- the predicate is usable and compiles.
  classical
  exact em _

/-- Ensemble-level Assembly quantity is defined and finite on the example set. -/
example : AssemblyEnsemble idx mu objSet = 0 ∨ AssemblyEnsemble idx mu objSet ≠ 0 := by
  classical
  exact em _

/-- On the specific example set `objSet = {objA, objAB}`, the ensemble-level
Assembly quantity reduces to a simple closed form that can be computed
directly. In particular, only `objAB` contributes a nonzero term. -/
example :
    AssemblyEnsemble idx mu objSet =
      Real.exp (idx objAB : ℝ) * ((2 - 1 : ℝ) / (3 : ℝ)) := by
  classical
  -- `objSet` has copy numbers 1 and 2, so the total is 3.
  -- The contribution from `objA` vanishes since `mu objA - 1 = 0`.
  -- The contribution from `objAB` is `exp(1) * (1 / 3)`.
  simp [objSet, AssemblyEnsemble, idx, mu, demoRules, objA, objAB]

/-
Assembly-based complexity wrappers

These examples exercise the metrics layer in `HeytingLean.Metrics.AssemblyComplexity`
on the same tiny alphabet, wiring object and ensemble scores through to the
core Assembly quantities.
-/

open Metrics.AssemblyComplexity

/-- Copy-number configuration for the test objects, reusing `mu` both as
raw copy number and as secondary weight. For objects outside the tiny
test set we default to zero counts. -/
def partCopy : CopyNumber (Obj Part) where
  n o :=
    match o with
    | Obj.base Part.A => 1
    | Obj.join (Obj.base Part.A) (Obj.base Part.B) => 2
    | Obj.join (Obj.base Part.A)
        (Obj.join (Obj.base Part.B) (Obj.base Part.A)) => 0
    | _ => 0
  μ o := mu o

/-- Assembly-complexity configuration for the tiny test ensemble. -/
def cfg : Config (Obj Part) where
  idx  := idx
  copy := partCopy

/-- Object-level Assembly score is just the underlying `Assembly` functional. -/
example :
    cfg.objectScore objAB =
      Assembly idx mu objAB := rfl

/-- Ensemble-level complexity reduces to the same closed form as the earlier
`AssemblyEnsemble` example, now routed through the metrics configuration. -/
example :
    cfg.ensembleScore objSet =
      Real.exp (idx objAB : ℝ) * ((2 - 1 : ℝ) / (3 : ℝ)) := by
  classical
  -- Here `cfg.copy.n = mu`, so the computation matches the previous lemma.
  simp [cfg, Config.ensembleScore, partCopy, objSet, AssemblyEnsemble,
        idx, mu, demoRules, objA, objAB]

end Assembly
end Tests
end HeytingLean
