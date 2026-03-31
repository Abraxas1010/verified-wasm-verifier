import HeytingLean.Bridges.Assembly.AssemblyInterior
import HeytingLean.ATheory.AssemblyCore
import HeytingLean.Generative.IntNucleusKit

/-
# Assembly ↔ Birth bridge

This file defines a small interface layer connecting the canonical assembly
reachability interior (Alexandroff opens) to the generic Birth machinery
(`IntNucleusKit.ibirth`).

Important: because the interior nucleus is idempotent, the resulting `ibirth`
is always ≤ 1, so this bridge provides a coarse stability test.
-/

namespace HeytingLean
namespace Bridges
namespace Assembly

open HeytingLean.ATheory
open HeytingLean.Generative
open HeytingLean.LoF

universe u

namespace ASpace

variable {α : Type u} (G : ASpace α)

/-- Birth of a vertex-set under the canonical Alexandroff-style interior. -/
noncomputable def setBirth (U : Set G.V) : Nat :=
  IntNucleusKit.ibirth (R := ASpace.intReentry G) U

theorem setBirth_eq_zero_iff (U : Set G.V) :
    setBirth (G := G) U = 0 ↔ ASpace.opens G U = U := by
  simp [setBirth, ASpace.intReentry, ASpace.intNucleus, ASpace.opens]

theorem setBirth_le_one (U : Set G.V) : setBirth (G := G) U ≤ 1 := by
  simpa [setBirth] using
    (IntNucleusKit.ibirth_le_one (R := ASpace.intReentry G) (a := U))

end ASpace

namespace ObjBridge

variable {Atom : Type}

/-- Convert an assembly object to a singleton vertex-set. -/
def objToSet (o : Obj Atom) : Set (Obj Atom) := {o}

/-- Assembly graph where edges are admissible single-step compositions.

Edges are only from *syntactic joins of base atoms* to base atoms; this matches
the lightweight structure currently present in `HeytingLean.ATheory.AssemblyCore`.
Later work can generalise `E` to permit multi-step / nested composition rules.
-/
def assemblyGraph (R : Rules Atom) : ASpace Atom where
  V := Obj Atom
  E := fun p q =>
    ∃ a b c,
      p = Obj.join (Obj.base a) (Obj.base b) ∧
      q = Obj.base c ∧
      c ∈ R.compose a b

/-- Birth of a single assembly object, via its singleton vertex-set. -/
noncomputable def objectBirth (R : Rules Atom) (o : Obj Atom) : Nat :=
  ASpace.setBirth (G := assemblyGraph (Atom := Atom) R) (objToSet (Atom := Atom) o)

lemma assemblyGraph_no_edge_from_base (R : Rules Atom) (a : Atom) (u : Obj Atom) :
    ¬ (assemblyGraph (Atom := Atom) R).E (Obj.base a) u := by
  intro h
  rcases h with ⟨a', b', c', hp, _hq, _hc⟩
  cases hp

lemma reaches_from_base_eq (R : Rules Atom) (a : Atom) (u : Obj Atom)
    (hu : Relation.ReflTransGen (assemblyGraph (Atom := Atom) R).E (Obj.base a) u) :
    u = Obj.base a := by
  induction hu with
  | refl => rfl
  | tail hab hbc ih =>
      subst ih
      exfalso
      exact assemblyGraph_no_edge_from_base (Atom := Atom) (R := R) (a := a) (u := _) hbc

theorem objectBirth_base_zero (R : Rules Atom) (a : Atom) :
    objectBirth (Atom := Atom) R (Obj.base a) = 0 := by
  -- It suffices to show the singleton `{base a}` is a fixed point of the interior.
  refine
    (ASpace.setBirth_eq_zero_iff (G := assemblyGraph (Atom := Atom) R)
        (U := objToSet (Atom := Atom) (Obj.base a))).2 ?_
  apply Set.Subset.antisymm
  · exact
      ASpace.opens_subset (G := assemblyGraph (Atom := Atom) R)
        (U := objToSet (Atom := Atom) (Obj.base a))
  · intro v hv
    have hv' : v = Obj.base a := by
      simpa [objToSet] using hv
    subst hv'
    intro u hu
    have huE :
        Relation.ReflTransGen (assemblyGraph (Atom := Atom) R).E (Obj.base a) u :=
      (Relation.reflTransGen_swap (r := (assemblyGraph (Atom := Atom) R).E)
          (a := u) (b := Obj.base a)).1 hu
    have : u = Obj.base a :=
      reaches_from_base_eq (Atom := Atom) (R := R) (a := a) (u := u) huE
    simp [objToSet, this]

end ObjBridge

end Assembly
end Bridges
end HeytingLean

