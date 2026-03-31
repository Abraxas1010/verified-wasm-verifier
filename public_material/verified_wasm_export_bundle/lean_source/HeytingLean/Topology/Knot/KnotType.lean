import Mathlib.Logic.Relation
import HeytingLean.Topology.Knot.BracketMathlibReidemeisterR1
import HeytingLean.Topology.Knot.JonesMathlibLaws

/-!
# Knot theory: knot types (Phase 1, proof-oriented skeleton)

This module introduces a *proof-oriented* notion of "knot type" as an equivalence class of
well-formed signed PD graphs under a chosen move relation.

In Phase 1 we start with the minimal ambient-isotopy ingredient that is already proven in this
repository's Mathlib Laurent polynomial layer:

- Reidemeister-I moves (`r1Add`) leave the *Jones-normalized* bracket invariant.

We package this as a quotient type `KnotTypeR1` together with a well-defined invariant
`KnotTypeR1.normalizedBracketML`.
-/

namespace HeytingLean
namespace Topology
namespace Knot

namespace Kauffman

open scoped LaurentPolynomial
open Reidemeister

noncomputable section

/-- A signed PD graph with a proof that the sign array length matches the number of crossings. -/
structure SignedPDGraphWF where
  graph : PDGraph
  sign : Array CurlKind
  sign_size : sign.size = graph.n
deriving Repr

namespace SignedPDGraphWF

/-- Jones-normalized bracket in the Mathlib Laurent polynomial layer. -/
def normalizedBracketML (s : SignedPDGraphWF) : Except String PolyML :=
  Kauffman.normalizedBracketML s.graph s.sign

end SignedPDGraphWF

/-- One Reidemeister‑I step between well-formed signed PD graphs. -/
def R1Step (s t : SignedPDGraphWF) : Prop :=
  ∃ (x : Nat) (kind : CurlKind),
    Reidemeister.r1Add s.graph x kind = .ok t.graph ∧ t.sign = s.sign.push kind

theorem normalizedBracketML_eq_of_R1Step {s t : SignedPDGraphWF} (h : R1Step s t) :
    SignedPDGraphWF.normalizedBracketML s = SignedPDGraphWF.normalizedBracketML t := by
  classical
  rcases h with ⟨x, kind, hAdd, hsign⟩
  have hs' : (s.sign.push kind).size = t.graph.n := by
    simpa [hsign] using t.sign_size
  -- Rewrite the target signs using `hsign`, then apply the corresponding normalisation law.
  simp [SignedPDGraphWF.normalizedBracketML, hsign]
  cases kind with
  | pos =>
      exact (normalizedBracketML_r1Add_pos (g := s.graph) (g' := t.graph) (x := x) (sign := s.sign)
        (hs := s.sign_size) (hs' := hs') (h := hAdd)).symm
  | neg =>
      exact (normalizedBracketML_r1Add_neg (g := s.graph) (g' := t.graph) (x := x) (sign := s.sign)
        (hs := s.sign_size) (hs' := hs') (h := hAdd)).symm

/-- Knot types modulo Reidemeister‑I only (Phase 1 stepping stone). -/
def knotTypeR1Setoid : Setoid SignedPDGraphWF where
  r := Relation.EqvGen R1Step
  iseqv :=
    ⟨(fun x => Relation.EqvGen.refl (r := R1Step) x),
      (fun {x y} h => Relation.EqvGen.symm (r := R1Step) x y h),
      (fun {x y z} h1 h2 => Relation.EqvGen.trans (r := R1Step) x y z h1 h2)⟩

def KnotTypeR1 : Type :=
  Quot knotTypeR1Setoid

namespace KnotTypeR1

/-- The Jones-normalized bracket descends to `KnotTypeR1`. -/
def normalizedBracketML : KnotTypeR1 → Except String PolyML :=
  Quot.lift SignedPDGraphWF.normalizedBracketML (by
    intro a b hab
    change Relation.EqvGen R1Step a b at hab
    induction hab with
    | rel x y hxy =>
        exact normalizedBracketML_eq_of_R1Step hxy
    | refl x =>
        rfl
    | symm x y _ ih =>
        simpa using ih.symm
    | trans _ _ _ _ _ ihxy ihyz =>
        exact ihxy.trans ihyz)

end KnotTypeR1

end

end Kauffman

end Knot
end Topology
end HeytingLean
