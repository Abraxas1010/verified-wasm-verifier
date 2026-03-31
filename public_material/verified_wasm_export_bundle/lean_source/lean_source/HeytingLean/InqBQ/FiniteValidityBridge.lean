import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap

namespace HeytingLean
namespace InqBQ

/-!
# Finite Validity Bridge

Small native Lean reconstruction of the finite-environment layer used by the
external H10UPC → finite-validity reduction. The point of this module is to
remove low-value transport blockers (`finNum_fin`, `model_fin`, `m_listable`)
from the Coq import lane so the remaining work can focus on the genuinely
semantic theorems.
-/

/-- Uniform Diophantine pair constraints. -/
abbrev H10UPC := (Nat × Nat) × (Nat × Nat)

/-- Direct arithmetic semantics of a uniform Diophantine pair constraint. -/
def h10upcSemDirect : H10UPC → Prop
  | ((x, y), (z₁, z₂)) => 1 + x + y = z₁ ∧ y * (1 + y) = z₂ + z₂

/-- Constraint semantics under an assignment `ρ : ℕ → ℕ`. -/
def h10upcSem (ρ : Nat → Nat) : H10UPC → Prop
  | ((x, y), (z₁, z₂)) => h10upcSemDirect ((ρ x, ρ y), (ρ z₁, ρ z₂))

/-- Uniform Diophantine pair satisfiability. -/
def H10UPCSat (cs : List H10UPC) : Prop :=
  ∃ ρ : Nat → Nat, ∀ c, c ∈ cs → h10upcSem ρ c

/-- Highest variable appearing in a single H10UPC constraint. -/
def highestVar : H10UPC → Nat
  | ((a, b), (c, d)) => max a (max b (max c d))

/-- Highest variable appearing in a finite list of constraints. -/
def highestVarList : List H10UPC → Nat
  | [] => 0
  | c :: cs => max (highestVar c) (highestVarList cs)

/-- Highest value assumed by `ρ` on variables up to `n`. -/
def highestNum (ρ : Nat → Nat) : Nat → Nat
  | 0 => ρ 0
  | n + 1 => max (ρ (n + 1)) (highestNum ρ n)

/-- Coq-style computational listability witness. -/
abbrev cListable (X : Type) := Σ' L : List X, ∀ x : X, x ∈ L

/-- Propositional listability. -/
def listable (X : Type) : Prop := ∃ L : List X, ∀ x : X, x ∈ L

theorem cListable_to_listable {X : Type} : cListable X → listable X
  | ⟨L, hL⟩ => ⟨L, hL⟩

noncomputable def cListable_ofFintype (X : Type) [Fintype X] : cListable X := by
  refine ⟨Finset.univ.toList, ?_⟩
  intro x
  simpa using Finset.mem_toList.mpr (Finset.mem_univ x)

/-- Numbers bounded by `m`. This is the Lean reconstruction of Coq's `finNum`. -/
abbrev finNum (m : Nat) := { n : Nat // n ≤ m }

instance (m : Nat) : DecidableEq (finNum m) := inferInstance

def finNumEquiv (m : Nat) : Fin (m + 1) ≃ finNum m where
  toFun i := ⟨i.1, Nat.le_of_lt_succ i.2⟩
  invFun n := ⟨n.1, Nat.lt_succ_of_le n.2⟩
  left_inv i := by
    cases i
    rfl
  right_inv n := by
    cases n
    rfl

instance (m : Nat) : Fintype (finNum m) :=
  Fintype.ofEquiv (Fin (m + 1)) (finNumEquiv m)

noncomputable def finNum_fin (m : Nat) : cListable (finNum m) :=
  cListable_ofFintype (finNum m)

/-- Elements of the finite transport model. -/
inductive Model (m : Nat) where
  | num : finNum m → Model m
  | pair : finNum m → finNum m → Model m
  deriving DecidableEq

noncomputable def model_fin (m : Nat) : cListable (Model m) := by
  let xs := (finNum_fin m).1
  refine ⟨xs.map Model.num ++ xs.flatMap (fun a => xs.map (Model.pair a)), ?_⟩
  intro x
  cases x with
  | num a =>
      apply List.mem_append.mpr
      left
      exact List.mem_map.mpr ⟨a, (finNum_fin m).2 a, rfl⟩
  | pair a b =>
      apply List.mem_append.mpr
      right
      exact List.mem_flatMap.mpr ⟨a, (finNum_fin m).2 a, List.mem_map.mpr ⟨b, (finNum_fin m).2 b, rfl⟩⟩

noncomputable instance (m : Nat) : Fintype (Model m) :=
  Fintype.ofList (List.dedup (model_fin m).1) (by
    intro x
    simpa using List.mem_dedup.mpr ((model_fin m).2 x))

noncomputable instance (m : Nat) : Finite (Model m) :=
  Finite.of_fintype (Model m)

theorem m_listable (m : Nat) : listable (Model m) :=
  cListable_to_listable (model_fin m)

/-- Relation used by the canonical finite model in the H10UPC transport proof. -/
def modelRel (m : Nat) : Model m → Model m → Prop
  | .num a, .num b => a.1 ≤ b.1
  | .pair _ r, .num n => r.1 = n.1
  | .num n, .pair l _ => n.1 = l.1
  | .pair a b, .pair c d =>
      h10upcSemDirect ((a.1, b.1), (c.1, d.1))

instance (m : Nat) : DecidableRel (modelRel m) := by
  intro a b
  cases a with
  | num a =>
      cases b with
      | num b =>
          simpa [modelRel] using (inferInstance : Decidable (a.1 ≤ b.1))
      | pair l r =>
          simpa [modelRel] using (inferInstance : Decidable (a.1 = l.1))
  | pair a r =>
      cases b with
      | num n =>
          simpa [modelRel] using (inferInstance : Decidable (r.1 = n.1))
      | pair c d =>
          simpa [modelRel, h10upcSemDirect] using
            (inferInstance : Decidable (1 + a.1 + r.1 = c.1 ∧ r.1 * (1 + r.1) = d.1 + d.1))

/-- Predicate on length-2 vectors induced by `modelRel`. -/
def modelRelVec2 (m : Nat) (v : Vector (Model m) 2) : Prop :=
  modelRel m (v.get ⟨0, by decide⟩) (v.get ⟨1, by decide⟩)

def m_decidable (m : Nat) : DecidablePred (modelRelVec2 m) := by
  intro v
  dsimp [modelRelVec2]
  infer_instance

end InqBQ
end HeytingLean
