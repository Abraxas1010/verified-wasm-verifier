import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset

/-
- source_type: combinatorics (Frankl 1979)
- attribution_status: A-conditional (open conjecture)
- claim_status: statement only (conjecture, not proved)
- proof_status: definitions proved, conjecture stated without proof
-/

namespace HeytingLean
namespace Frankl

/-- A family of finite sets is union-closed if it is closed under pairwise union. -/
def UnionClosed {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A B, A ∈ F → B ∈ F → A ∪ B ∈ F

/-- The frequency of an element `x` in a family `F`: how many sets contain `x`. -/
def frequency {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α) : Nat :=
  (F.filter (fun S => x ∈ S)).card

/-- An element is abundant in `F` if it appears in at least half the sets. -/
def Abundant {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α) : Prop :=
  2 * frequency F x ≥ F.card

/-- The ground set of a family: the union of all sets in the family. -/
def groundSet {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Finset α :=
  F.biUnion id

/-- Frankl's union-closed sets conjecture (stated, not proved). -/
def FranklConjecture : Prop :=
  ∀ (α : Type*) [DecidableEq α] [Fintype α]
    (F : Finset (Finset α)),
    UnionClosed F →
    F.Nonempty →
    (∃ S ∈ F, S.Nonempty) →
    ∃ x, Abundant F x

/-- Gilmer's 1% weakening (stated as a target proposition). -/
def GilmerBound : Prop :=
  ∀ (α : Type*) [DecidableEq α] [Fintype α]
    (F : Finset (Finset α)),
    UnionClosed F →
    F.Nonempty →
    (∃ S ∈ F, S.Nonempty) →
    ∃ x, 100 * frequency F x ≥ F.card

/-- A union-closed family is trivial if it consists of a single set. -/
def Trivial {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  F.card ≤ 1

/-- Frankl's conjecture holds trivially for singleton families. -/
theorem frankl_trivial {α : Type*} [DecidableEq α]
    (F : Finset (Finset α))
    (hF : F.card = 1)
    (hne : ∃ S ∈ F, S.Nonempty) :
    ∃ x, Abundant F x := by
  obtain ⟨S, hS, hSnonempty⟩ := hne
  rcases hSnonempty with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hxInFilter : S ∈ F.filter (fun T => x ∈ T) := by
    simp [hS, hx]
  have hfreqPos : 1 ≤ frequency F x := by
    unfold frequency
    exact Finset.one_le_card.mpr ⟨S, hxInFilter⟩
  have htwo : 2 ≤ 2 * frequency F x := by
    simpa using (Nat.mul_le_mul_left 2 hfreqPos)
  have hbound : 2 * frequency F x ≥ 1 := by
    exact le_trans (by decide : 1 ≤ 2) htwo
  simpa [Abundant, hF] using hbound

/-- Frankl's conjecture holds for families of size ≤ 2. -/
theorem frankl_two {α : Type*} [DecidableEq α]
    (F : Finset (Finset α))
    (_huc : UnionClosed F)
    (hcard : F.card ≤ 2)
    (_hne : F.Nonempty)
    (hnotempty : ∃ S ∈ F, S.Nonempty) :
    ∃ x, Abundant F x := by
  obtain ⟨S, hS, hSnonempty⟩ := hnotempty
  rcases hSnonempty with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hxInFilter : S ∈ F.filter (fun T => x ∈ T) := by
    simp [hS, hx]
  have hfreqPos : 1 ≤ frequency F x := by
    unfold frequency
    exact Finset.one_le_card.mpr ⟨S, hxInFilter⟩
  have htwo : 2 ≤ 2 * frequency F x := by
    simpa using (Nat.mul_le_mul_left 2 hfreqPos)
  have hbound : F.card ≤ 2 * frequency F x := by
    exact le_trans hcard htwo
  simpa [Abundant] using hbound

end Frankl
end HeytingLean
