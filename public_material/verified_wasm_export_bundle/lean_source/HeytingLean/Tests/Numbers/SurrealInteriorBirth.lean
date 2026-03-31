import HeytingLean.Numbers.Surreal.Nucleus
import HeytingLean.Generative.SurrealNucleusKit

/-
Concrete interior-birth examples for the surreal interior nucleus.

We work with the current `SurrealCore` skeleton and the interior nucleus
`Surreal.intReentry` on `Set PreGame`, and exhibit:

* a "good" set `S_good` whose interior birth is `0` because it is fixed, and
* a "bad" set `S_bad` whose interior birth is `1` because it is not fixed
  but stabilises after one breath.

These examples are local to this test file and do not alter the core
surreal semantics.
-/

namespace HeytingLean.Tests.Numbers
namespace SurrealInteriorBirth

open HeytingLean.Numbers
open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore
open HeytingLean.Generative

open SurrealNucleusKit

/-! ### A non-fixed surreal carrier set with interior birth 1 -/

/-- A concrete pre-game that violates the classical cut legality condition:
it has the null cut as both a left and right option, forcing
`¬ lt nullCut nullCut`. -/
def badGame : PreGame :=
  { L := [nullCut], R := [nullCut], birth := 0 }

lemma badGame_not_legal : ¬ SurrealCore.legal badGame := by
  intro h
  have hlt : SurrealCore.lt nullCut nullCut := by
    -- specialise legality to the unique left and right options
    have := h nullCut (by simp [badGame]) nullCut (by simp [badGame])
    simpa using this
  -- But `le nullCut nullCut` holds at budget `0`, so `lt` cannot hold.
  have hle : SurrealCore.le nullCut nullCut := by
    -- `birth nullCut = 0`, so the comparison runs at budget `0`.
    simp [SurrealCore.le, SurrealCore.leAt, SurrealCore.nullCut]
  have hnot : ¬ SurrealCore.lt nullCut nullCut := by
    unfold SurrealCore.lt
    exact not_not_intro hle
  exact hnot hlt

/-- `badGame` is not in the canonical legal core `Int.C`. -/
lemma badGame_not_in_core : Surreal.Int.C badGame → False := by
  -- Membership in `Int.C` requires legality; this contradicts `badGame_not_legal`.
  intro hC
  have hleg : SurrealCore.legal badGame := hC.1
  exact badGame_not_legal hleg

/-- Carrier for the surreal interior nucleus. -/
abbrev Carrier := Set PreGame

/-- A set concentrating all mass on `badGame`. -/
def S_bad : Carrier := { g | g = badGame }

lemma badGame_mem_S_bad : badGame ∈ S_bad := by
  simp [S_bad]

/-- `S_bad` is not fixed by the interior nucleus: its singleton support
is mapped away from itself, since `badGame ∉ Int.C`. -/
lemma surrealIntReentry_S_bad_ne_self :
    Surreal.surrealIntReentry S_bad ≠ S_bad := by
  intro hEq
  -- Under the alleged equality, `badGame` would lie in the interior image.
  have hIn : badGame ∈ Surreal.surrealIntReentry S_bad := by
    simpa [hEq] using badGame_mem_S_bad
  -- Expand membership via the interior operator: `I S = S ∩ C`.
  change badGame ∈ Surreal.Int.I S_bad at hIn
  rcases hIn with ⟨_, hCore⟩
  -- But `badGame ∉ Int.C`, contradiction.
  exact badGame_not_in_core hCore

/-- Interior birth of `S_bad` is exactly `1`: the singleton is not fixed
by `surrealIntReentry`, but stabilises after a single breath. -/
lemma ibirth_S_bad_one :
    IntNucleusKit.ibirth (R := Surreal.surrealIntReentry) S_bad = 1 := by
  -- Birth is bounded by one for any interior nucleus.
  have h_le_one :
      IntNucleusKit.ibirth (R := Surreal.surrealIntReentry) S_bad ≤ 1 :=
    IntNucleusKit.ibirth_le_one (R := Surreal.surrealIntReentry) (a := S_bad)
  -- It is not zero because `S_bad` is not fixed.
  have h_ne_zero :
      IntNucleusKit.ibirth (R := Surreal.surrealIntReentry) S_bad ≠ 0 := by
    intro h0
    have hfix :
        Surreal.surrealIntReentry S_bad = S_bad := by
      have :=
        (IntNucleusKit.ibirth_eq_zero_iff
          (R := Surreal.surrealIntReentry) (a := S_bad)).mp h0
      exact this
    exact surrealIntReentry_S_bad_ne_self hfix
  -- Show `1 ≤ ibirth` by ruling out the zero case.
  have h_pos : 1 ≤ IntNucleusKit.ibirth (R := Surreal.surrealIntReentry) S_bad := by
    cases h : IntNucleusKit.ibirth (R := Surreal.surrealIntReentry) S_bad with
    | zero =>
        exact (h_ne_zero h).elim
    | succ n =>
        have : 1 ≤ Nat.succ n := Nat.succ_le_succ (Nat.zero_le n)
        simpa [h] using this
  -- Combine `ibirth ≤ 1` and `1 ≤ ibirth` to obtain equality.
  exact le_antisymm h_le_one h_pos

/-- Express the same statement via `SurrealNucleusKit.birth`. -/
lemma birth_S_bad_one :
    SurrealNucleusKit.birth S_bad = 1 := by
  -- `birth` is `ibirth` specialised to `surrealIntReentry`.
  simpa [SurrealNucleusKit.birth] using ibirth_S_bad_one

/-! ### A fixed surreal carrier set with interior birth 0 -/

/-- A "good" set: the canonical legal core `Int.C` itself. -/
def S_good : Carrier := Surreal.Int.C

/-- `S_good` is fixed by the interior nucleus `Int.I`. -/
lemma surrealIntReentry_S_good_eq :
    Surreal.surrealIntReentry S_good = S_good := by
  -- Re-express the goal using the underlying interior operator `Int.I`.
  change Surreal.Int.I S_good = S_good
  -- With `S_good = Int.C`, this is `I C = C ∩ C = C`.
  unfold S_good
  -- Prove set equality by extensionality.
  apply Set.ext
  intro g
  constructor
  · intro hg; exact hg.1
  · intro hC; exact And.intro hC hC

/-- Interior birth (via `IntNucleusKit`) of `S_good` is zero. -/
lemma ibirth_S_good_zero :
    IntNucleusKit.ibirth (R := Surreal.surrealIntReentry) S_good = 0 := by
  have hfix :
      Surreal.surrealIntReentry S_good = S_good :=
    surrealIntReentry_S_good_eq
  exact
    IntNucleusKit.ibirth_eq_zero_of_fixed
      (R := Surreal.surrealIntReentry) (a := S_good) hfix

/-- The interior birth of `S_good` is zero. -/
lemma birth_S_good_zero :
    SurrealNucleusKit.birth S_good = 0 := by
  -- Characterise zero birth via fixed points of the interior operator.
  have hfix :
      Surreal.surrealIntReentry S_good = S_good :=
    surrealIntReentry_S_good_eq
  -- Delegate to the `ibirth` lemma and specialise the alias.
  have := ibirth_S_good_zero
  simpa [SurrealNucleusKit.birth] using this

end SurrealInteriorBirth
end HeytingLean.Tests.Numbers
