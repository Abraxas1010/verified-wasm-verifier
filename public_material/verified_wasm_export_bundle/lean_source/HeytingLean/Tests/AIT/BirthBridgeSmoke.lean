import HeytingLean.Meta.AIT.BirthBridge
import HeytingLean.Tests.Plausibility
import HeytingLean.Numbers.Surreal.ReentryLoF
import HeytingLean.Generative.SurrealNucleusKit
import HeytingLean.Tests.Numbers.SurrealInteriorBirth

/-
Compile-time smoke tests for the bridge between code-length
complexity and birth index.  We instantiate a trivial
`ReentryModelFamily` using the boolean reentry nucleus from the
plausibility tests and check that the combined structure and basic
lemmas type-check.
-/

namespace HeytingLean.Tests.AIT

open HeytingLean.Meta.AIT
open HeytingLean.Epistemic
open HeytingLean.LoF
open HeytingLean.Numbers
open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore
open HeytingLean.Generative

noncomputable def boolReentryModelFamily : ReentryModelFamily (α := Set Bool)
    (M := Unit) (D := Unit) (O := Unit) :=
  { R        := HeytingLean.Tests.reentryBool
    family   :=
      { models     := [Unit.unit]
        code       := fun _ => [true]
        predict    := fun _ _ => ()
        consistent := fun _ _ => true }
    interpret := fun _ => (Set.univ : Set Bool) }

noncomputable def boolReentryModelFamily' :
    ReentryModelFamily (α := Set Bool) (M := Unit) (D := Unit) (O := Unit) :=
  boolReentryModelFamily

-- Basic checks: the combined complexity profiles are well-typed.
noncomputable example : Nat :=
  boolReentryModelFamily.codeComplexity ()

noncomputable example : Nat :=
  boolReentryModelFamily.birthComplexity ()

/-
A surreal instantiation: we use the LoF-style surreal reentry nucleus
`Numbers.Surreal.surrealReentry` on the carrier `Set PreGame` together
with a finite model family whose codes have different lengths.  Since
the surreal reentry nucleus is the identity closure, every interpreted
element is fixed and therefore has birth complexity zero, but the
code-length complexity still separates models.
-/

abbrev SurrealCarrier := Set SurrealCore.PreGame

noncomputable def surrealModelFamily :
    ModelFamily (M := Bool) (D := Unit) (O := Unit) where
  models     := [false, true]
  code       := fun b => if b then [true, false] else [false]
  predict    := fun _ _ => ()
  consistent := fun _ _ => true

noncomputable def surrealReentryModelFamily :
    ReentryModelFamily (α := SurrealCarrier)
        (M := Bool) (D := Unit) (O := Unit) :=
  { R        := Numbers.Surreal.surrealReentry
    family   := surrealModelFamily
    interpret := fun b =>
      if b then (Quantum.SurrealOML.canonicalCoreSet : SurrealCarrier)
           else (Quantum.SurrealOML.nullCutSet : SurrealCarrier) }

-- Code-length complexity distinguishes the two surreal models.
noncomputable example :
    surrealReentryModelFamily.codeComplexity false <
      surrealReentryModelFamily.codeComplexity true := by
  -- `false` is encoded as `[false]` (length 1), `true` as `[true, false]` (length 2).
  decide

-- Birth complexity is zero for both models because the surreal reentry nucleus is identity.
noncomputable example :
    surrealReentryModelFamily.birthComplexity false = 0 := by
  -- Every set is fixed by `surrealReentry`.
  have hfix :
      surrealReentryModelFamily.R
          (surrealReentryModelFamily.interpret false)
        = surrealReentryModelFamily.interpret false := by
    simp [surrealReentryModelFamily, Numbers.Surreal.surrealReentry]
  simpa using
    surrealReentryModelFamily.birthComplexity_eq_zero_of_fixed
      (m := false) hfix

noncomputable example :
    surrealReentryModelFamily.birthComplexity true = 0 := by
  have hfix :
      surrealReentryModelFamily.R
          (surrealReentryModelFamily.interpret true)
        = surrealReentryModelFamily.interpret true := by
    simp [surrealReentryModelFamily, Numbers.Surreal.surrealReentry]
  simpa using
    surrealReentryModelFamily.birthComplexity_eq_zero_of_fixed
      (m := true) hfix

/-
Interior Bool nucleus: we now build an `IntReentryModelFamily` over a simple
interior nucleus on `Set Bool` and exhibit two models with different interior
birth complexities, aligned with their code lengths.
-/

namespace BoolInterior

open HeytingLean.LoF
open Set

noncomputable local instance : PrimaryAlgebra (Set Bool) :=
  { toFrame := inferInstance }

/-- Constant-bottom interior nucleus on `Set Bool`. -/
def R_bot : IntReentry (Set Bool) where
  nucleus :=
    { act := fun _ => (⊥ : Set Bool)
      monotone := by
        intro S T h
        exact (bot_le : (⊥ : Set Bool) ≤ (⊥ : Set Bool))
      idempotent := by
        intro S; rfl
      apply_le := by
        intro S
        exact (bot_le : (⊥ : Set Bool) ≤ S)
      map_inf := by
        intro S T; ext x; simp }

/-- Carrier for the Bool interior nucleus. -/
abbrev Carrier := Set Bool

/-- Two simple carrier sets: empty and singleton `{true}`. -/
def S₀ : Carrier := (⊥ : Set Bool)
def S₁ : Carrier := {b : Bool | b = true}

lemma R_bot_S₀_fixed : R_bot S₀ = S₀ := by
  rfl

lemma R_bot_S₁_not_fixed : R_bot S₁ ≠ S₁ := by
  -- `R_bot S₁ = ⊥`, while `S₁` contains `true`.
  intro h
  have hTrue : (true : Bool) ∈ S₁ := by
    simp [S₁]
  -- Rewrite `R_bot S₁` to `⊥` in the equality.
  have h' : (⊥ : Set Bool) = S₁ := by
    simpa [R_bot, S₁] using h
  -- Transport membership of `true` along `h'`.
  have hFalse : (true : Bool) ∈ (⊥ : Set Bool) := by
    simpa [h'] using hTrue
  -- But `true` cannot belong to `⊥`.
  simpa using hFalse

/-- Interior birth of `S₀` is zero (fixed point). -/
lemma ibirth_S₀_zero :
    IntNucleusKit.ibirth (R := R_bot) S₀ = 0 := by
  have := IntNucleusKit.ibirth_eq_zero_of_fixed
    (R := R_bot) (a := S₀) (h := R_bot_S₀_fixed)
  simpa using this

/-- Interior birth of `S₁` is one: it is not fixed, but stabilises after
one breath under the constant-bottom nucleus. -/
lemma ibirth_S₁_one :
    IntNucleusKit.ibirth (R := R_bot) S₁ = 1 := by
  -- Birth is bounded by one for any interior nucleus.
  have h_le_one :
      IntNucleusKit.ibirth (R := R_bot) S₁ ≤ 1 :=
    IntNucleusKit.ibirth_le_one (R := R_bot) (a := S₁)
  -- It is not zero because `S₁` is not fixed.
  have h_ne_zero :
      IntNucleusKit.ibirth (R := R_bot) S₁ ≠ 0 := by
    intro h0
    have hfix :
        R_bot S₁ = S₁ := by
      have :=
        (IntNucleusKit.ibirth_eq_zero_iff
          (R := R_bot) (a := S₁)).mp h0
      exact this
    exact R_bot_S₁_not_fixed hfix
  -- Show `1 ≤ ibirth` by ruling out the zero case.
  have h_pos : 1 ≤ IntNucleusKit.ibirth (R := R_bot) S₁ := by
    cases h : IntNucleusKit.ibirth (R := R_bot) S₁ with
    | zero =>
        exact (h_ne_zero h).elim
    | succ n =>
        have : 1 ≤ Nat.succ n := Nat.succ_le_succ (Nat.zero_le n)
        simpa [h] using this
  -- Combine `ibirth ≤ 1` and `1 ≤ ibirth` to obtain equality.
  exact le_antisymm h_le_one h_pos

end BoolInterior

open BoolInterior

/-- Interior Bool model family: two models with different codes and
different interior birth complexities under `R_bot`. -/
noncomputable def boolIntReentryModelFamily :
    IntReentryModelFamily (α := BoolInterior.Carrier)
        (M := Bool) (D := Unit) (O := Unit) :=
  { R        := R_bot
    family   :=
      { models     := [false, true]
        code       := fun b => if b then [true, false] else [false]
        predict    := fun _ _ => ()
        consistent := fun _ _ => true }
    interpret := fun b => if b then S₁ else S₀ }

-- Code-length complexity prefers the `false` model (shorter code).
noncomputable example :
    boolIntReentryModelFamily.codeComplexity false <
      boolIntReentryModelFamily.codeComplexity true := by
  decide

-- Interior birth is `0` for `S₀` and `1` for `S₁`.
noncomputable example :
    boolIntReentryModelFamily.birthComplexity false = 0 := by
  -- `interpret false = S₀`, fixed by `R_bot`.
  have hfix :
      R_bot (boolIntReentryModelFamily.interpret false)
        = boolIntReentryModelFamily.interpret false := by
    simp [boolIntReentryModelFamily, S₀, R_bot]
  simpa using
    boolIntReentryModelFamily.birthComplexity_eq_zero_of_fixed
      (m := false) hfix

noncomputable example :
    boolIntReentryModelFamily.birthComplexity true = 1 := by
  -- `interpret true = S₁`, whose interior birthday is `1`.
  have :
      IntNucleusKit.ibirth (R := R_bot)
        (boolIntReentryModelFamily.interpret true) = 1 := by
    simpa [boolIntReentryModelFamily, S₁, R_bot] using
      ibirth_S₁_one
  unfold IntReentryModelFamily.birthComplexity
  simpa [boolIntReentryModelFamily] using this

/-!
Surreal interior nucleus: we reuse the finite Bool model family
`surrealModelFamily` but interpret models as the surreal carrier sets
`S_good` and `S_bad` from `SurrealInteriorBirth`. This yields a genuinely
nontrivial birth-vs-code inequality for the surreal interior nucleus.
-/

namespace SurrealInterior

open HeytingLean.Tests.Numbers
open HeytingLean.Tests.Numbers.SurrealInteriorBirth

/-- Interior surreal model family: two models with different codes and
different interior birth complexities under `surrealIntReentry`. -/
noncomputable def surrealIntReentryModelFamily :
    IntReentryModelFamily (α := SurrealCarrier)
        (M := Bool) (D := Unit) (O := Unit) :=
  { R        := Surreal.surrealIntReentry
    family   := surrealModelFamily
    interpret := fun b =>
      if b then S_bad else S_good }

-- Code-length complexity again prefers the `false` model (shorter code).
noncomputable example :
    surrealIntReentryModelFamily.codeComplexity false <
      surrealIntReentryModelFamily.codeComplexity true := by
  decide

-- Interior birth is `0` for `S_good` and `1` for `S_bad`.
noncomputable example :
    surrealIntReentryModelFamily.birthComplexity false = 0 := by
  -- `interpret false = S_good`, fixed by the interior nucleus.
  have h :
      IntNucleusKit.ibirth (R := Surreal.surrealIntReentry) S_good = 0 := by
    simpa using ibirth_S_good_zero
  unfold IntReentryModelFamily.birthComplexity
  simpa [surrealIntReentryModelFamily] using h

noncomputable example :
    surrealIntReentryModelFamily.birthComplexity true = 1 := by
  -- `interpret true = S_bad`, whose interior birthday is `1`.
  have h :
      IntNucleusKit.ibirth (R := Surreal.surrealIntReentry) S_bad = 1 := by
    simpa using ibirth_S_bad_one
  unfold IntReentryModelFamily.birthComplexity
  simpa [surrealIntReentryModelFamily] using h

/-! A combined Occam-style inequality: shorter code, no higher birth. -/

noncomputable example :
    surrealIntReentryModelFamily.codeComplexity false <
      surrealIntReentryModelFamily.codeComplexity true
    ∧ surrealIntReentryModelFamily.birthComplexity false ≤
      surrealIntReentryModelFamily.birthComplexity true := by
  refine And.intro ?hcode ?hbirth
  · -- Code inequality: reuse the earlier `decide` proof.
    have hcode' :
        surrealIntReentryModelFamily.codeComplexity false <
          surrealIntReentryModelFamily.codeComplexity true := by
      decide
    exact hcode'
  · -- Birth inequality: `0 = birth false ≤ birth true = 1`.
    -- First reuse the explicit birth equalities we just proved.
    have hb0 :
        surrealIntReentryModelFamily.birthComplexity false = 0 := by
      -- `interpret false = S_good` and `ibirth S_good = 0`.
      have h' :
          IntNucleusKit.ibirth
            (R := Surreal.surrealIntReentry) S_good = 0 := by
        simpa using ibirth_S_good_zero
      unfold IntReentryModelFamily.birthComplexity
      simpa [surrealIntReentryModelFamily] using h'
    have hb1 :
        surrealIntReentryModelFamily.birthComplexity true = 1 := by
      -- `interpret true = S_bad` and `ibirth S_bad = 1`.
      have h' :
          IntNucleusKit.ibirth
            (R := Surreal.surrealIntReentry) S_bad = 1 := by
        simpa using ibirth_S_bad_one
      unfold IntReentryModelFamily.birthComplexity
      simpa [surrealIntReentryModelFamily] using h'
    -- Now rewrite the goal to `0 ≤ 1`.
    have hle : (0 : Nat) ≤ 1 := Nat.zero_le _
    simpa [hb0, hb1] using hle

end SurrealInterior

end HeytingLean.Tests.AIT
