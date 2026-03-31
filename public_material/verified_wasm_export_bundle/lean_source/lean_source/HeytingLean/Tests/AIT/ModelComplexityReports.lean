import HeytingLean.Meta.AIT.ModelComplexity
import HeytingLean.Tests.AIT.BirthBridgeSmoke

/-
Lean-side comparison reports for model complexity profiles.

This module instantiates the generic `ModelComplexity` interface on
two concrete families drawn from the existing AIT/birth-index bridge:

* a Bool interior nucleus (logic-flavoured), and
* the surreal interior nucleus over `Set PreGame` (physics-flavoured
  via the surreal OML carrier).

For each, we define a `ModelComplexity` profile over the Boolean model
index and exhibit a simple Occam-style inequality showing that the
shorter code does not have strictly higher birth complexity.

These are honest, example-level reports: they rely only on fully
proved lemmas from `BirthBridgeSmoke` and the surreal interior tests,
without introducing any axioms.
-/

namespace HeytingLean.Tests.AIT

open HeytingLean.Meta.AIT
open HeytingLean.Generative
open HeytingLean.Numbers
open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore

/-- Logic-flavoured complexity profile: Bool interior nucleus on `Set Bool`. -/
noncomputable def boolLogicComplexity : ModelComplexity Bool :=
  boolIntReentryModelFamily.toModelComplexity

/-- For the Bool interior nucleus, the model with shorter code
(`false`) is no more complex than the longer-code model (`true`)
with respect to both code length and interior birth. -/
noncomputable example :
    (boolLogicComplexity.codeComplexity false <
      boolLogicComplexity.codeComplexity true)
    ∧ boolLogicComplexity.birthComplexity false ≤
      boolLogicComplexity.birthComplexity true := by
  -- Code inequality follows from the existing AIT example.
  have hCode :
      boolIntReentryModelFamily.codeComplexity false <
        boolIntReentryModelFamily.codeComplexity true := by
    -- proved in `BirthBridgeSmoke`
    decide
  -- Birth equalities follow from the interior birth lemmas.
  have hBirth0 :
      boolIntReentryModelFamily.birthComplexity false = 0 := by
    -- `interpret false = S₀`, fixed by `R_bot`.
    have hfix :
        BoolInterior.R_bot
          (boolIntReentryModelFamily.interpret false)
        = boolIntReentryModelFamily.interpret false := by
      simp [boolIntReentryModelFamily, BoolInterior.S₀, BoolInterior.R_bot]
    simpa using
      boolIntReentryModelFamily.birthComplexity_eq_zero_of_fixed
        (m := false) hfix
  have hBirth1 :
      boolIntReentryModelFamily.birthComplexity true = 1 := by
    -- `interpret true = S₁`, whose interior birthday is `1`.
    have :
        IntNucleusKit.ibirth (R := BoolInterior.R_bot)
          (boolIntReentryModelFamily.interpret true) = 1 := by
      simpa [boolIntReentryModelFamily, BoolInterior.S₁, BoolInterior.R_bot] using
        BoolInterior.ibirth_S₁_one
    unfold IntReentryModelFamily.birthComplexity
    simpa [boolIntReentryModelFamily] using this
  -- Package everything through `boolLogicComplexity`.
  refine And.intro ?hcode ?hbirth
  · -- Rewrite to the underlying family inequality.
    simpa [boolLogicComplexity, ReentryModelFamily.toModelComplexity] using hCode
  · -- Rewrite to `0 ≤ 1`.
    -- First transport the birth equalities to the `boolLogicComplexity` façade.
    have hb0C :
        boolLogicComplexity.birthComplexity false = 0 := by
      simpa [boolLogicComplexity, ReentryModelFamily.toModelComplexity] using hBirth0
    have hb1C :
        boolLogicComplexity.birthComplexity true = 1 := by
      simpa [boolLogicComplexity, ReentryModelFamily.toModelComplexity] using hBirth1
    -- Then reduce to the base inequality `0 ≤ 1`.
    have hle0 : (0 : Nat) ≤ 1 := Nat.zero_le _
    have hleC :
        boolLogicComplexity.birthComplexity false ≤
          boolLogicComplexity.birthComplexity true := by
      simpa [hb0C, hb1C] using hle0
    exact hleC

/-- Physics-flavoured complexity profile: surreal interior nucleus on
`Set PreGame`, with models interpreting to the canonical core and a
non-fixed singleton around `badGame`. -/
noncomputable def surrealPhysicsComplexity : ModelComplexity Bool :=
  SurrealInterior.surrealIntReentryModelFamily.toModelComplexity

/-- For the surreal interior nucleus, the model with shorter code
(`false`, interpreting to `S_good`) is no more complex than the
longer-code model (`true`, interpreting to `S_bad`) with respect to
both code length and interior birth. -/
noncomputable example :
    (surrealPhysicsComplexity.codeComplexity false <
      surrealPhysicsComplexity.codeComplexity true)
    ∧ surrealPhysicsComplexity.birthComplexity false ≤
      surrealPhysicsComplexity.birthComplexity true := by
  -- Code inequality is inherited from the Bool code scheme.
  have hCode :
      SurrealInterior.surrealIntReentryModelFamily.codeComplexity false <
        SurrealInterior.surrealIntReentryModelFamily.codeComplexity true := by
    -- proved in `BirthBridgeSmoke`
    decide
  -- Birth equalities are provided by the surreal interior tests.
  have hBirth0 :
      SurrealInterior.surrealIntReentryModelFamily.birthComplexity false = 0 := by
    -- `interpret false = S_good` with `ibirth S_good = 0`.
    have h' :
        IntNucleusKit.ibirth
          (R := Surreal.surrealIntReentry)
          HeytingLean.Tests.Numbers.SurrealInteriorBirth.S_good = 0 := by
      simpa using
        HeytingLean.Tests.Numbers.SurrealInteriorBirth.ibirth_S_good_zero
    unfold IntReentryModelFamily.birthComplexity
    simpa [SurrealInterior.surrealIntReentryModelFamily] using h'
  have hBirth1 :
      SurrealInterior.surrealIntReentryModelFamily.birthComplexity true = 1 := by
    -- `interpret true = S_bad` with `ibirth S_bad = 1`.
    have h' :
        IntNucleusKit.ibirth
          (R := Surreal.surrealIntReentry)
          HeytingLean.Tests.Numbers.SurrealInteriorBirth.S_bad = 1 := by
      simpa using
        HeytingLean.Tests.Numbers.SurrealInteriorBirth.ibirth_S_bad_one
    unfold IntReentryModelFamily.birthComplexity
    simpa [SurrealInterior.surrealIntReentryModelFamily] using h'
  -- Package through `surrealPhysicsComplexity`.
  refine And.intro ?hcode ?hbirth
  · simpa [surrealPhysicsComplexity, IntReentryModelFamily.toModelComplexity] using hCode
  · -- Transport the birth equalities to the `surrealPhysicsComplexity` façade.
    have hb0C :
        surrealPhysicsComplexity.birthComplexity false = 0 := by
      simpa [surrealPhysicsComplexity, IntReentryModelFamily.toModelComplexity] using hBirth0
    have hb1C :
        surrealPhysicsComplexity.birthComplexity true = 1 := by
      simpa [surrealPhysicsComplexity, IntReentryModelFamily.toModelComplexity] using hBirth1
    -- Reduce to `0 ≤ 1`.
    have hle0 : (0 : Nat) ≤ 1 := Nat.zero_le _
    have hleC :
        surrealPhysicsComplexity.birthComplexity false ≤
          surrealPhysicsComplexity.birthComplexity true := by
      simpa [hb0C, hb1C] using hle0
    exact hleC

end HeytingLean.Tests.AIT
