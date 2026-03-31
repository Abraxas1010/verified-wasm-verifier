import HeytingLean.LoF.Bauer.ScottReflexiveDomain
import HeytingLean.LoF.BoundaryHeyting
import HeytingLean.LoF.Bauer.LawvereFixedPoint
import HeytingLean.LoF.Bauer.LawvereCategorical
import HeytingLean.LoF.Combinators.Denotational
import HeytingLean.Numbers.Surreal.BridgeToPGame
import HeytingLean.Numbers.Surreal.BridgeToPGamePreservation
import HeytingLean.Numbers.Surreal.BridgeToFGame
import HeytingLean.Numbers.Surreal.BoundaryLogic
import HeytingLean.Numbers.Surreal.LoFDerivation
import HeytingLean.LoF.Combinators.EigenformBridge
import HeytingLean.Topos.DimensionalRatchet
import HeytingLean.Topos.DimensionalRatchetTranslate

/-!
# UnifiedMathSanity

Compile-time sanity checks for the “unified mathematics” integration layers:

* Scott-style reflexive domain interface + fixed point operator (`scottFix`)
* Explicit “boundary → Heyting” packaging (`BoundaryHeyting`)
* Explicit bridge from `SurrealCore.PreGame` to CGT `IGame`
* Executable bridge from `SurrealCore.PreGame` to CGT `FGame`
* Surreal `{L|R}` as LoF distinction data (`LoFDerivation`)
* Eigenform/self-application bridge for SKY combinators (`EigenformBridge`)
* Dimensional ratchet interfaces (`DimensionalRatchet`)
-/

namespace HeytingLean.Tests.UnifiedMathSanity

open HeytingLean.LoF
open HeytingLean.Numbers

-- Scott fixed point operator exists and has the expected type.
#check HeytingLean.LoF.Bauer.scottFix
#check HeytingLean.LoF.Bauer.scottFix_isFixed
#check HeytingLean.LoF.Bauer.ReflexiveDomain

-- Lawvere fixed-point theorem exists (Type/Set-level core).
#check HeytingLean.LoF.Bauer.Lawvere.PointSurjective
#check HeytingLean.LoF.Bauer.Lawvere.exists_fixedPoint_of_pointSurjective

-- Lawvere fixed-point theorem exists (categorical CCC form).
#check HeytingLean.LoF.Bauer.LawvereCategorical.WeaklyPointSurjective
#check HeytingLean.LoF.Bauer.LawvereCategorical.exists_fixedPoint_of_weaklyPointSurjective

-- Boundary packaging exists.
#check HeytingLean.LoF.BoundaryHeyting.boundary
#check HeytingLean.LoF.BoundaryHeyting.boundary_isLeast

-- Surreal bridge exists.
#check HeytingLean.Numbers.SurrealCore.PreGame.toIGame
#check HeytingLean.Numbers.SurrealCore.PreGame.toFGame

-- SurrealCore → IGame preservation (structural Conway operations).
#check HeytingLean.Numbers.SurrealCore.PreGame.negConway
#check HeytingLean.Numbers.SurrealCore.PreGame.addConway
#check HeytingLean.Numbers.SurrealCore.PreGame.toIGame_negConway
#check HeytingLean.Numbers.SurrealCore.PreGame.toIGame_addConway
#check HeytingLean.Numbers.SurrealCore.PreGame.toIGame_neg
#check HeytingLean.Numbers.SurrealCore.PreGame.toIGame_add
#check HeytingLean.Numbers.SurrealCore.PreGame.toIGame_add_comm
#check HeytingLean.Numbers.SurrealCore.PreGame.toIGame_add_assoc
#check HeytingLean.Numbers.SurrealCore.PreGame.toIGame_add_left_neg_equiv_zero
#check HeytingLean.Numbers.SurrealCore.PreGame.toIGame_add_left_cancel_equiv
#check HeytingLean.Numbers.SurrealCore.PreGame.toIGame_add_right_cancel_equiv
#check HeytingLean.Numbers.SurrealCore.mul_nullCut_left
#check HeytingLean.Numbers.SurrealCore.mul_nullCut_right
#check HeytingLean.Numbers.SurrealCore.PreGame.toIGame_mul_nullCut_left
#check HeytingLean.Numbers.SurrealCore.PreGame.toIGame_mul_nullCut_right
#check HeytingLean.Numbers.Surreal.canonical_boundary_idem
#check HeytingLean.Numbers.Surreal.fin3_impossible_one
#check HeytingLean.Numbers.Surreal.fin3_one_has_no_complement
#check HeytingLean.Numbers.Surreal.fin3Prod_impossible_mid
#check HeytingLean.Numbers.Surreal.fin3Prod_mid_has_no_complement

-- Surreal `{L|R}` as LoF distinction data.
#check HeytingLean.Numbers.Surreal.LoFDerivation.GameDistinction
#check HeytingLean.Numbers.Surreal.LoFDerivation.GameDistinction.distinction_pregame_equiv
#check HeytingLean.Numbers.Surreal.LoFDerivation.void_is_zero

-- SKY eigenform bridge.
#check HeytingLean.LoF.Combinators.EigenformBridge.Y_eigenform
#check HeytingLean.LoF.Combinators.EigenformBridge.gremlin_fixedpoint

-- Denotational semantics interface and soundness.
#check HeytingLean.LoF.Combinators.SKYModel
#check HeytingLean.LoF.Combinators.SKYModel.denote_steps

-- Dimensional ratchet (interfaces + Sasaki idempotence + Boolean core).
#check HeytingLean.Topos.DimensionalRatchet.LogicDimension
#check HeytingLean.Topos.DimensionalRatchet.Magmatic.toHeytingCore
#check HeytingLean.Topos.DimensionalRatchet.Sasaki.proj_idempotent
#check HeytingLean.Topos.DimensionalRatchet.Bauer.classicalCoreBoolean

-- Concrete OML → Heyting transport via the translation layer.
#check HeytingLean.Topos.DimensionalRatchet.Interface.omlToHeyting_ofTranslate
#check HeytingLean.Topos.DimensionalRatchet.Interface.sasakiHook_le_himp_in_omega

end HeytingLean.Tests.UnifiedMathSanity
