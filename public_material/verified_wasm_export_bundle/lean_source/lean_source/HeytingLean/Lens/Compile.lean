/-
  Compilation of lens transformations.

  RT proofs are erased; only forward/backward functions are compiled.
  This module is parameterized by caller-supplied compilation functions.

  Note: HeytingLean's certified compilation pipeline is fragment-based (Nat¹/Nat²).
  Since arbitrary Lean functions cannot be reified without additional reflection
  infrastructure, fragment compilation is exposed as an *attempt* via partial
  compiler hooks.
-/

import HeytingLean.Certified.Basic
import HeytingLean.Erasure.Fragment
import HeytingLean.LambdaIR.Compile
import HeytingLean.LambdaIR.Certified
import HeytingLean.Lens.Certified

namespace HeytingLean
namespace Lens

open HeytingLean.Certified

universe u

/-- Compile a lens to a LambdaIR pair (forward, backward) using provided compiler hooks. -/
def compileLens {α β : Type u} (lens : CertifiedLens α β)
    (compileForward : (α → β) → HeytingLean.LambdaIR.TypedTerm)
    (compileBackward : (β → α) → HeytingLean.LambdaIR.TypedTerm) :
    Certified (HeytingLean.LambdaIR.TypedTerm × HeytingLean.LambdaIR.TypedTerm) (fun _ => True) :=
  ⟨(compileForward lens.forward, compileBackward lens.backward), trivial⟩

/-- Unverified compilation hook that simply returns the compiled pair (no certificate). -/
def compileLensHook {α β : Type u} (lens : CertifiedLens α β)
    (compileForward : (α → β) → HeytingLean.LambdaIR.TypedTerm)
    (compileBackward : (β → α) → HeytingLean.LambdaIR.TypedTerm) :
    HeytingLean.LambdaIR.TypedTerm × HeytingLean.LambdaIR.TypedTerm :=
  (compileForward lens.forward, compileBackward lens.backward)

/-- Attempt fragment-specific compilation using partial compiler hooks. -/
def compileLensFragment {α β : Type u} (lens : CertifiedLens α β)
    (frag : HeytingLean.Erasure.FragmentId)
    (compileForward : (α → β) → HeytingLean.Erasure.FragmentId → Option HeytingLean.LambdaIR.TypedTerm)
    (compileBackward : (β → α) → HeytingLean.Erasure.FragmentId → Option HeytingLean.LambdaIR.TypedTerm) :
    Option (HeytingLean.LambdaIR.TypedTerm × HeytingLean.LambdaIR.TypedTerm) :=
  match compileForward lens.forward frag, compileBackward lens.backward frag with
  | some fwd, some bwd => some (fwd, bwd)
  | _, _ => none

/-! ## Nat¹ certified compilation (MiniC) -/

open HeytingLean.Core
open HeytingLean.LambdaIR

/-- A Nat→Nat lens equipped with Nat¹-fragment LambdaIR implementations. -/
structure Nat1LensIR (lens : CertifiedLens Nat Nat) where
  forwardName : String
  forwardParam : String
  forwardTerm : Term [] (Ty.arrow Ty.nat Ty.nat)
  forwardIsNatFun : NatFunFragment.IsNatFun forwardTerm
  forwardSem :
    ∀ x,
      LambdaIR.evalClosed (Term.app forwardTerm (Term.constNat x)) = lens.forward x

  backwardName : String
  backwardParam : String
  backwardTerm : Term [] (Ty.arrow Ty.nat Ty.nat)
  backwardIsNatFun : NatFunFragment.IsNatFun backwardTerm
  backwardSem :
    ∀ x,
      LambdaIR.evalClosed (Term.app backwardTerm (Term.constNat x)) = lens.backward x

/-- Spec: compiled MiniC forward/backward implement the Lean lens functions. -/
def Nat1LensMiniCSpec (lens : CertifiedLens Nat Nat)
    (forwardName forwardParam backwardName backwardParam : String)
    (p : HeytingLean.MiniC.Fun × HeytingLean.MiniC.Fun) : Prop :=
  p.1.name = forwardName ∧
    p.2.name = backwardName ∧
    (∀ x, HeytingLean.MiniC.runNatFunFrag p.1 forwardParam x = some (lens.forward x)) ∧
    (∀ x, HeytingLean.MiniC.runNatFunFrag p.2 backwardParam x = some (lens.backward x))

/-- Compile a Nat→Nat lens (Nat¹ fragment) to MiniC, with certificate. -/
def Nat1LensIR.compileMiniC {lens : CertifiedLens Nat Nat} (ir : Nat1LensIR lens) :
    Certified (HeytingLean.MiniC.Fun × HeytingLean.MiniC.Fun)
      (Nat1LensMiniCSpec lens
        ir.forwardName ir.forwardParam ir.backwardName ir.backwardParam) := by
  let fwd :=
    HeytingLean.LambdaIR.CertifiedCompile.compileNat1Fun
      ir.forwardName ir.forwardParam (t := ir.forwardTerm) ir.forwardIsNatFun
  let bwd :=
    HeytingLean.LambdaIR.CertifiedCompile.compileNat1Fun
      ir.backwardName ir.backwardParam (t := ir.backwardTerm) ir.backwardIsNatFun
  refine ⟨(fwd.val, bwd.val), ?_⟩
  rcases fwd.ok with ⟨hFName, hFRun⟩
  rcases bwd.ok with ⟨hBName, hBRun⟩
  refine ⟨hFName, hBName, ?_, ?_⟩
  · intro x
    have hx := hFRun x
    have hSem : LambdaIR.eval ir.forwardTerm HeytingLean.Core.baseEnv x = lens.forward x := by
      simpa [LambdaIR.evalClosed, LambdaIR.eval] using ir.forwardSem x
    simpa [hSem] using hx
  · intro x
    have hx := hBRun x
    have hSem : LambdaIR.eval ir.backwardTerm HeytingLean.Core.baseEnv x = lens.backward x := by
      simpa [LambdaIR.evalClosed, LambdaIR.eval] using ir.backwardSem x
    simpa [hSem] using hx

namespace Nat1LensMiniCSpec

theorem forward_sem {lens : CertifiedLens Nat Nat}
    {forwardName forwardParam backwardName backwardParam : String}
    {p : HeytingLean.MiniC.Fun × HeytingLean.MiniC.Fun}
    (h : Nat1LensMiniCSpec lens forwardName forwardParam backwardName backwardParam p) :
    ∀ x, HeytingLean.MiniC.runNatFunFrag p.1 forwardParam x = some (lens.forward x) :=
  h.2.2.1

theorem backward_sem {lens : CertifiedLens Nat Nat}
    {forwardName forwardParam backwardName backwardParam : String}
    {p : HeytingLean.MiniC.Fun × HeytingLean.MiniC.Fun}
    (h : Nat1LensMiniCSpec lens forwardName forwardParam backwardName backwardParam p) :
    ∀ x, HeytingLean.MiniC.runNatFunFrag p.2 backwardParam x = some (lens.backward x) :=
  h.2.2.2

theorem rt1_roundtrip {lens : CertifiedLens Nat Nat}
    {forwardName forwardParam backwardName backwardParam : String}
    {p : HeytingLean.MiniC.Fun × HeytingLean.MiniC.Fun}
    (h : Nat1LensMiniCSpec lens forwardName forwardParam backwardName backwardParam p)
    (hRT : lens.rtLevel = RTLevel.RT1) :
    ∀ x, HeytingLean.MiniC.runNatFunFrag p.2 backwardParam (lens.forward x) = some x := by
  intro x
  have hb := h.backward_sem (x := lens.forward x)
  have hr := lens.rt1_proof hRT x
  simpa [hr] using hb

end Nat1LensMiniCSpec

end Lens
end HeytingLean
