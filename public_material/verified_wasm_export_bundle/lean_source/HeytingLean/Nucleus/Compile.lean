/-
  Compilation for nucleus operators.

  Background:
  - `CertifiedNucleus X` is Mathlib's `Nucleus X` (an inflationary, idempotent,
    inf-preserving endomorphism).
  - HeytingLean's certified compilation pipeline is currently fragment-based:
    it can compile *LambdaIR terms* in the Nat¹ / Nat² fragments into MiniC,
    with proven semantic preservation (fragment runner correctness).

  Consequently:
  - For arbitrary nuclei `X → X`, we only expose an *unverified* compilation hook.
  - For nuclei on `Nat` whose operator is *implemented by a Nat¹ LambdaIR term*,
    we provide a certified compilation into MiniC, and derived preservation of
    the nucleus laws at the MiniC fragment semantics level.
-/

import HeytingLean.Certified.Basic
import HeytingLean.LambdaIR.Certified
import HeytingLean.LambdaIR.Compile
import HeytingLean.MiniC.ToCCorrectness
import HeytingLean.Nucleus.Certified

namespace HeytingLean
namespace Nucleus

open HeytingLean.Certified

universe u

/-- Unverified compilation hook for arbitrary nuclei: callers provide a backend `compileOp`. -/
def compileNucleusHook {X : Type u} [SemilatticeInf X]
    (n : CertifiedNucleus X)
    (compileOp : (X → X) → HeytingLean.LambdaIR.TypedTerm) : HeytingLean.LambdaIR.TypedTerm :=
  compileOp n

/-! ## Nat¹ certified compilation -/

open HeytingLean.Core
open HeytingLean.LambdaIR

/-- A Nat nucleus equipped with a Nat¹-fragment LambdaIR implementation. -/
structure Nat1NucleusIR (n : CertifiedNucleus Nat) where
  funName : String
  paramName : String
  term : Term [] (Ty.arrow Ty.nat Ty.nat)
  isNatFun : NatFunFragment.IsNatFun term
  sem :
    ∀ x,
      LambdaIR.evalClosed (Term.app term (Term.constNat x)) = n x

/-- Spec: a MiniC fragment function implements a Nat nucleus. -/
def Nat1NucleusMiniCSpec (n : CertifiedNucleus Nat) (funName paramName : String)
    (f : HeytingLean.MiniC.Fun) : Prop :=
  f.name = funName ∧
    ∀ x, HeytingLean.MiniC.runNatFunFrag f paramName x = some (n x)

/-- Compile a Nat nucleus (given as a Nat¹ LambdaIR term) to MiniC, with certificate. -/
def Nat1NucleusIR.compileMiniC {n : CertifiedNucleus Nat} (ir : Nat1NucleusIR n) :
    Certified HeytingLean.MiniC.Fun (Nat1NucleusMiniCSpec n ir.funName ir.paramName) := by
  let compiled :=
    HeytingLean.LambdaIR.CertifiedCompile.compileNat1Fun
      ir.funName ir.paramName (t := ir.term) ir.isNatFun
  refine ⟨compiled.val, ?_⟩
  rcases compiled.ok with ⟨hName, hRun⟩
  refine ⟨hName, ?_⟩
  intro x
  have hx := hRun x
  have hSem : LambdaIR.eval ir.term HeytingLean.Core.baseEnv x = n x := by
    simpa [LambdaIR.evalClosed, LambdaIR.eval] using ir.sem x
  simpa [hSem] using hx

/-- Spec: a compiled tiny-C function implements a Nat nucleus on integer inputs/outputs. -/
def Nat1NucleusCSpec (n : CertifiedNucleus Nat) (funName : String)
    (f : HeytingLean.C.CFun) : Prop :=
  f.name = funName ∧
    ∀ x : Nat, HeytingLean.C.runCFunFrag f [(x : Int)] = some (Int.ofNat (n x))

/-- Compile a Nat nucleus all the way to the tiny-C AST, with fragment-runner correctness. -/
def Nat1NucleusIR.compileC {n : CertifiedNucleus Nat} (ir : Nat1NucleusIR n) :
    Certified HeytingLean.C.CFun (Nat1NucleusCSpec n ir.funName) := by
  let minic := ir.compileMiniC
  let cfun := HeytingLean.MiniC.ToC.compileFun minic.val
  refine ⟨cfun, ?_⟩
  rcases minic.ok with ⟨hName, hRun⟩
  refine ⟨by simpa [HeytingLean.MiniC.ToC.compileFun] using hName, ?_⟩
  intro x
  have hC :=
    HeytingLean.MiniC.ToC.runNatFunFrag_correct_toC
      (fn := minic.val) (paramName := ir.paramName) (n := x) (out := n x) (h := hRun x)
  simpa [HeytingLean.MiniC.ToC.compileFun] using hC

/-- Totalized Nat runner (defaults to `0` on `none`). -/
def runNatFunFrag! (f : HeytingLean.MiniC.Fun) (paramName : String) (n : Nat) : Nat :=
  Option.getD (HeytingLean.MiniC.runNatFunFrag f paramName n) 0

namespace Nat1NucleusMiniCSpec

theorem sem {n : CertifiedNucleus Nat} {funName paramName : String} {f : HeytingLean.MiniC.Fun}
    (h : Nat1NucleusMiniCSpec n funName paramName f) :
    ∀ x, HeytingLean.MiniC.runNatFunFrag f paramName x = some (n x) :=
  h.2

theorem run!_eq {n : CertifiedNucleus Nat} {funName paramName : String} {f : HeytingLean.MiniC.Fun}
    (h : Nat1NucleusMiniCSpec n funName paramName f) :
    ∀ x, runNatFunFrag! f paramName x = n x := by
  intro x
  simp [runNatFunFrag!, h.sem x]

theorem extensive {n : CertifiedNucleus Nat} {funName paramName : String} {f : HeytingLean.MiniC.Fun}
    (h : Nat1NucleusMiniCSpec n funName paramName f) :
    ∀ x, x ≤ runNatFunFrag! f paramName x := by
  intro x
  simpa [h.run!_eq (x := x)] using (_root_.Nucleus.le_apply (n := n) (x := x))

theorem monotone {n : CertifiedNucleus Nat} {funName paramName : String} {f : HeytingLean.MiniC.Fun}
    (h : Nat1NucleusMiniCSpec n funName paramName f) :
    Monotone (fun x => runNatFunFrag! f paramName x) := by
  intro a b hab
  simpa [h.run!_eq (x := a), h.run!_eq (x := b)] using (_root_.Nucleus.monotone (n := n) hab)

theorem idempotent {n : CertifiedNucleus Nat} {funName paramName : String} {f : HeytingLean.MiniC.Fun}
    (h : Nat1NucleusMiniCSpec n funName paramName f) :
    ∀ x, runNatFunFrag! f paramName (runNatFunFrag! f paramName x) = runNatFunFrag! f paramName x := by
  intro x
  -- Rewrite the fragment runner into the underlying nucleus, then apply nucleus idempotence.
  rw [h.run!_eq (x := x)]
  rw [h.run!_eq (x := n x)]
  exact _root_.Nucleus.idempotent (n := n) x

end Nat1NucleusMiniCSpec

end Nucleus
end HeytingLean
