import HeytingLean.ProgramCalculus.Futamura
import HeytingLean.LambdaIR.PartialEval

/-!
# ProgramCalculus.Instances.LambdaIRBoolNat

Concrete instantiation of `ProgramCalculus` for a tiny closed LambdaIR fragment:

* Programs are closed terms of type `Bool → Nat → Nat`.
* Inputs are `(Bool × Nat)`, split as a static Bool + dynamic Nat.
* `Mix` specializes the Bool argument using `HeytingLean.LambdaIR.Term.specializeBoolNatFun`.
-/

namespace HeytingLean
namespace ProgramCalculus
namespace Instances

open HeytingLean.Core
open HeytingLean.LambdaIR

def lambdaIRBoolNatLanguage : Language where
  Program := LambdaIR.Term [] (Ty.arrow Ty.bool (Ty.arrow Ty.nat Ty.nat))
  Input := Bool × Nat
  Output := Nat
  eval := fun program input =>
    let (b, n) := input
    LambdaIR.evalClosed
      (LambdaIR.Term.app
        (LambdaIR.Term.app program (LambdaIR.Term.constBool b))
        (LambdaIR.Term.constNat n))

def lambdaIRBoolNatSplit : SplitInput (Bool × Nat) where
  Static := Bool
  Dynamic := Nat
  pack := fun b n => (b, n)

def lambdaIRBoolNatMix :
    Mix lambdaIRBoolNatLanguage lambdaIRBoolNatSplit where
  Residual := LambdaIR.Term [] (Ty.arrow Ty.nat Ty.nat)
  evalResidual := fun program n =>
    LambdaIR.evalClosed (LambdaIR.Term.app program (LambdaIR.Term.constNat n))
  apply := fun program b =>
    LambdaIR.Term.specializeBoolNatFun program b
  correct := by
    intro program b n
    simpa [lambdaIRBoolNatLanguage, lambdaIRBoolNatSplit] using
      (LambdaIR.Term.eval_specializeBoolNatFun (program := program) (b := b) (n := n))

/-- A tiny “interpreter” term for codes `Bool`: if `true` then add1 else double. -/
def lambdaIRBoolNatInterp : LambdaIR.Term [] (Ty.arrow Ty.bool (Ty.arrow Ty.nat Ty.nat)) :=
  LambdaIR.Term.lam
    (LambdaIR.Term.lam
      (LambdaIR.Term.if_
        (LambdaIR.Term.var (Var.vs Var.vz))
        (LambdaIR.Term.app
          (LambdaIR.Term.app LambdaIR.Term.primAddNat (LambdaIR.Term.var Var.vz))
          (LambdaIR.Term.constNat 1))
        (LambdaIR.Term.app
          (LambdaIR.Term.app LambdaIR.Term.primAddNat (LambdaIR.Term.var Var.vz))
          (LambdaIR.Term.var Var.vz))))

def lambdaIRBoolNatCodeSem (b : Bool) (n : Nat) : Nat :=
  if b then n + 1 else n + n

def lambdaIRBoolNatInterpModel :
    InterpModel lambdaIRBoolNatLanguage lambdaIRBoolNatSplit where
  codeSem := lambdaIRBoolNatCodeSem
  interp := lambdaIRBoolNatInterp
  correct := by
    intro b n
    cases b <;> simp [lambdaIRBoolNatLanguage, lambdaIRBoolNatSplit, lambdaIRBoolNatInterp, lambdaIRBoolNatCodeSem]

end Instances
end ProgramCalculus
end HeytingLean

