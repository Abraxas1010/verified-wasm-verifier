import HeytingLean.ProgramCalculus.Futamura
import HeytingLean.LambdaIR.PartialEval

/-!
# ProgramCalculus.Instances.LambdaIRNatNat

Concrete instantiation of `ProgramCalculus` for a tiny closed LambdaIR fragment:

* Programs are closed terms of type `Nat → Nat → Nat`.
* Inputs are `(Nat × Nat)`, split as a static `Nat` + dynamic `Nat`.
* `Mix` specializes the first Nat argument using `HeytingLean.LambdaIR.Term.specializeNatNatFun`.
-/

namespace HeytingLean
namespace ProgramCalculus
namespace Instances

open HeytingLean.Core
open HeytingLean.LambdaIR

def lambdaIRNatNatLanguage : Language where
  Program := LambdaIR.Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat))
  Input := Nat × Nat
  Output := Nat
  eval := fun program input =>
    let (k, n) := input
    LambdaIR.evalClosed
      (LambdaIR.Term.app
        (LambdaIR.Term.app program (LambdaIR.Term.constNat k))
        (LambdaIR.Term.constNat n))

def lambdaIRNatNatSplit : SplitInput (Nat × Nat) where
  Static := Nat
  Dynamic := Nat
  pack := fun k n => (k, n)

def lambdaIRNatNatMix :
    Mix lambdaIRNatNatLanguage lambdaIRNatNatSplit where
  Residual := LambdaIR.Term [] (Ty.arrow Ty.nat Ty.nat)
  evalResidual := fun program n =>
    LambdaIR.evalClosed (LambdaIR.Term.app program (LambdaIR.Term.constNat n))
  apply := fun program k =>
    LambdaIR.Term.specializeNatNatFun program k
  correct := by
    intro program k n
    simpa [lambdaIRNatNatLanguage, lambdaIRNatNatSplit] using
      (LambdaIR.Term.eval_specializeNatNatFun (program := program) (k := k) (n := n))

/-- A tiny “interpreter” term for codes `Nat`: add the code to the dynamic input. -/
def lambdaIRNatNatInterp : LambdaIR.Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat)) :=
  LambdaIR.Term.lam <|
    LambdaIR.Term.lam <|
      LambdaIR.Term.app
        (LambdaIR.Term.app LambdaIR.Term.primAddNat (LambdaIR.Term.var Var.vz))
        (LambdaIR.Term.var (Var.vs Var.vz))

def lambdaIRNatNatCodeSem (k : Nat) (n : Nat) : Nat :=
  n + k

def lambdaIRNatNatInterpModel :
    InterpModel lambdaIRNatNatLanguage lambdaIRNatNatSplit where
  codeSem := lambdaIRNatNatCodeSem
  interp := lambdaIRNatNatInterp
  correct := by
    intro k n
    simp [lambdaIRNatNatLanguage, lambdaIRNatNatSplit, lambdaIRNatNatInterp, lambdaIRNatNatCodeSem]

end Instances
end ProgramCalculus
end HeytingLean

