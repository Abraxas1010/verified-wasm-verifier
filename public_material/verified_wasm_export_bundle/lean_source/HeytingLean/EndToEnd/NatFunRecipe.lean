import HeytingLean.Core.Types
import HeytingLean.EndToEnd.NatFunSpec
import HeytingLean.LeanCoreV2.Semantics
import HeytingLean.LeanCoreV2.Syntax
import HeytingLean.LeanCoreV2.ToLambdaIR
import HeytingLean.LambdaIR.NatFunFragment
import HeytingLean.LambdaIR.Semantics
import HeytingLean.LambdaIR.Syntax

namespace HeytingLean
namespace EndToEnd
namespace NatFunRecipe

open HeytingLean.Core
open HeytingLean.EndToEnd
open HeytingLean.LeanCoreV2
open HeytingLean.LeanCoreV2.ToLambdaIR
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment

/-- Data required to prove an end-to-end certificate for a nat→nat function. -/
structure NatFunPipelineWitness where
  funName : String
  paramName : String
  f : Nat → Nat
  tLC : LeanCoreV2.Term [] (Ty.arrow Ty.nat Ty.nat)
  tIR : LambdaIR.Term [] (Ty.arrow Ty.nat Ty.nat)
  tIR_eq : tIR = translateTerm tLC
  sem_Lean :
    ∀ n,
      LeanCoreV2.evalClosed
        (LeanCoreV2.Term.app tLC (LeanCoreV2.Term.constNat n)) = f n
  isNatFun : LambdaIR.IsNatFun tIR

/-- Use bundled witnesses to obtain an end-to-end NatFunSpec. -/
def certify (w : NatFunPipelineWitness) :
    EndToEndNatSpec w.funName w.paramName w.f w.tIR := by
  refine EndToEndNatSpec_of_IsNatFun ?_ w.isNatFun
  intro n
  have htrans :=
    translate_eval_closed
      (LeanCoreV2.Term.app w.tLC (LeanCoreV2.Term.constNat n))
  have hlean := w.sem_Lean n
  simpa [translateTerm, w.tIR_eq.symm] using htrans.trans hlean

end NatFunRecipe
end EndToEnd
end HeytingLean
