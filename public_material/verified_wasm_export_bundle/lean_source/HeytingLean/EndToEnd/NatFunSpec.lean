import HeytingLean.LambdaIR.NatFunFragment
import HeytingLean.LambdaIR.Nat2FunFragment
import HeytingLean.LambdaIR.NatCompileFrag
import HeytingLean.LambdaIR.NatCompileFragCorrectness
import HeytingLean.LambdaIR.Nat2CompileFrag
import HeytingLean.LambdaIR.Nat2CompileFragCorrectness
import HeytingLean.MiniC.Semantics

namespace HeytingLean
namespace EndToEnd

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatCompileFrag
open HeytingLean.LambdaIR.Nat2CompileFrag

/-- End-to-end specification for the nat→nat pipeline. -/
def EndToEndNatSpec (funName paramName : String)
    (f : Nat → Nat)
    (t : Term [] (Ty.arrow Ty.nat Ty.nat)) : Prop :=
  ∀ n,
    runCompiledNatFunFrag funName paramName t n = some (f n)

/-- If a LambdaIR function `t` computes a Lean function `f`, then the
fragment compiler preserves the semantics end-to-end. -/
theorem EndToEndNatSpec_of_IsNatFun
    {funName paramName : String}
    {f : Nat → Nat}
    {t : Term [] (Ty.arrow Ty.nat Ty.nat)}
    (hf :
      ∀ n,
        evalClosed (Term.app t (Term.constNat n)) = f n)
    (ht : IsNatFun t) :
    EndToEndNatSpec funName paramName f t := by
  intro n
  have hSpec :=
    NatCompileFrag.compileNatFunFrag_correct
      (funName := funName) (paramName := paramName) ht
  have hRun := hSpec n
  have hEval :
      eval t baseEnv n = f n := by
    simpa [evalClosed, LambdaIR.eval] using hf n
  have hBridge :
      some (evalClosed (Term.app t (Term.constNat n)))
        = some (f n) := by
    simp [LambdaIR.evalClosed, LambdaIR.eval, hEval]
  have hFinal := hRun.trans hBridge
  simpa [EndToEndNatSpec, runCompiledNatFunFrag] using hFinal

/-- End-to-end specification for the curried nat→nat→nat pipeline. -/
def EndToEndNat2Spec (funName param1 param2 : String)
    (f : Nat → Nat → Nat)
    (t : Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat))) : Prop :=
  ∀ x y,
    runCompiledNat2FunFrag funName param1 param2 t x y
      = some (f x y)

/-- If a LambdaIR `nat → nat → nat` term computes a Lean function `f`,
then the fragment compiler preserves the semantics end-to-end. -/
theorem EndToEndNat2Spec_of_IsNat2Fun
    {funName : String}
    {f : Nat → Nat → Nat}
    {t : Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat))}
    (hf :
      ∀ x y,
        evalClosed
          (Term.app
            (Term.app t (Term.constNat x))
            (Term.constNat y)) = f x y)
    (ht : Nat2FunFragment.IsNat2Fun t) :
    EndToEndNat2Spec funName "x" "y" f t := by
  have hSpec :=
    Nat2CompileFragCorrectness.compileNat2FunFrag_correct
      (funName := funName)
      (ht := ht) (leanF := f) (hf := hf)
  simpa [EndToEndNat2Spec, Nat2FunSpec, runCompiledNat2FunFrag,
        Nat2CompileFragCorrectness.param1, Nat2CompileFragCorrectness.param2] using hSpec

end EndToEnd
end HeytingLean

namespace HeytingLean
namespace EndToEnd
namespace NatFunSpec

/-- Re-export of `EndToEndNatSpec` under the `NatFunSpec` namespace. -/
abbrev EndToEndNatSpec
    (leanF : Nat → Nat) (funName paramName : String)
    (t :
      _root_.HeytingLean.LambdaIR.Term []
        (_root_.HeytingLean.Core.Ty.arrow
          _root_.HeytingLean.Core.Ty.nat
          _root_.HeytingLean.Core.Ty.nat)) :=
  _root_.HeytingLean.EndToEnd.EndToEndNatSpec funName paramName leanF t

/-- Re-export of `EndToEndNatSpec_of_IsNatFun` under the `NatFunSpec` namespace. -/
theorem EndToEndNatSpec_of_IsNatFun
    {leanF : Nat → Nat}
    {funName paramName : String}
    {t :
      _root_.HeytingLean.LambdaIR.Term []
        (_root_.HeytingLean.Core.Ty.arrow
          _root_.HeytingLean.Core.Ty.nat
          _root_.HeytingLean.Core.Ty.nat)}
    (ht :
      _root_.HeytingLean.LambdaIR.NatFunFragment.IsNatFun t)
    (hf :
      ∀ n,
        _root_.HeytingLean.LambdaIR.evalClosed
          (_root_.HeytingLean.LambdaIR.Term.app t
            (_root_.HeytingLean.LambdaIR.Term.constNat n)) = leanF n) :
    EndToEndNatSpec leanF funName paramName t :=
  _root_.HeytingLean.EndToEnd.EndToEndNatSpec_of_IsNatFun hf ht

/-- Re-export of the two-argument end-to-end spec. -/
abbrev EndToEndNat2Spec
    (leanF : Nat → Nat → Nat)
    (funName param1 param2 : String)
    (t : _root_.HeytingLean.LambdaIR.Term []
      (_root_.HeytingLean.Core.Ty.arrow _root_.HeytingLean.Core.Ty.nat
        (_root_.HeytingLean.Core.Ty.arrow _root_.HeytingLean.Core.Ty.nat
          _root_.HeytingLean.Core.Ty.nat))) :=
  _root_.HeytingLean.EndToEnd.EndToEndNat2Spec funName param1 param2 leanF t

/-- Re-export of `EndToEndNat2Spec_of_IsNat2Fun` in the `NatFunSpec` namespace. -/
theorem EndToEndNat2Spec_of_IsNat2Fun
    {leanF : Nat → Nat → Nat}
    {funName : String}
    {t : _root_.HeytingLean.LambdaIR.Term []
        (_root_.HeytingLean.Core.Ty.arrow _root_.HeytingLean.Core.Ty.nat
          (_root_.HeytingLean.Core.Ty.arrow _root_.HeytingLean.Core.Ty.nat
            _root_.HeytingLean.Core.Ty.nat))}
    (ht :
      _root_.HeytingLean.LambdaIR.Nat2FunFragment.IsNat2Fun t)
    (hf :
      ∀ x y,
        _root_.HeytingLean.LambdaIR.evalClosed
          (_root_.HeytingLean.LambdaIR.Term.app
            (_root_.HeytingLean.LambdaIR.Term.app t
              (_root_.HeytingLean.LambdaIR.Term.constNat x))
            (_root_.HeytingLean.LambdaIR.Term.constNat y))
            = leanF x y) :
    EndToEndNat2Spec leanF funName "x" "y" t :=
  _root_.HeytingLean.EndToEnd.EndToEndNat2Spec_of_IsNat2Fun hf ht

end NatFunSpec
end EndToEnd
end HeytingLean
