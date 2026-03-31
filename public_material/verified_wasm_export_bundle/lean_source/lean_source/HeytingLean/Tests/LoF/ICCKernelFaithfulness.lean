import Lean
import HeytingLean.LoF.ICCKernel.Faithfulness

namespace HeytingLean
namespace Tests
namespace LoF
namespace ICCKernelFaithfulness

open HeytingLean.LoF.ICCKernel
open HeytingLean.LoF.ICCKernel.Lower

def sampleConst : Lean.ConstantInfo :=
  .axiomInfo
    { name := `demoAx
      levelParams := []
      type := .sort (.succ .zero)
      isUnsafe := false }

example : ∃ c, lowerConstantInfo sampleConst = .ok c := by
  exact lowerConstantInfo_total sampleConst

example : NoConstantFallback lowerConstantInfo := by
  exact lowerConstantInfo_respects_noFallback

example : Raise.raiseConstantInfo (Lower.lowerConstantInfoCore sampleConst) = .ok sampleConst := by
  exact Raise.raiseConstantInfo_lowerConstantInfoCore sampleConst

example : InLowerConstantInfoImage sampleConst := by
  exact lowerConstantInfo_mem_image sampleConst

example :
    recoverAndRelowerConstantInfo (Lower.lowerConstantInfoCore sampleConst) =
      .ok (Lower.lowerConstantInfoCore sampleConst) := by
  exact recoverAndRelower_lowerConstantInfoCore_roundTrip sampleConst

example :
    raiseModuleBundle (lowerModuleBundleCore `Demo.Module [sampleConst]) = .ok (`Demo.Module, [sampleConst]) := by
  exact raise_lowerModuleBundleCore_roundTrip `Demo.Module [sampleConst]

example :
    recoverAndRelowerExportedDecl
      { moduleName := Lower.lowerName `Demo.Module, decl := Lower.lowerConstantInfoCore sampleConst } =
      .ok { moduleName := Lower.lowerName `Demo.Module, decl := Lower.lowerConstantInfoCore sampleConst } := by
  exact recoverAndRelower_loweredExportedDecl_roundTrip `Demo.Module sampleConst

end ICCKernelFaithfulness
end LoF
end Tests
end HeytingLean
