import HeytingLean.Ontology.CoinductiveBounded

/-!
# Tests.Ontology.CoinductiveBoundedSKYCompilationSanity

Compile-time sanity checks for the SKY compilation routing tranche.
-/

namespace HeytingLean.Tests.Ontology

open HeytingLean.Ontology.CoinductiveBounded

#check SkyBackendTag
#check StagedLeanCarrier
#check stageLeanExpr
#check cpuKernelRoute
#check gpuWrapperRoute
#check hybridZeckendorfRoute
#check signedNafRoute

example : (cpuKernelRoute 32).backend = .cpuSky := by
  rfl

example : (gpuWrapperRoute 32).backend = .gpuSky := by
  rfl

example : (hybridZeckendorfRoute 32).backend = .hybridZeckendorf := by
  rfl

example : (signedNafRoute 32).backend = .signedNaf := by
  rfl

example : (compileToCpuState? 32 stagedNatThree).isSome = true := by
  native_decide

example : (compileToKernelState? 32 stagedNatThree).isSome = true := by
  native_decide

example : (compileToGpuWrapper? 32 stagedNatThree).isSome = true := by
  native_decide

example : (compileToSignedNaf? 32 stagedNatThree).isSome = true := by
  native_decide

example :
    Option.map HeytingLean.Bridge.Veselov.HybridZeckendorf.eval
        (compileToHybridZeckendorf? 32 stagedNatThree) =
      Option.map (fun s => s.nodes.size) (compileToCpuState? 32 stagedNatThree) := by
  simpa using hybridZeckendorf_route_preserves_nodesUsed 32 stagedNatThree

example :
    Option.map kernelFootprint (compileToKernelState? 32 stagedAppNat) =
      Option.map (fun s => cpuFootprint s 32) (compileToCpuState? 32 stagedAppNat) := by
  simpa using kernel_route_preserves_cpu_footprint 32 stagedAppNat

example : SignedNaf.ofNat 3 = [.negOne, .zero, .posOne] := by
  native_decide

example : SignedNaf.eval (SignedNaf.ofNat 3) = 3 := by
  native_decide

example : SignedNaf.eval (SignedNaf.ofNat 5) = 5 := by
  native_decide

end HeytingLean.Tests.Ontology
