import HeytingLean.Blockchain.Contracts.LeanYulDSL.VirtualPipeline

/-!
# Tests.Blockchain.LeanYulDSLVirtualPipelineSanity

Compile-only checks that the Lean→Yul DSL lane can track compilation/emission as a `VirtualChain`.
-/

namespace HeytingLean.Tests.Blockchain

open HeytingLean.Blockchain.Contracts.LeanYulDSL
open HeytingLean.Util

def ownerSpec : ContractSpec :=
  { params := .owner }

def ownerResult : CompileResult :=
  { spec := ownerSpec
    contractName := "Owner"
    pragma := ownerSpec.pragma
    parts := ownerParts }

theorem compile_ownerSpec : compile ownerSpec = .ok ownerResult := by
  rfl

def ownerSolidity : String :=
  Artifact.toSolidity ownerResult

def ownerPipeline :
    Pipeline (Artifact.spec ownerSpec) (Artifact.solidityText ownerSolidity) :=
  HeytingLean.Util.VirtualChain.cons (Step := Step)
    (a := Artifact.spec ownerSpec)
    (b := Artifact.compiled ownerResult)
    (c := Artifact.solidityText ownerSolidity)
    compile_ownerSpec
    (HeytingLean.Util.VirtualChain.cons (Step := Step)
      (a := Artifact.compiled ownerResult)
      (b := Artifact.solidityText ownerSolidity)
      (c := Artifact.solidityText ownerSolidity)
      rfl
      (HeytingLean.Util.VirtualChain.nil (Step := Step) (Artifact.solidityText ownerSolidity)))

#check ownerPipeline

end HeytingLean.Tests.Blockchain
