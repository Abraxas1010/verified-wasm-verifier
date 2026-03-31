import HeytingLean.Util.VirtualChain
import HeytingLean.Blockchain.Contracts.LeanYulDSL.Compiler

/-!
# Blockchain.Contracts.LeanYulDSL.VirtualPipeline

Systematic reuse of the “virtualization via chains” pattern for the Lean→Yul DSL lane.

Here the hard part is not mathematical coherence, but *pipeline composition / provenance*:
we want to represent “spec → compiled → emitted artifacts” without forcing a single monolithic
end-to-end object.

We do this by:
- introducing a small sum type of pipeline artifacts; and
- tracking pipeline progress as a `VirtualChain` of step witnesses.
-/

namespace HeytingLean.Blockchain.Contracts.LeanYulDSL

open HeytingLean.Util

/-- Pipeline artifacts we can talk about inside Lean. -/
inductive Artifact where
  | spec (s : ContractSpec)
  | compiled (r : CompileResult)
  | yulObjectText (yul : String)
  | solidityText (src : String)
  deriving Repr, DecidableEq

namespace Artifact

def toSolidity (r : CompileResult) : String :=
  solidityWrapperOfParts r.parts r.pragma r.contractName

def toYulObject (r : CompileResult) : String :=
  yulObjectStringOfParts r.parts

end Artifact

/-- One-step transitions in the Lean→Yul DSL lane. -/
def Step : Artifact → Artifact → Prop
  | .spec s, .compiled r => compile s = .ok r
  | .compiled r, .yulObjectText y => y = Artifact.toYulObject r
  | .compiled r, .solidityText src => src = Artifact.toSolidity r
  | _, _ => False

abbrev Pipeline (a b : Artifact) : Type :=
  VirtualChain Step a b

end HeytingLean.Blockchain.Contracts.LeanYulDSL

