import HeytingLean.LoF.ICC.Syntax
import HeytingLean.LoF.ICC.Encodings
import HeytingLean.LoF.ICC.Reduction
import HeytingLean.LoF.ICC.YFree
import HeytingLean.LoF.ICC.Soundness
import HeytingLean.LoF.ICC.UnrestrictedY
import HeytingLean.LoF.ICC.Workloads
import HeytingLean.LoF.ICC.ConservativeEmbedding
import HeytingLean.LoF.ICC.GPUVerifierContract
import HeytingLean.LoF.ICC.GPUVerifierTranslate
import HeytingLean.LoF.ICC.GPUVerifierCorpus
import HeytingLean.LoF.ICC.GPUVerifier
import HeytingLean.LoF.ICC.WitnessSpec
import HeytingLean.LoF.ICC.WitnessFormat
import HeytingLean.CLI.VerifierProofCorpus
import HeytingLean.Bridge.INet.ICCBasic
import HeytingLean.Bridge.INet.ICCLowering

/-!
Experimental additive ICC lane re-export.

This module is intentionally narrow. It exposes the research-lane syntax,
encodings, reduction, conservativity helpers, and ICC net lowering without
changing the production SKY or FullKernel import surfaces.

Claim boundary:

- formal soundness currently means the closed Y-free fragment only
- same-workload parity/performance currently means the shared Lean-owned ICC corpus only
- unrestricted `Y` remains a research lane, not part of the promoted soundness surface
-/
