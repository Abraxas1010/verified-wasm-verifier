import HeytingLean.CLI.VerifierFixture
import HeytingLean.CLI.VerifierProofCorpus
import HeytingLean.LoF.ICC.Encoder.DeclWalker

namespace HeytingLean
namespace LoF
namespace ICC
namespace Encoder

open Lean

inductive EncodingTier where
  | tierA
  | tierB
  | tierC
  deriving DecidableEq, Repr

def EncodingTier.code : EncodingTier → String
  | .tierA => "tier_a"
  | .tierB => "tier_b"
  | .tierC => "tier_c"

structure DeclClassification where
  tier : EncodingTier
  reason : String
  detail : String
  supportedSeed? : Option VerifierCorpusSeed := none
  exactCatalogMatch : Bool := false
  aggregateCatalogMatch : Bool := false
  hasAxiomDeps : Bool := false
  hasOpaqueDeps : Bool := false
  hasRecursorDeps : Bool := false
  trustAssumptions : List String := []
  deriving Repr

def declarationBackedSeeds : List VerifierCorpusSeed :=
  HeytingLean.CLI.VerifierFixture.iccVerifierCorpusSeeds ++
    HeytingLean.CLI.VerifierProofCorpus.iccVerifierCorpusSeeds

def seedForDeclName? (declName : Name) : Option VerifierCorpusSeed :=
  declarationBackedSeeds.find? (fun seed => seed.sourceDeclName = declName.toString)

def isAggregateSeedCatalog (declName : Name) : Bool :=
  let text := declName.toString
  text == "HeytingLean.CLI.VerifierFixture.iccVerifierCorpusSeeds" ||
    text == "HeytingLean.CLI.VerifierProofCorpus.iccVerifierCorpusSeeds"

private def closureKinds (env : Environment) (summary : DeclSummary) :
    Bool × Bool × Bool :=
  summary.closure.foldl
    (init := (false, false, false))
    (fun (hasAxiom, hasOpaque, hasRecursor) dep =>
      match env.find? dep with
      | some (.axiomInfo _) => (true, hasOpaque, hasRecursor)
      | some (.opaqueInfo _) => (hasAxiom, true, hasRecursor)
      | some (.recInfo _) => (hasAxiom, hasOpaque, true)
      | _ => (hasAxiom, hasOpaque, hasRecursor))

private def tierBReason (summary : DeclSummary) (hasAxiom hasOpaque hasRecursor : Bool) :
    String × String × List String :=
  if hasAxiom then
    ( "partial_ingestion_axiom_boundary"
    , s!"{summary.declName} is ingestible for dependency/trust reporting, but not yet executable under the current ICC lowering because it depends on axioms."
    , ["axiom_dependency"] )
  else if hasRecursor then
    ( "partial_ingestion_recursor_surface"
    , s!"{summary.declName} is ingestible for dependency/trust reporting, but not yet executable under the current ICC lowering because it reaches recursor dependencies outside the current witness catalog."
    , ["recursor_dependency"] )
  else if hasOpaque then
    ( "partial_ingestion_opaque_boundary"
    , s!"{summary.declName} is ingestible for dependency/trust reporting, but not yet executable under the current ICC lowering because it depends on opaque values."
    , ["opaque_dependency"] )
  else
    ( "partial_ingestion_catalog_gap"
    , s!"{summary.declName} is a surface declaration and is now part of the ingestion report, but it does not yet have an executable ICC seed mapping."
    , [] )

def classifyDecl (env : Environment) (summary : DeclSummary) : DeclClassification :=
  if isAggregateSeedCatalog summary.declName then
      { tier := .tierA
        reason := "aggregate_seed_catalog_match"
        detail := s!"{summary.declName} is the declaration-backed aggregate carrier for ICC seeds and is fully ingested through catalog expansion."
        exactCatalogMatch := true
        aggregateCatalogMatch := true
        hasRecursorDeps := true
        trustAssumptions := ["aggregate_seed_catalog", "catalog_expansion"] }
  else match seedForDeclName? summary.declName with
  | some seed =>
      { tier := .tierA
        reason := "catalog_exact_match"
        detail := s!"{summary.declName} has an exact declaration-backed ICC seed and can be auto-ingested through the existing verifier translation."
        supportedSeed? := some seed
        exactCatalogMatch := true
        trustAssumptions := ["catalog_exact_translation", "y_free_fixture_boundary"] }
  | none =>
      let (hasAxiom, hasOpaque, hasRecursor) := closureKinds env summary
      match summary.declKind with
      | "theorem" | "definition" | "opaque" =>
          let (reason, detail, extraTrust) := tierBReason summary hasAxiom hasOpaque hasRecursor
          { tier := .tierB
            reason := reason
            detail := detail
            hasAxiomDeps := hasAxiom
            hasOpaqueDeps := hasOpaque
            hasRecursorDeps := hasRecursor
            trustAssumptions := extraTrust }
      | _ =>
          { tier := .tierC
            reason := "boundary_ingestion_decl_kind"
            detail := s!"{summary.declName} has declaration kind {summary.declKind}; it is still ingested for inventory and boundary tracking, but not yet lowered to executable ICC."
            hasAxiomDeps := hasAxiom
            hasOpaqueDeps := hasOpaque
            hasRecursorDeps := hasRecursor
            trustAssumptions := ["non_checkable_decl_kind"] }

end Encoder
end ICC
end LoF
end HeytingLean
