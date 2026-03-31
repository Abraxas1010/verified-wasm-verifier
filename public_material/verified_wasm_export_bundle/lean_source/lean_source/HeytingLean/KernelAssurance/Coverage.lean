import HeytingLean.KernelAssurance.Bundle

namespace HeytingLean.KernelAssurance

open Lean

structure FamilyLedger where
  family : FamilyId
  discovered : Nat
  exported : Nat
  replaySupported : Nat
  checkerSupported : Nat
  blocked : Nat
  unclassified : Nat
  deriving Repr, Inhabited, BEq, ToJson, FromJson

structure CoverageReport where
  version : String := "kernel-assurance-v1"
  moduleRoots : Array String
  families : Array FamilyLedger
  discoveredFamilyCount : Nat
  exportedFamilyCount : Nat
  replaySupportedFamilyCount : Nat
  checkerSupportedFamilyCount : Nat
  blockedFamilyCount : Nat
  unclassifiedFamilyCount : Nat
  declsTotal : Nat
  supportedDecls : Nat
  blockedDecls : Nat
  unclassifiedDecls : Nat
  bundleDigest : String
  deriving Repr, Inhabited, BEq, ToJson, FromJson

private def familyLedgerOf (entries : Array SliceEntry) (family : FamilyId) : Option FamilyLedger :=
  let familyEntries := entries.filter (fun e => e.family = family)
  if familyEntries.isEmpty then
    none
  else
    let supportedDecls := familyEntries.foldl (fun acc e => if e.status = .supported then acc + 1 else acc) 0
    let blockedDecls := familyEntries.foldl (fun acc e => if e.status = .blocked then acc + 1 else acc) 0
    let unclassifiedDecls := familyEntries.foldl (fun acc e => if e.status = .unclassified then acc + 1 else acc) 0
    some {
      family := family
      discovered := familyEntries.size
      exported := familyEntries.size
      replaySupported := supportedDecls
      checkerSupported := supportedDecls
      blocked := blockedDecls
      unclassified := unclassifiedDecls
    }

def CoverageReport.ofBundle (bundle : SliceBundle) : CoverageReport :=
  let families := allFamilies.filterMap (familyLedgerOf bundle.entries)
  let discoveredFamilyCount := families.size
  let exportedFamilyCount := families.size
  let replaySupportedFamilyCount :=
    families.foldl (fun acc row => if row.replaySupported > 0 then acc + 1 else acc) 0
  let checkerSupportedFamilyCount :=
    families.foldl (fun acc row => if row.checkerSupported > 0 then acc + 1 else acc) 0
  let blockedFamilyCount :=
    families.foldl (fun acc row => if row.blocked > 0 then acc + 1 else acc) 0
  let unclassifiedFamilyCount :=
    families.foldl (fun acc row => if row.unclassified > 0 then acc + 1 else acc) 0
  {
    moduleRoots := bundle.descriptor.moduleRoots
    families := families
    discoveredFamilyCount := discoveredFamilyCount
    exportedFamilyCount := exportedFamilyCount
    replaySupportedFamilyCount := replaySupportedFamilyCount
    checkerSupportedFamilyCount := checkerSupportedFamilyCount
    blockedFamilyCount := blockedFamilyCount
    unclassifiedFamilyCount := unclassifiedFamilyCount
    declsTotal := bundle.declsTotal
    supportedDecls := bundle.exportedSupported
    blockedDecls := bundle.exportedBlocked
    unclassifiedDecls := bundle.exportedUnclassified
    bundleDigest := bundle.bundleDigest
  }

end HeytingLean.KernelAssurance
