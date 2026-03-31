import Lean.Data.Json
import HeytingLean.KernelAssurance.ExportSupport

namespace HeytingLean.KernelAssurance

open Lean
open HeytingLean.LoF.ICCKernel

private structure EntryMaterial where
  moduleName : String
  declName : String
  kindTag : String
  family : FamilyId
  status : SupportStatus
  termCounts : Array CountEntry
  exportedDigest : String
  deriving Repr, Inhabited, BEq, ToJson

structure SliceEntry where
  moduleName : String
  declName : String
  kindTag : String
  family : FamilyId
  status : SupportStatus
  termCounts : Array CountEntry
  exportedDigest : String
  entryDigest : String
  exported : ExportedDecl
  deriving Repr, Inhabited, BEq, ToJson

def mkEntryDigest
    (moduleName declName kindTag : String)
    (family : FamilyId)
    (status : SupportStatus)
    (termCounts : Array CountEntry)
    (exportedDigest : String) : String :=
  structuralDigest ({
    moduleName := moduleName
    declName := declName
    kindTag := kindTag
    family := family
    status := status
    termCounts := termCounts
    exportedDigest := exportedDigest
  } : EntryMaterial)

def SliceEntry.recomputedEntryDigest (entry : SliceEntry) : String :=
  mkEntryDigest entry.moduleName entry.declName entry.kindTag entry.family entry.status
    entry.termCounts entry.exportedDigest

def mkSliceEntry (d : ExportedDecl) : SliceEntry :=
  let family := familyOfDecl d
  let status := statusOfDecl d
  let termCounts := d.termCounts
  let exportedDigest := exportedDeclDigest d
  let moduleName := moduleNameText d
  let declName := declNameText d
  let kindTag := d.kindTag
  {
    moduleName := moduleName
    declName := declName
    kindTag := kindTag
    family := family
    status := status
    termCounts := termCounts
    exportedDigest := exportedDigest
    entryDigest := mkEntryDigest moduleName declName kindTag family status termCounts exportedDigest
    exported := d
  }

private structure BundleDigestMaterial where
  descriptor : SliceDescriptor
  declsTotal : Nat
  exportedSupported : Nat
  exportedBlocked : Nat
  exportedUnclassified : Nat
  entryDigests : Array String
  deriving Repr, Inhabited, BEq, ToJson

structure SliceBundle where
  descriptor : SliceDescriptor
  declsTotal : Nat
  exportedSupported : Nat
  exportedBlocked : Nat
  exportedUnclassified : Nat
  entries : Array SliceEntry
  bundleDigest : String
  deriving Repr, Inhabited, BEq, ToJson

def SliceBundle.recomputedBundleDigest (bundle : SliceBundle) : String :=
  structuralDigest ({
    descriptor := bundle.descriptor
    declsTotal := bundle.declsTotal
    exportedSupported := bundle.exportedSupported
    exportedBlocked := bundle.exportedBlocked
    exportedUnclassified := bundle.exportedUnclassified
    entryDigests := bundle.entries.map (·.entryDigest)
  } : BundleDigestMaterial)

def SliceBundle.bundleDigestValid (bundle : SliceBundle) : Bool :=
  bundle.bundleDigest = bundle.recomputedBundleDigest

def SliceBundle.ofExportBundle (bundle : ExportBundle) : SliceBundle :=
  let entries := bundle.declarations.map mkSliceEntry
  let exportedSupported := entries.foldl (fun acc e => if e.status = .supported then acc + 1 else acc) 0
  let exportedBlocked := entries.foldl (fun acc e => if e.status = .blocked then acc + 1 else acc) 0
  let exportedUnclassified := entries.foldl (fun acc e => if e.status = .unclassified then acc + 1 else acc) 0
  let descriptor : SliceDescriptor := { moduleRoots := bundle.moduleRoots }
  let base : SliceBundle :=
    { descriptor := descriptor
      declsTotal := bundle.summary.declsTotal
      exportedSupported := exportedSupported
      exportedBlocked := exportedBlocked
      exportedUnclassified := exportedUnclassified
      entries := entries
      bundleDigest := "" }
  { base with bundleDigest := base.recomputedBundleDigest }

end HeytingLean.KernelAssurance
