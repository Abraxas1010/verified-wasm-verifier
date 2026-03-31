import HeytingLean.KernelAssurance.Manifest

namespace HeytingLean.Tests.KernelAssurance

open HeytingLean.KernelAssurance
open HeytingLean.LoF.ICCKernel

theorem fixtureTruth : True := trivial

def fixtureNat : Nat := 7

def baseName : Name := .str .anonymous "KernelAssuranceFixture"

def sampleType : Term :=
  .sort .zero

def sampleValue : Term :=
  .const (.str .anonymous "Nat.zero") []

def theoremDecl : ExportedDecl :=
  { moduleName := baseName
    decl := .thmInfo
      { name := .str baseName "sampleTheorem"
        levelParams := []
        type := sampleType
        value := sampleValue
        all := [] } }

def defnDecl : ExportedDecl :=
  { moduleName := baseName
    decl := .defnInfo
      { name := .str baseName "sampleDef"
        levelParams := []
        type := sampleType
        value := sampleValue
        hints := .opaque
        safety := .safe
        all := [] } }

def axiomDecl : ExportedDecl :=
  { moduleName := baseName
    decl := .axiomInfo
      { name := .str baseName "sampleAxiom"
        levelParams := []
        type := sampleType
        isUnsafe := false } }

def supportedExport : ExportBundle :=
  { moduleRoots := #["HeytingLean.Tests.KernelAssurance"]
    declarations := #[theoremDecl, defnDecl]
    summary := exportSummaryOf #["HeytingLean.Tests.KernelAssurance"] 2 #[theoremDecl, defnDecl] }

def mixedExport : ExportBundle :=
  { moduleRoots := #["HeytingLean.Tests.KernelAssurance"]
    declarations := #[theoremDecl, axiomDecl]
    summary := exportSummaryOf #["HeytingLean.Tests.KernelAssurance"] 2 #[theoremDecl, axiomDecl] }

def supportedBundle : SliceBundle :=
  SliceBundle.ofExportBundle supportedExport

def mixedBundle : SliceBundle :=
  SliceBundle.ofExportBundle mixedExport

def tamperedBundle : SliceBundle :=
  let entry0 := supportedBundle.entries[0]!
  let tamperedEntry := { entry0 with entryDigest := "0xtampered" }
  let entries := supportedBundle.entries.set! 0 tamperedEntry
  { supportedBundle with entries := entries }

end HeytingLean.Tests.KernelAssurance
