import HeytingLean.LoF.LeanKernel.KernelMappingLeanCP

namespace HeytingLean
namespace LoF
namespace LeanKernel

/-!
# KernelOverlay

Lean-owned overlay rows that keep all conversion layers aligned under a single
stable row id.
-/

inductive KernelDivergenceLayer where
  | none
  | leanToCExport
  | cToLeanCPContract
  | cToRustIngest
  | rustToGPUProjection
  | gpuExecution
  | timeoutOrResource
  deriving Repr, DecidableEq

inductive KernelVerdict where
  | matched
  | unsupported
  | mismatch
  | timeout
  deriving Repr, DecidableEq

structure KernelOverlayRow where
  rowId : String
  declName : String
  moduleName : String
  obligationLabel : String
  kind : KernelObligationKind
  canonical : CanonicalObligationRow
  cContract : CContractRow
  leanCPContract : LeanCPContractRow
  rustMirror : RustMirrorRow
  gpuKernel : GPUKernelRow
  divergenceLayer : KernelDivergenceLayer := .none
  cpuVerdict : KernelVerdict := .matched
  rustVerdict : KernelVerdict := .matched
  gpuVerdict : KernelVerdict := .matched
  deriving Repr

noncomputable instance : DecidableEq KernelOverlayRow := Classical.decEq _

def mkKernelOverlayRow (row : CanonicalObligationRow) : KernelOverlayRow :=
  let cRow := canonicalToCContract row
  let leanCPRow := cContractToLeanCPContract cRow
  let rustRow := cContractToRustMirror cRow
  let gpuRow := rustMirrorToGPUKernel rustRow
  { rowId := row.rowId
    declName := row.declName
    moduleName := row.moduleName
    obligationLabel := row.obligationLabel
    kind := row.kind
    canonical := row
    cContract := cRow
    leanCPContract := leanCPRow
    rustMirror := rustRow
    gpuKernel := gpuRow }

@[simp] theorem mkKernelOverlayRow_rowId (row : CanonicalObligationRow) :
    (mkKernelOverlayRow row).rowId = row.rowId := rfl

@[simp] theorem mkKernelOverlayRow_kind (row : CanonicalObligationRow) :
    (mkKernelOverlayRow row).kind = row.kind := rfl

@[simp] theorem mkKernelOverlayRow_canonical (row : CanonicalObligationRow) :
    (mkKernelOverlayRow row).canonical = row := rfl

@[simp] theorem mkKernelOverlayRow_cContract (row : CanonicalObligationRow) :
    (mkKernelOverlayRow row).cContract = canonicalToCContract row := rfl

@[simp] theorem mkKernelOverlayRow_rustMirror (row : CanonicalObligationRow) :
    (mkKernelOverlayRow row).rustMirror =
      cContractToRustMirror (canonicalToCContract row) := rfl

@[simp] theorem mkKernelOverlayRow_leanCPContract (row : CanonicalObligationRow) :
    (mkKernelOverlayRow row).leanCPContract =
      cContractToLeanCPContract (canonicalToCContract row) := rfl

@[simp] theorem mkKernelOverlayRow_gpuKernel (row : CanonicalObligationRow) :
    (mkKernelOverlayRow row).gpuKernel =
      rustMirrorToGPUKernel (cContractToRustMirror (canonicalToCContract row)) := rfl

structure KernelMappingSummary where
  canonicalRows : Nat
  overlayRows : Nat
  deriving Repr, DecidableEq

structure KernelMappingArtifact where
  schemaVersion : Nat := 1
  tool : String := "kernel_mapping_export"
  rows : List KernelOverlayRow
  summary : KernelMappingSummary
  deriving Repr

noncomputable instance : DecidableEq KernelMappingArtifact := Classical.decEq _

def artifactOfCanonicalRows (rows : List CanonicalObligationRow) : KernelMappingArtifact :=
  let overlays := rows.map mkKernelOverlayRow
  { rows := overlays
    summary := { canonicalRows := rows.length, overlayRows := overlays.length } }

@[simp] theorem artifactOfCanonicalRows_summary_canonicalRows
    (rows : List CanonicalObligationRow) :
    (artifactOfCanonicalRows rows).summary.canonicalRows = rows.length := rfl

@[simp] theorem artifactOfCanonicalRows_summary_overlayRows
    (rows : List CanonicalObligationRow) :
    (artifactOfCanonicalRows rows).summary.overlayRows = rows.length := by
  simp [artifactOfCanonicalRows]

end LeanKernel
end LoF
end HeytingLean
