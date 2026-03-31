import Lean.Data.Json
import HeytingLean.Meta.LeanTT0.Hash
import HeytingLean.Meta.LeanTT0.Merkle

/-!
# Export CAB - Content-Addressable Certificates for Lens Exports

Provides infrastructure to generate CAB certificates for exported C/Python
artifacts from Heyting algebra lenses.

## Key Features

- SHA-256 hashing of all generated artifacts
- Merkle root over artifact hashes for single integrity commitment
- Certificate JSON linking to Lean theorem provenance
- Verification utilities

## Usage

```lean
-- After generating artifacts:
let artifacts := [("diamond.c", cCode), ("diamond.h", headerCode), ...]
let certificate := ExportCAB.generateCertificate "diamond" artifacts theoremNames
IO.FS.writeFile (outDir / "certificate.json") (certificate.compress)
```
-/

namespace HeytingLean.Meta.LeanTT0.ExportCAB

open Lean

/-- Hex-encode a ByteArray -/
def hexEncode (ba : ByteArray) : String :=
  let parts := ba.toList.map fun b =>
    let s := (Nat.toDigits 16 b.toNat).asString
    if s.length = 1 then "0" ++ s else s
  "0x" ++ String.intercalate "" parts

/-- Hash a string using SHA-256 -/
def hashString (s : String) : ByteArray :=
  HeytingLean.Meta.LeanTT0.sha256 s.toUTF8

/-- An artifact is a named file with its content -/
structure Artifact where
  name : String
  content : String
deriving Repr

/-- Computed hash entry for an artifact -/
structure ArtifactHash where
  name : String
  sha256 : ByteArray

/-- Hash all artifacts -/
def hashArtifacts (artifacts : List Artifact) : List ArtifactHash :=
  artifacts.map fun a => { name := a.name, sha256 := hashString a.content }

/-- Compute Merkle root over artifact hashes -/
def artifactMerkleRoot (hashes : List ArtifactHash) : ByteArray :=
  HeytingLean.Meta.LeanTT0.merkleRoot (hashes.map (·.sha256))

/-- Certificate version (v1) -/
def cabVersion : String := "cab-export-1"

/-- Certificate version (v2 with verification tiers) -/
def cabVersionV2 : String := "cab-export-2"

/-! ## Verification Tiers (v2) -/

/-- Verification tier indicating the strength of guarantees.
    - Gold: Full formal (Lean + dReal) for dim ≤ 16
    - Silver: Bounded compositional (Lean + α,β-CROWN) for dim ≤ 256
    - Bronze: Statistical (Lean + sampling) for any dimension -/
inductive VerificationTier where
  | gold   : VerificationTier
  | silver : VerificationTier
  | bronze : VerificationTier
deriving Repr, DecidableEq

def VerificationTier.toString : VerificationTier → String
  | .gold => "gold"
  | .silver => "silver"
  | .bronze => "bronze"

def VerificationTier.toJson (t : VerificationTier) : Json :=
  Json.str t.toString

/-- Numeric verification metadata for v2 certificates -/
structure NumericVerification where
  method : String               -- e.g., "alpha_beta_crown", "dreal", "sampling"
  gpuAccelerated : Bool
  latentDim : Nat
  bounds : Option Json          -- Optional bounds information
  compositional : Bool
  verificationTimeSeconds : Float

def NumericVerification.toJson (nv : NumericVerification) : Json :=
  Json.mkObj [
    ("method", Json.str nv.method),
    ("gpu_accelerated", Json.bool nv.gpuAccelerated),
    ("latent_dim", Json.num nv.latentDim),
    ("bounds", nv.bounds.getD Json.null),
    ("compositional", Json.bool nv.compositional),
    ("verification_time_seconds", Json.str (toString nv.verificationTimeSeconds))
  ]

/-- Categorical correspondence metadata for v2 certificates.
    Documents the connection between HeytingLean's lattice-theoretic
    formalizations and Categorical Deep Learning (CDL). -/
structure CategoricalCorrespondence where
  cdlReference : String            -- e.g., "arXiv:2402.15332"
  monadAlgebra : Option (List String)  -- Theorems showing nucleus = monad algebra
  algebraHomomorphism : Option (List String)  -- Theorems for T-algebra morphisms
  weightTying : Option String      -- Comonoid theorem for weight tying

def CategoricalCorrespondence.toJson (cc : CategoricalCorrespondence) : Json :=
  let monadArr := cc.monadAlgebra.getD []
  let homArr := cc.algebraHomomorphism.getD []
  Json.mkObj [
    ("cdl_reference", Json.str cc.cdlReference),
    ("monad_algebra_theorems", Json.arr (monadArr.map Json.str).toArray),
    ("algebra_homomorphism_theorems", Json.arr (homArr.map Json.str).toArray),
    ("weight_tying_theorem", cc.weightTying.map Json.str |>.getD Json.null)
  ]

/-- Default categorical correspondence for nucleus-based architectures -/
def defaultCategoricalCorrespondence : CategoricalCorrespondence :=
  { cdlReference := "arXiv:2402.15332"
    monadAlgebra := some ["monad_multiplication", "monad_unit", "monad_strength"]
    algebraHomomorphism := some ["AlgebraHomomorphism.comp", "AlgebraHomomorphism.id"]
    weightTying := some "CDL.LaxAlgebraComonoid.WeightTying.tie2" }

/-- Generate a CAB certificate as JSON -/
def generateCertificate
    (lensId : String)
    (artifacts : List Artifact)
    (theorems : List String)
    (leanModules : List String)
    (description : String := "")
    (toolchain : String := "leanprover/lean4:v4.24.0") : Json :=
  let hashes := hashArtifacts artifacts
  let root := artifactMerkleRoot hashes
  let artifactArr := hashes.map fun h =>
    Json.mkObj [
      ("name", Json.str h.name),
      ("sha256", Json.str (hexEncode h.sha256))
    ]
  let theoremArr := theorems.map Json.str
  let moduleArr := leanModules.map Json.str
  Json.mkObj [
    ("version", Json.str cabVersion),
    ("lens_id", Json.str lensId),
    ("description", Json.str description),
    ("algo", Json.str "sha256"),
    ("merkle_root", Json.str (hexEncode root)),
    ("lean_toolchain", Json.str toolchain),
    ("lean_modules", Json.arr moduleArr.toArray),
    ("theorems", Json.arr theoremArr.toArray),
    ("artifacts", Json.arr artifactArr.toArray),
    ("generator", Json.str "HeytingLean.Meta.LeanTT0.ExportCAB")
  ]

/-- Generate a CAB certificate v2 as JSON with verification tier.
    The v2 schema adds:
    - verification_tier: gold/silver/bronze
    - algebraic_verification: dimension-independent Lean proofs
    - numeric_verification: instance-specific bounds and method
    - categorical_correspondence: CDL framework mappings

    The v2 certificate is backward-compatible; v1 readers can
    ignore the new fields and use the core fields unchanged. -/
def generateCertificateV2
    (lensId : String)
    (artifacts : List Artifact)
    (theorems : List String)
    (leanModules : List String)
    (verificationTier : VerificationTier)
    (numericVerification : Option NumericVerification := none)
    (categoricalCorrespondence : Option CategoricalCorrespondence := none)
    (description : String := "")
    (toolchain : String := "leanprover/lean4:v4.24.0") : Json :=
  let hashes := hashArtifacts artifacts
  let root := artifactMerkleRoot hashes
  let artifactArr := hashes.map fun h =>
    Json.mkObj [
      ("name", Json.str h.name),
      ("sha256", Json.str (hexEncode h.sha256))
    ]
  let theoremArr := theorems.map Json.str
  let moduleArr := leanModules.map Json.str
  let algebraicVerification := Json.mkObj [
    ("lean_modules", Json.arr moduleArr.toArray),
    ("theorems", Json.arr theoremArr.toArray),
    ("dimension_independent", Json.bool true)
  ]
  let numericJson := match numericVerification with
    | some nv => nv.toJson
    | none => Json.null
  let categoricalJson := match categoricalCorrespondence with
    | some cc => cc.toJson
    | none => Json.null
  Json.mkObj [
    ("version", Json.str cabVersionV2),
    ("lens_id", Json.str lensId),
    ("merkle_root", Json.str (hexEncode root)),
    ("verification_tier", verificationTier.toJson),
    ("algebraic_verification", algebraicVerification),
    ("numeric_verification", numericJson),
    ("categorical_correspondence", categoricalJson),
    ("artifacts", Json.arr artifactArr.toArray),
    ("algo", Json.str "sha256"),
    ("lean_toolchain", Json.str toolchain),
    ("description", Json.str description),
    ("generator", Json.str "HeytingLean.Meta.LeanTT0.ExportCAB")
  ]

/-- Verify a single artifact against its expected hash -/
def verifyArtifact (content : String) (expectedHash : String) : Bool :=
  let computed := hexEncode (hashString content)
  computed == expectedHash

/-- Parse a certificate JSON and extract artifact hashes -/
def parseArtifactHashes (certJson : Json) : Option (List (String × String)) :=
  match certJson.getObjVal? "artifacts" with
  | Except.error _ => some []
  | Except.ok artifacts =>
    match artifacts with
    | Json.arr arr =>
      let pairs := arr.toList.filterMap fun obj =>
        match (Json.getObjValAs? obj String "name", Json.getObjValAs? obj String "sha256") with
        | (Except.ok name, Except.ok hash) => some (name, hash)
        | _ => none
      some pairs
    | _ => none

/-- Parse Merkle root from certificate -/
def parseMerkleRoot (certJson : Json) : Option String :=
  match Json.getObjValAs? certJson String "merkle_root" with
  | Except.ok s => some s
  | Except.error _ => none

/-- Recompute Merkle root from artifact contents -/
def recomputeMerkleRoot (artifactContents : List (String × String)) : String :=
  let hashes : List ArtifactHash := artifactContents.map fun (name, content) =>
    { name := name, sha256 := hashString content }
  hexEncode (artifactMerkleRoot hashes)

/-- Full verification of a certificate against artifact files -/
def verifyCertificate (certJson : Json) (readFile : String → IO String) : IO Bool := do
  -- Parse expected hashes
  let some expectedHashes := parseArtifactHashes certJson
    | return false
  let some expectedRoot := parseMerkleRoot certJson
    | return false

  -- Read and hash all files
  let mut contents : List (String × String) := []
  for (name, expectedHash) in expectedHashes do
    let content ← readFile name
    if !verifyArtifact content expectedHash then
      IO.eprintln s!"Hash mismatch for {name}"
      return false
    contents := (name, content) :: contents

  -- Verify Merkle root
  let computedRoot := recomputeMerkleRoot contents.reverse
  if computedRoot != expectedRoot then
    IO.eprintln s!"Merkle root mismatch: expected {expectedRoot}, got {computedRoot}"
    return false

  return true

/-- Generate summary of verification results -/
structure VerificationResult where
  success : Bool
  merkleRoot : String
  artifactCount : Nat
  failedArtifacts : List String
deriving Repr

def toVerificationJson (r : VerificationResult) : Json :=
  Json.mkObj [
    ("success", Json.bool r.success),
    ("merkle_root", Json.str r.merkleRoot),
    ("artifact_count", Json.num r.artifactCount),
    ("failed_artifacts", Json.arr (r.failedArtifacts.map Json.str).toArray)
  ]

end HeytingLean.Meta.LeanTT0.ExportCAB
