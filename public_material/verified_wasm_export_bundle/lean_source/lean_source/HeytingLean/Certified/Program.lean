import Lean
import Lean.Data.Json
import HeytingLean.Certified.Types
import HeytingLean.Certified.Properties
import HeytingLean.Util.SHA

namespace HeytingLean
namespace Certified

open Lean
open HeytingLean.Util

/-- JSON-exportable program header (searchable metadata only). -/
structure ProgramHeader where
  id         : ProgramId
  name       : String
  version    : SemVer
  dom        : Ty
  cod        : Ty
  dimension  : Dimension
  lenses     : List Lens
  properties : List Property
  invariants : List Property
  cHash      : String
deriving Inhabited, Repr

instance : ToJson ProgramHeader where
  toJson h :=
    Json.mkObj
      [ ("id", Json.str h.id)
      , ("name", Json.str h.name)
      , ("version", toJson h.version)
      , ("type", Json.mkObj [("input", toJson h.dom), ("output", toJson h.cod)])
      , ("classification", Json.mkObj
          [ ("dimension", toJson h.dimension)
          , ("lenses", toJson (h.lenses.map toJson |>.toArray))
          ])
      , ("properties", toJson (h.properties.map toJson |>.toArray))
      , ("invariants", toJson (h.invariants.map toJson |>.toArray))
      , ("representations", Json.mkObj [("c_hash", Json.str h.cHash)])
      ]

/-- Full exported program artifact (header + C code). -/
structure ProgramArtifact where
  header : ProgramHeader
  cCode  : String
deriving Inhabited, Repr

instance : ToJson ProgramArtifact where
  toJson a :=
    match (toJson a.header) with
    | Json.obj kvs =>
        Json.obj (kvs.insert "representations"
          (Json.mkObj [("c_hash", Json.str a.header.cHash), ("c_code", Json.str a.cCode)]))
    | other =>
        other

/-- In-memory certified program (executable semantics + proofs). -/
structure CertifiedProgram where
  id        : ProgramId
  name      : String
  version   : SemVer
  dom       : Ty
  cod       : Ty
  dimension : Dimension
  lenses    : List Lens
  properties : List Property
  invariants : List Property
  fn        : dom.interp → cod.interp
  propProofs : ∀ p, p ∈ properties → Property.Holds p dom cod fn
  cCode     : String
  cHash     : String
  cHashOk   : cHash = SHA256.sha256Hex cCode.toUTF8

namespace CertifiedProgram

def header (p : CertifiedProgram) : ProgramHeader :=
  { id := p.id
    name := p.name
    version := p.version
    dom := p.dom
    cod := p.cod
    dimension := p.dimension
    lenses := p.lenses
    properties := p.properties
    invariants := p.invariants
    cHash := p.cHash
  }

def artifact (p : CertifiedProgram) : ProgramArtifact :=
  { header := p.header, cCode := p.cCode }

/-- Convenience constructor that derives `cHash` from `cCode`. -/
def mkHashed
    (id : ProgramId)
    (name : String)
    (version : SemVer)
    (dom cod : Ty)
    (dimension : Dimension)
    (lenses : List Lens)
    (properties invariants : List Property)
    (fn : dom.interp → cod.interp)
    (propProofs : ∀ p, p ∈ properties → Property.Holds p dom cod fn)
    (cCode : String) : CertifiedProgram :=
  { id := id
    name := name
    version := version
    dom := dom
    cod := cod
    dimension := dimension
    lenses := lenses
    properties := properties
    invariants := invariants
    fn := fn
    propProofs := propProofs
    cCode := cCode
    cHash := SHA256.sha256Hex cCode.toUTF8
    cHashOk := rfl
  }

end CertifiedProgram

end Certified
end HeytingLean
