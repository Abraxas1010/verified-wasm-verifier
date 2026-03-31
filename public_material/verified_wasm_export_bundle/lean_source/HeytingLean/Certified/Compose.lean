import Lean.Data.Json
import HeytingLean.Certified.ComposeCore
import HeytingLean.Certified.Library

namespace HeytingLean
namespace Certified

open Lean

structure CertifiedComposition where
  fId    : ProgramId
  gId    : ProgramId
  result : ProgramArtifact
  derivedProperties : List Property
deriving Inhabited, Repr

namespace CertifiedComposition

instance : ToJson CertifiedComposition where
  toJson c :=
    Json.mkObj
      [ ("f_id", Json.str c.fId)
      , ("g_id", Json.str c.gId)
      , ("result", toJson c.result)
      , ("derived_properties", toJson (c.derivedProperties.map toJson |>.toArray))
      ]

end CertifiedComposition

namespace CertifiedLibrary

def compose? (lib : CertifiedLibrary) (fId gId : ProgramId) : Option CertifiedComposition := do
  let f ← lib.find? fId
  let g ← lib.find? gId
  let result ← composePrograms? f g
  return { fId := fId
           gId := gId
           result := result.artifact
           derivedProperties := result.properties
         }

end CertifiedLibrary

end Certified
end HeytingLean
