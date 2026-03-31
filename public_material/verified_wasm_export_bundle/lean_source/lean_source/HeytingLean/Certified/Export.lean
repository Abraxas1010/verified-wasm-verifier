import Lean
import Lean.Data.Json
import HeytingLean.Certified.Library

namespace HeytingLean
namespace Certified

open Lean
open System

structure LibraryManifest where
  generatedBy : String
  programs    : List ProgramHeader
deriving Inhabited, Repr

instance : ToJson LibraryManifest where
  toJson m :=
    Json.mkObj
      [ ("generated_by", Json.str m.generatedBy)
      , ("programs", toJson (m.programs.map toJson |>.toArray))
      ]

namespace Export

private def ensureDir (p : FilePath) : IO Unit := do
  if (← p.pathExists) then
    pure ()
  else
    IO.FS.createDirAll p

private def toJsonListNat (xs : List Nat) : Json :=
  Json.arr (xs.map toJson |>.toArray)

private def sampleNats : List Nat :=
  [0, 1, 2, 10, 100, 300, 400, 1000, 10000, 20000]

private def sampleInts : List Int :=
  [-1000, -300, -1, 0, 1, 2, 300, 1000]

private def sampleListNats : List (List Nat) :=
  [ []
  , [0]
  , [1]
  , [1, 2, 3]
  , [100, 200]
  , [1, 200, 3]
  , [10000]
  ]

private def sampleU32s : List UInt32 :=
  [ 0
  , 1
  , 2
  , 10
  , 100
  , (0x7fffffff : UInt32)
  , (0x80000000 : UInt32)
  , (0xffffffff : UInt32)
  ]

private def toJsonU32 (x : UInt32) : Json :=
  toJson x.toNat

private def toJsonVal : (t : Ty) → t.interp → Json
  | .nat, x => toJson x
  | .int, x => toJson x
  | .listNat, xs => toJsonListNat xs
  | .u32, x => toJsonU32 x
  | .prod a b, x => Json.arr #[toJsonVal a x.1, toJsonVal b x.2]

private def sampleValues : (t : Ty) → List t.interp
  | .nat => sampleNats
  | .int => sampleInts
  | .listNat => sampleListNats
  | .u32 => sampleU32s
  | .prod a b =>
      let as := (sampleValues a).take 8
      let bs := (sampleValues b).take 8
      as.foldr (fun x acc => (bs.map (fun y => (x, y))) ++ acc) []

private def vectorsJson (p : CertifiedProgram) : Json :=
  let mkVec (inp outp : Json) : Json :=
    Json.mkObj [("input", inp), ("output", outp)]
  let vecs : List Json :=
    (sampleValues p.dom).map (fun x =>
      mkVec (toJsonVal p.dom x) (toJsonVal p.cod (p.fn x)))
  Json.mkObj
    [ ("generated_by", Json.str "HeytingLean.Certified.Export.vectors")
    , ("id", Json.str p.id)
    , ("type", Json.mkObj [("input", toJson p.dom), ("output", toJson p.cod)])
    , ("representations", Json.mkObj [("c_hash", Json.str p.cHash)])
    , ("vectors", Json.arr (vecs.toArray))
    ]

def writeLibrary (lib : CertifiedLibrary) (outDir : FilePath) : IO Unit := do
  ensureDir outDir
  let programsDir := outDir / "programs"
  ensureDir programsDir
  let manifest : LibraryManifest :=
    { generatedBy := "HeytingLean.Certified.export_library"
      programs := lib.headers
    }
  IO.FS.writeFile (outDir / "library_manifest.json") (toJson manifest |>.pretty)
  for p in lib.programs do
    let base := programsDir / p.id
    IO.FS.writeFile (base.withExtension "json") (toJson p.artifact |>.pretty)
    IO.FS.writeFile (base.withExtension "c") p.cCode
    IO.FS.writeFile (base.withExtension "vectors.json") (vectorsJson p |>.pretty)

end Export

end Certified
end HeytingLean
