import Lean

namespace HeytingLean
namespace Crypto
namespace KAT

open System

structure KyberCase where
  name : String
  seedHex : String
  deriving Repr, Inhabited

private def normalize (s : String) : String :=
  s.trim

private def parseCaseLine (line : String) : Option KyberCase :=
  let fields := line.trim.split (fun c => c = ',' || c = '\t' || c = ';')
  let clean := fields.filter (fun s => s.length > 0)
  match clean.toList with
  | [name, seed] => some { name := normalize name, seedHex := normalize seed }
  | [name, seed, _sig] =>
      -- Accept a trailing checksum/signature field for broader KAT compatibility.
      some { name := normalize name, seedHex := normalize seed }
  | _ => none

def parseVectors (dir : FilePath) : IO (Array KyberCase) := do
  let exists ← dir.pathExists
  unless exists do
    return #[]
  let content ← IO.FS.readFile dir
  let lines := content.split (fun c => c = '\n')
  let cases :=
    lines.toList.filterMap (fun l =>
      let t := l.trim
      if t.isEmpty then none
      else if t.get? 0 = some '#' then none
      else parseCaseLine t)
  pure cases.toArray

end KAT
end Crypto
end HeytingLean
