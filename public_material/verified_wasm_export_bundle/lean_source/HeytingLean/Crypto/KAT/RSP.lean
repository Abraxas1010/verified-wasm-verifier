import Lean

namespace HeytingLean
namespace Crypto
namespace KAT

open System

structure KEMRSPCase where
  count : Nat
  seedHex : String
  pkHex   : String
  skHex   : String
  ctHex   : String
  ssHex   : String
  deriving Repr

structure DSARSPCase where
  count : Nat
  seedHex : String
  mlen : Nat
  msgHex : String
  pkHex : String
  skHex : String
  smlen : Nat
  smHex : String
  deriving Repr

private def trim (s : String) : String := s.trim

private def afterEq (s : String) : String :=
  match s.splitOn "=" with
  | _ :: v :: _ => v.trim
  | _ => ""

private def isMarker (line marker : String) : Bool := line.startsWith marker

/-- Normalize a hex-ish string by stripping all non-hex characters and lowercasing. -/
def normHex (s : String) : String :=
  let isHex (c : Char) : Bool :=
    ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
  String.mk <| (s.toList.filter isHex).map Char.toLower

def parseKEMRSPFile (p : FilePath) : IO (Array KEMRSPCase) := do
  let ok ← p.pathExists
  if !ok then return #[]
  let lines ← try IO.FS.lines p catch _ => pure #[]
  let mut cases : Array KEMRSPCase := #[]
  let mut curCount : Nat := 0
  let mut seed := ""
  let mut pk := ""
  let mut sk := ""
  let mut ct := ""
  let mut ss := ""
  for l in lines do
    let line := trim l
    if line.isEmpty || line.get! 0 = '#' then continue
    if isMarker line "count = " then
      -- start of a new case: flush previous if complete
      if seed != "" && pk != "" && sk != "" && ct != "" && ss != "" then
        cases := cases.push { count := curCount, seedHex := seed, pkHex := pk, skHex := sk, ctHex := ct, ssHex := ss }
      match line.drop 8 |>.toNat? with
      | some n => curCount := n
      | none => curCount := cases.size
      -- reset accumulators
      seed := ""; pk := ""; sk := ""; ct := ""; ss := ""
    else if isMarker line "seed = " then
      seed := afterEq line
    else if isMarker line "pk = " then
      pk := afterEq line
    else if isMarker line "sk = " then
      sk := afterEq line
    else if isMarker line "ct = " then
      ct := afterEq line
    else if isMarker line "ss = " then
      ss := afterEq line
    else
      pure ()
  -- flush last
  if seed != "" && pk != "" && sk != "" && ct != "" && ss != "" then
    cases := cases.push { count := curCount, seedHex := seed, pkHex := pk, skHex := sk, ctHex := ct, ssHex := ss }
  return cases

abbrev RSPCase := KEMRSPCase

def parseRSPFile (p : FilePath) : IO (Array RSPCase) :=
  parseKEMRSPFile p

def parseDSARSPFile (p : FilePath) : IO (Array DSARSPCase) := do
  let ok ← p.pathExists
  if !ok then return #[]
  let lines ← try IO.FS.lines p catch _ => pure #[]
  let mut cases : Array DSARSPCase := #[]
  let mut curCount : Nat := 0
  let mut seed := ""
  let mut mlen : Nat := 0
  let mut msg := ""
  let mut pk := ""
  let mut sk := ""
  let mut smlen : Nat := 0
  let mut sm := ""
  for l in lines do
    let line := trim l
    if line.isEmpty || line.get! 0 = '#' then continue
    if isMarker line "count = " then
      if seed != "" && msg != "" && pk != "" && sk != "" && sm != "" then
        cases := cases.push {
          count := curCount
          seedHex := seed
          mlen := mlen
          msgHex := msg
          pkHex := pk
          skHex := sk
          smlen := smlen
          smHex := sm
        }
      match line.drop 8 |>.toNat? with
      | some n => curCount := n
      | none => curCount := cases.size
      seed := ""; msg := ""; pk := ""; sk := ""; sm := ""
      mlen := 0; smlen := 0
    else if isMarker line "seed = " then
      seed := afterEq line
    else if isMarker line "mlen = " then
      mlen := (afterEq line).toNat?.getD 0
    else if isMarker line "msg = " then
      msg := afterEq line
    else if isMarker line "pk = " then
      pk := afterEq line
    else if isMarker line "sk = " then
      sk := afterEq line
    else if isMarker line "smlen = " then
      smlen := (afterEq line).toNat?.getD 0
    else if isMarker line "sm = " then
      sm := afterEq line
    else
      pure ()
  if seed != "" && msg != "" && pk != "" && sk != "" && sm != "" then
    cases := cases.push {
      count := curCount
      seedHex := seed
      mlen := mlen
      msgHex := msg
      pkHex := pk
      skHex := sk
      smlen := smlen
      smHex := sm
    }
  return cases

def countCasesByMarker (p : FilePath) : IO Nat := do
  let ok ← p.pathExists
  if !ok then return 0
  let lines ← try IO.FS.lines p catch _ => pure #[]
  let n := lines.foldl (init := 0) (fun acc l => if (trim l).startsWith "count = " then acc + 1 else acc)
  return n

def countRSPCasesInDir (dir : FilePath) : IO (List (String × Nat)) := do
  let ok ← dir.pathExists
  if !ok then return []
  let entries ← FilePath.readDir dir
  let mut out : List (String × Nat) := []
  for e in entries do
    if e.fileName.endsWith ".rsp" then
      let n ← countCasesByMarker e.path
      out := (e.fileName, n) :: out
  return out.reverse

end KAT
end Crypto
end HeytingLean
