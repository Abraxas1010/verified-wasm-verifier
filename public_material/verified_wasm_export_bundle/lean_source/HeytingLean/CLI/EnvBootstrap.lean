import Lean

open Lean
open System

namespace HeytingLean.CLI.EnvBootstrap

private def leanProjectRootCandidates (cwd : FilePath) : List FilePath :=
  [ cwd
  , cwd / "lean"
  , cwd / ".." / "lean"
  ]

def findLeanProjectRoot (cwd? : Option FilePath := none) : IO FilePath := do
  let cwd ← match cwd? with
    | some cwd => pure cwd
    | none => IO.currentDir
  for candidate in leanProjectRootCandidates cwd do
    if ← (candidate / "lakefile.lean").pathExists then
      return candidate
  throw <| IO.userError s!"could not locate lean project root from {cwd}"

def bootstrapSearchPath (leanRoot? : Option FilePath := none) : IO Unit := do
  let leanRoot ← match leanRoot? with
    | some leanRoot => pure leanRoot
    | none => findLeanProjectRoot
  let sysroot ← Lean.findSysroot
  Lean.initSearchPath sysroot
  let current ← Lean.searchPathRef.get
  let mut candidates : Array FilePath := #[leanRoot / ".lake" / "build" / "lib" / "lean"]
  let packagesDir := leanRoot / ".lake" / "packages"
  if ← packagesDir.pathExists then
    for entry in ← packagesDir.readDir do
      candidates := candidates.push (entry.path / ".lake" / "build" / "lib" / "lean")
  let seen0 := current.foldl (fun acc p => acc.insert p true) (Std.HashMap.emptyWithCapacity)
  let (_, extrasRev) ← candidates.foldlM
    (fun (seen, extrasRev) path => do
      if (← path.pathExists) && !seen.contains path then
        pure (seen.insert path true, path :: extrasRev)
      else
        pure (seen, extrasRev))
    (seen0, ([] : List FilePath))
  Lean.searchPathRef.set (current ++ extrasRev.reverse)

def moduleNameFromString (text : String) : Name :=
  text.splitOn "." |>.foldl (fun acc piece => Name.str acc piece) Name.anonymous

def moduleImportFromString (text : String) : Import :=
  { module := moduleNameFromString text }

end HeytingLean.CLI.EnvBootstrap
