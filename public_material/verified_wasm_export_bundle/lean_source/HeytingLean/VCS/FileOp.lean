import Mathlib

namespace HeytingLean
namespace VCS

/-- Hash digest used by VCS operations. -/
abbrev Hash := ByteArray

/-- Compact deterministic fingerprint for merge tie-break keys. -/
def hashFingerprint (h : Hash) : Nat :=
  h.toList.foldl (fun acc b => (acc * 257 + b.toNat) % 1000000007) 0

/-- File-level operation for the Abraxas append-only VCS log. -/
inductive FileOp where
  | create (path : String) (hash : Hash)
  | modify (path : String) (oldHash newHash : Hash)
  | delete (path : String) (hash : Hash)
  | rename (oldPath newPath : String) (hash : Hash)
  deriving DecidableEq

/-- Primary path used for conflict grouping. -/
def FileOp.primaryPath : FileOp → String
  | .create path _ => path
  | .modify path _ _ => path
  | .delete path _ => path
  | .rename oldPath _ _ => oldPath

/-- All touched paths for indexing and sheaf-style overlap checks. -/
def FileOp.touchedPaths : FileOp → List String
  | .create path _ => [path]
  | .modify path _ _ => [path]
  | .delete path _ => [path]
  | .rename oldPath newPath _ => [oldPath, newPath]

/-- Stable discriminator used for deterministic conflict resolution. -/
def FileOp.stableKey : FileOp → String
  | .create path hash => s!"create:{path}:{hash.size}:{hashFingerprint hash}"
  | .modify path oldHash newHash =>
      s!"modify:{path}:{oldHash.size}:{hashFingerprint oldHash}:{newHash.size}:{hashFingerprint newHash}"
  | .delete path hash => s!"delete:{path}:{hash.size}:{hashFingerprint hash}"
  | .rename oldPath newPath hash =>
      s!"rename:{oldPath}:{newPath}:{hash.size}:{hashFingerprint hash}"

end VCS
end HeytingLean
