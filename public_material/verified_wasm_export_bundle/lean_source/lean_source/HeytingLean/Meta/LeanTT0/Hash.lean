import HeytingLean.Util.SHA

/-
  Library-safe SHA-256 for LeanTT0.

  This module now delegates to the shared pure SHA-256 implementation in
  `HeytingLean.Util.SHA`, ensuring that all TT0 digests are backed by a
  real SHA-256 rather than an ad-hoc hash.
-/

namespace HeytingLean.Meta.LeanTT0

/-- SHA-256 digest of a byte array, using the shared pure implementation. -/
def sha256 (ba : ByteArray) : ByteArray :=
  HeytingLean.Util.SHA256.sha256Bytes ba

/- Domain-separation helpers (pure Lean, using sha256) -/
def tag (s : String) : ByteArray := s.toUTF8

def hcat (xs : List ByteArray) : ByteArray :=
  ByteArray.mk (xs.foldl (fun acc b => acc ++ b.data) (Array.mkEmpty 0))

def H (tagStr : String) (payload : ByteArray) : ByteArray :=
  sha256 (ByteArray.mk ((tag tagStr).data ++ payload.data))

def Hcat (tagStr : String) (xs : List ByteArray) : ByteArray :=
  H tagStr (hcat xs)

end HeytingLean.Meta.LeanTT0
