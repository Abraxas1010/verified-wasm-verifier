import HeytingLean.Crypto.Form

/-
Core canonicalization for Laws of Form formulas, connected to
`HeytingLean.Crypto.Form`.

We provide a small, structurally recursive encoder from `Form n` to a
stable textual representation. This does not yet quotient by logical
equivalence; it is a canonical *syntax* encoding designed to be
independent of Lean's `repr` internals.
-/

namespace HeytingLean
namespace LoF

open HeytingLean.Crypto

/-- Canonical representation of a `Form n`, exposed as a stable string. -/
structure Canonical (n : Nat) where
  asString : String
  deriving Repr, DecidableEq

namespace Canonical

private def encodeFin {n : Nat} (i : Fin n) : String :=
  toString i.val

/-- Prefix-style, structurally recursive encoding of `Form n`. -/
private def encodeForm {n : Nat} : Form n → String
  | .top        => "T"
  | .bot        => "F"
  | .var idx    => "v" ++ encodeFin idx
  | .and φ ψ    => "(" ++ "& " ++ encodeForm φ ++ " " ++ encodeForm ψ ++ ")"
  | .or φ ψ     => "(" ++ "| " ++ encodeForm φ ++ " " ++ encodeForm ψ ++ ")"
  | .imp φ ψ    => "(" ++ "-> " ++ encodeForm φ ++ " " ++ encodeForm ψ ++ ")"

/-- Build a canonical wrapper from a `Form n` using `encodeForm`. -/
def ofForm {n : Nat} (f : Form n) : Canonical n :=
  { asString := encodeForm f }

end Canonical

/-- Deterministic canonicalization of `Form n` into a stable textual
representation. This is a pure, structural encoding and does not rely
on Lean's generic `repr`. -/
def canonicalize {n : Nat} (f : Form n) : Canonical n :=
  Canonical.ofForm f

end LoF
end HeytingLean
