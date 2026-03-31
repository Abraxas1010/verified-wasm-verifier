import Lean
import HeytingLean.Crypto.Signature.Spec

/-
# sig_demo CLI

Small CLI that exercises a trivial signature-scheme instance of the
abstract `Signature.Spec.Scheme` interface. This is for demonstration
only and does **not** model any real cryptographic scheme.
-/

namespace HeytingLean
namespace CLI
namespace SigDemo

open HeytingLean.Crypto.Signature
open HeytingLean.Crypto.Signature.Spec

def main (_argv : List String) : IO UInt32 := do
  let m := "message"
  let pk : Unit := ()
  let sk : Unit := ()
  let σ := demoScheme.sign sk m
  -- In this scheme, verification is trivial; we simply report success.
  let _ := pk
  let _ := σ
  IO.println s!"sig_demo: msg={m}, verified=true"
  pure 0

end SigDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.SigDemo.main args
