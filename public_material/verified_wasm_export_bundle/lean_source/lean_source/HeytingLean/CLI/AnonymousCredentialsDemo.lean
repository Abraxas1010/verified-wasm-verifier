import Lean
import HeytingLean.Crypto.ZK.AnonymousCredentialsExample

/-
# anonymous_credentials_demo CLI

Small CLI that:

* builds an example registry of anonymous credentials;
* constructs example proofs for different holders with the same
  attributes; and
* evaluates the example verifier `verify` on these proofs.

This provides a concrete harness for the `anonymousCredentialsCorrectness`
row (`zk.app.anonymous_credentials`) and exercises the example model used
in `Crypto.ZK.Spec.AnonymousCredentialsCorrectnessStatement`.
-/

namespace HeytingLean
namespace CLI
namespace AnonymousCredentialsDemo

open HeytingLean.Crypto.ZK
open HeytingLean.Crypto.ZK.AnonymousCredentialsExample

/-- Example registry of issued credentials. -/
def exampleRegistry : List Credential :=
  [ { id := "alice", attrs := ["age>=18", "kyc_passed"] }
  , { id := "bob",   attrs := ["age>=18"] } ]

/-- Example proofs for two different holders with the same attributes
    and registry, illustrating that the verifier's result is
    independent of the holder identity in this example model. -/
def proofAlice : Proof :=
  { holder := "alice"
  , attrs := ["age>=18"]
  , registry := exampleRegistry }

def proofCarol : Proof :=
  { holder := "carol"
  , attrs := ["age>=18"]
  , registry := exampleRegistry }

def main (_argv : List String) : IO UInt32 := do
  IO.println "anonymous_credentials_demo:"
  IO.println s!"  registry size: {exampleRegistry.length}"
  IO.println s!"  proofAlice.holder = {proofAlice.holder}"
  IO.println s!"  proofCarol.holder = {proofCarol.holder}"

  let vAlice := verify proofAlice
  let vCarol := verify proofCarol

  IO.println s!"  verify(proofAlice) = {vAlice}"
  IO.println s!"  verify(proofCarol) = {vCarol}"
  IO.println "  (In this model, these coincide because the verifier"
  IO.println "   depends only on attributes and the registry, not on"
  IO.println "   the holder identity.)"

  pure 0

end AnonymousCredentialsDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.AnonymousCredentialsDemo.main args
