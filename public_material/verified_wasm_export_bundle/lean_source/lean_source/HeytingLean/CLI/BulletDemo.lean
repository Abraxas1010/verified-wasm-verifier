import HeytingLean.Crypto.ZK.Spec.Bullet

/-!
# bullet_demo CLI

Minimal smoke test for the Bulletproof-style IR spec façade.
-/

namespace HeytingLean
namespace CLI
namespace BulletDemo

open Crypto.ZK.Spec

def main (_args : List String) : IO UInt32 := do
  let _ : Bullet.ConstraintsCorrectnessStatement :=
    Bullet.constraintsCorrectnessStatement_holds
  let _ : Bullet.BackendCorrectnessStatement :=
    Bullet.backendCorrectnessStatement_holds
  IO.println "bullet_demo: ok (constraints + backend correctness statements typecheck)"
  pure 0

end BulletDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.BulletDemo.main args

