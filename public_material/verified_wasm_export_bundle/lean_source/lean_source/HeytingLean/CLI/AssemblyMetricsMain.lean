import Lean.Data.Json
import HeytingLean.ATheory.AssemblyCore
import HeytingLean.ATheory.CopyNumberSelection

/-!
# Assembly metrics demo CLI

Emits a tiny, deterministic JSON payload for Assembly Theory metrics that can
be used as an ML loss target or capability check.
-/

namespace HeytingLean.CLI.AssemblyMetricsMain

open Lean
open HeytingLean.ATheory

inductive Part
  | A | B | C
deriving DecidableEq, Repr

def demoRules : Rules Part where
  compose _ _ := {}

def objA : Obj Part := Obj.base Part.A
def objAB : Obj Part := Obj.join (Obj.base Part.A) (Obj.base Part.B)
def objABA : Obj Part := Obj.join (Obj.base Part.A) (Obj.join (Obj.base Part.B) (Obj.base Part.A))

def idx (o : Obj Part) : Nat :=
  syntacticIndex demoRules o

def mu (o : Obj Part) : Nat :=
  match o with
  | Obj.base _   => 1
  | Obj.join _ _ => 2

def assemblyScore (o : Obj Part) : Float :=
  Float.ofNat (mu o) * Float.ofNat (idx o + 1)

def ensembleScore : Float :=
  let nA := mu objA
  let nB := mu objAB
  let NT := nA + nB
  if NT == 0 then
    0.0
  else
    let ntf := Float.ofNat NT
    let termA := Float.exp (Float.ofNat (idx objA)) * (Float.ofNat (nA - 1)) / ntf
    let termB := Float.exp (Float.ofNat (idx objAB)) * (Float.ofNat (nB - 1)) / ntf
    termA + termB

def selectedFlag : Bool :=
  let vset : List (Obj Part) := [objA, objAB]
  vset.any (fun v => decide (idx v ≥ 1) && decide (mu v ≥ 1))

def jsonNumFloat (x : Float) : Json :=
  match JsonNumber.fromFloat? x with
  | Sum.inl _ => Json.num (0 : JsonNumber)
  | Sum.inr n => Json.num n

def payload : Json :=
  let objArr :=
    Json.arr #[
      Json.mkObj [
        ("name", Json.str "objA"),
        ("idx", Json.num (idx objA)),
        ("mu", Json.num (mu objA)),
        ("assembly_score", jsonNumFloat (assemblyScore objA))
      ],
      Json.mkObj [
        ("name", Json.str "objAB"),
        ("idx", Json.num (idx objAB)),
        ("mu", Json.num (mu objAB)),
        ("assembly_score", jsonNumFloat (assemblyScore objAB))
      ],
      Json.mkObj [
        ("name", Json.str "objABA"),
        ("idx", Json.num (idx objABA)),
        ("mu", Json.num (mu objABA)),
        ("assembly_score", jsonNumFloat (assemblyScore objABA))
      ]
    ]
  Json.mkObj [
    ("schema", Json.str "HeytingLean/AssemblyMetricsOutput.v1"),
    ("rules", Json.str "demoRules (compose always allowed)"),
    ("objects", objArr),
    ("ensemble", Json.mkObj [
      ("NT", Json.num (mu objA + mu objAB)),
      ("value", jsonNumFloat ensembleScore),
      ("formula", Json.str "exp(idx objAB) * ((2 - 1) / 3)")
    ]),
    ("selected_1_1", Json.bool selectedFlag)
  ]

def main (_argv : List String) : IO UInt32 := do
  IO.println (Json.pretty payload)
  return 0

end HeytingLean.CLI.AssemblyMetricsMain

open HeytingLean.CLI.AssemblyMetricsMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.AssemblyMetricsMain.main args
