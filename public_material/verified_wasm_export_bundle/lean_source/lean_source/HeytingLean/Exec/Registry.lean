import Lean
import HeytingLean.Exec.Core
import HeytingLean.Theorems.Core
import HeytingLean.LambdaIR.Add1MiniCProof
import HeytingLean.LambdaIR.DoubleMiniCProof
import HeytingLean.LambdaIR.ClampMiniCProof
import HeytingLean.LambdaIR.SuccTwiceMiniCProof
import HeytingLean.LambdaIR.Max01MiniCProof
import HeytingLean.LambdaIR.Add2MiniCProof
import HeytingLean.LambdaIR.Max2MiniCProof
import HeytingLean.LambdaIR.Min2MiniCProof
import HeytingLean.LambdaIR.RealFunMiniCProof
import HeytingLean.LambdaIR.Add1EndToEnd
import HeytingLean.LambdaIR.DoubleEndToEnd
import HeytingLean.LambdaIR.ClampEndToEnd
import HeytingLean.LambdaIR.SuccTwiceEndToEnd
import HeytingLean.LambdaIR.Max01EndToEnd
import HeytingLean.LambdaIR.Add2EndToEnd
import HeytingLean.LambdaIR.Max2EndToEnd
import HeytingLean.LambdaIR.Min2EndToEnd
import HeytingLean.LambdaIR.RealFunEndToEnd

namespace HeytingLean.Exec

open Lean
open HeytingLean.Theorems
open Json

/-- Build a result state for a Nat function. -/
private def mkResult (fnName : String) (args : Array Json) (r : Nat) : State :=
  { payload :=
      Json.mkObj
        [ ("fn",     Json.str fnName),
          ("args",   Json.arr args),
          ("result", Json.num r)
        ] }

/-- Build a unary Nat process from a Lean function and its end-to-end theorem name. -/
def mkUnaryNatProc (id : String) (specName : Name) (f : Nat → Nat) : Proc :=
  { id   := id,
    arity := Arity.unary,
    spec := { specThm := { name := specName }, notes := none },
    run  := fun s => do
      match decodeUnaryArgs s with
      | .ok n =>
          let r := f n
          pure <| mkResult id #[Json.num n] r
      | .error e =>
          throw <| IO.userError e }

/-- Build a binary Nat process from a Lean function and its end-to-end theorem name. -/
def mkBinaryNatProc (id : String) (specName : Name) (f : Nat → Nat → Nat)
    (notes : Option String := none) : Proc :=
  { id   := id,
    arity := Arity.binary,
    spec := { specThm := { name := specName }, notes },
    run  := fun s => do
      match decodeBinaryArgs s with
      | .ok (x, y) =>
          let r := f x y
          pure <| mkResult id #[Json.num x, Json.num y] r
      | .error e =>
          throw <| IO.userError e }

/-! ### Concrete processes -/

def proc_add1 : Proc :=
  mkUnaryNatProc "add1"
    `HeytingLean.LambdaIR.Add1EndToEnd.add1_end_to_end
    HeytingLean.LambdaIR.Add1MiniCProof.leanAdd1

def proc_double : Proc :=
  mkUnaryNatProc "double"
    `HeytingLean.LambdaIR.DoubleEndToEnd.double_end_to_end
    HeytingLean.LambdaIR.DoubleMiniCProof.leanDouble

def proc_succTwice : Proc :=
  mkUnaryNatProc "succ_twice"
    `HeytingLean.LambdaIR.SuccTwiceEndToEnd.succTwice_end_to_end
    HeytingLean.LambdaIR.SuccTwiceMiniCProof.leanSuccTwice

def proc_clamp01 : Proc :=
  mkUnaryNatProc "clamp01"
    `HeytingLean.LambdaIR.ClampEndToEnd.clamp01_end_to_end
    HeytingLean.LambdaIR.ClampMiniCProof.leanClamp01

def proc_max01 : Proc :=
  mkUnaryNatProc "max01"
    `HeytingLean.LambdaIR.Max01EndToEnd.max01_end_to_end
    HeytingLean.LambdaIR.Max01MiniCProof.leanMax01

def proc_add2 : Proc :=
  mkBinaryNatProc "add2"
    `HeytingLean.LambdaIR.Add2EndToEnd.add2_end_to_end
    HeytingLean.LambdaIR.Add2MiniCProof.leanAdd2
    (some "Nat2 end-to-end add (LoF: add2_compiled_spec)")

def proc_max2 : Proc :=
  mkBinaryNatProc "max2"
    `HeytingLean.LambdaIR.Max2EndToEnd.max2_end_to_end
    HeytingLean.LambdaIR.Max2MiniCProof.leanMax2
    (some "Nat2 end-to-end max (LoF: max2_compiled_select)")

def proc_min2 : Proc :=
  mkBinaryNatProc "min2"
    `HeytingLean.LambdaIR.Min2EndToEnd.min2_end_to_end
    HeytingLean.LambdaIR.Min2MiniCProof.leanMin2
    (some "Nat2 end-to-end min (LoF: min2_compiled_select)")

def proc_xorSum : Proc :=
  mkBinaryNatProc "xorSum"
    `HeytingLean.LambdaIR.RealFunEndToEnd.xorSum_end_to_end
    HeytingLean.LambdaIR.RealFunMiniCProof.leanXorSum
    (some "Nat2 end-to-end xorSum (LoF: xorSum_spec)")

/-- Registry of all processes. Extend this array as needed. -/
def allProcs : Array Proc :=
  #[ proc_add1
   , proc_double
   , proc_succTwice
   , proc_clamp01
   , proc_max01
   , proc_add2
   , proc_max2
   , proc_min2
   , proc_xorSum ]

/-- Lookup a process by id. -/
def findProcById (id : String) : Option Proc :=
  allProcs.find? (fun p => p.id = id)

end HeytingLean.Exec
