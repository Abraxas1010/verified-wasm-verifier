import Lean
import Lean.Data.Json

namespace HeytingLean
namespace Crypto

open Lean

structure EvalStep where
  operation   : String
  reentry_idx : Option Nat
  outer       : Option String
  deriving Repr

structure Witness where
  reentry_values : List String
  boundary_marks : List Bool
  eval_trace     : List EvalStep
  deriving Repr

namespace Witness

def toJson (w : Witness) : Json :=
  let evList := w.eval_trace.map (fun s =>
    Json.mkObj [
      ("operation", Json.str s.operation),
      ("reentry_idx", match s.reentry_idx with | some n => Json.str (toString n) | none => Json.null),
      ("outer", match s.outer with | some x => Json.str x | none => Json.null)
    ])
  Json.mkObj [
    ("reentry_values", Json.arr (Array.mk (w.reentry_values.map Json.str))),
    ("boundary_marks", Json.arr (Array.mk (w.boundary_marks.map Json.bool))),
    ("eval_trace", Json.arr (Array.mk evList))
  ]

def fromJson (j : Json) : Option Witness :=
  match j.getObj? with
  | .error _ => none
  | .ok o =>
    let getArr (k : String) : Option (List Json) :=
      match o.get? k with | some (Json.arr a) => some a.toList | _ => none
    let rv := getArr "reentry_values"
    let bm := getArr "boundary_marks"
    let et := getArr "eval_trace"
    match (rv, bm, et) with
    | (some rvs, some bms, some ets) =>
        let rvs' := rvs.foldr (fun j acc => match j with | Json.str s => s :: acc | _ => acc) [] |>.reverse
        let bms' := bms.foldr (fun j acc => match j with | Json.bool b => b :: acc | _ => acc) [] |>.reverse
        let ets' := ets.foldr (fun j acc =>
          match j.getObj? with
          | .ok o2 =>
            let op := match o2.get? "operation" with | some (Json.str s) => s | _ => ""
            let rid := match o2.get? "reentry_idx" with | some (Json.str s) => s.toNat? | _ => none
            let outer := match o2.get? "outer" with | some (Json.str s) => some s | _ => none
            { operation := op, reentry_idx := rid, outer := outer } :: acc
          | _ => acc) []
        some { reentry_values := rvs', boundary_marks := bms', eval_trace := ets' }
    | _ => none

end Witness

end Crypto
end HeytingLean
