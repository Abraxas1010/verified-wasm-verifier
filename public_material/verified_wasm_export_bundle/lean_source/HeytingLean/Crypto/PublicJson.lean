import Lean
import Lean.Data.Json

namespace HeytingLean
namespace Crypto

open Lean

structure PublicInputs where
  form_commitment : String
  initial_state   : String
  final_state     : String
  lens_selector   : Nat
  deriving Repr

def PublicInputs.toJson (p : PublicInputs) : Json :=
  Json.mkObj [
    ("form_commitment", Json.str p.form_commitment),
    ("initial_state", Json.str p.initial_state),
    ("final_state", Json.str p.final_state),
    ("lens_selector", Json.str (toString p.lens_selector))
  ]

def PublicInputs.fromJson (j : Json) : Option PublicInputs :=
  match j.getObj? with
  | .error _ => none
  | .ok o =>
    let getStr? (k : String) : Option String :=
      match o.get? k with | some (Json.str s) => some s | _ => none
    let getNat? (k : String) : Option Nat :=
      match o.get? k with | some (Json.str s) => s.toNat? | _ => none
    match (getStr? "form_commitment", getStr? "initial_state", getStr? "final_state", getNat? "lens_selector") with
    | (some fc, some i, some f, some ls) =>
        if ls ≤ 2 then some { form_commitment := fc, initial_state := i, final_state := f, lens_selector := ls }
        else none
    | _ => none

end Crypto
end HeytingLean

