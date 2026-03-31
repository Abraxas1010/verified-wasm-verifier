import Lean
import Lean.Data.Json
import HeytingLean.Crypto.PublicJson
import HeytingLean.Crypto.WitnessJson

/-!
Typed core structures for public inputs and witness, plus simple validators
and converters from the JSON codec types. No proofs, no sorries.
-/

namespace HeytingLean
namespace Crypto

inductive EvalOp where
  | Mark | Cross | Process
  deriving Repr, DecidableEq

namespace EvalOp
def ofString : String → Option EvalOp
  | "Mark" => some .Mark
  | "Cross" => some .Cross
  | "Process" => some .Process
  | _ => none
end EvalOp

structure EvalStepCore where
  operation   : EvalOp
  reentry_idx : Option Nat := none
  outer       : Option String := none
  deriving Repr

structure WitnessCore where
  reentry_values : List String
  boundary_marks : List Bool
  eval_trace     : List EvalStepCore
  deriving Repr

structure PublicInputsCore where
  form_commitment : String
  initial_state   : String
  final_state     : String
  lens_selector   : Nat
  deriving Repr

def PublicInputsCore.isValid (p : PublicInputsCore) : Bool := p.lens_selector ≤ 2

def WitnessCore.isSane (_w : WitnessCore) : Bool :=
  -- Minimal sanity: no further checks yet
  true

namespace Convert

open HeytingLean.Crypto

def toCorePublic (p : PublicInputs) : PublicInputsCore :=
  { form_commitment := p.form_commitment
  , initial_state := p.initial_state
  , final_state := p.final_state
  , lens_selector := p.lens_selector }

def toCoreWitness (w : Witness) : Option WitnessCore :=
  let steps? : Option (List EvalStepCore) :=
    w.eval_trace.foldr (fun s acc? => do
      let acc ← acc?
      let op ← EvalOp.ofString s.operation
      some ({ operation := op, reentry_idx := s.reentry_idx, outer := s.outer } :: acc)
    ) (some [])
  steps?.map (fun steps =>
    { reentry_values := w.reentry_values
    , boundary_marks := w.boundary_marks
    , eval_trace := steps })

end Convert

end Crypto
end HeytingLean
