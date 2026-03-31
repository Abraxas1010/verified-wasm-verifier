import Lean
import Lean.Data.Json
import HeytingLean.Certified.Library
import HeytingLean.Certified.Modality

namespace HeytingLean
namespace Certified

open Lean

structure Query where
  dom?        : Option Ty := none
  cod?        : Option Ty := none
  property?   : Option Property := none
  modality?   : Option ModalityProfile := none
deriving Inhabited, Repr

namespace Query

def satisfies (q : Query) (p : CertifiedProgram) : Bool :=
  let domOk := q.dom?.map (· == p.dom) |>.getD true
  let codOk := q.cod?.map (· == p.cod) |>.getD true
  let propOk := q.property?.map (fun pr => decide (pr ∈ p.properties)) |>.getD true
  let modOk :=
    match q.modality? with
    | none => true
    | some m => m.admissible p.invariants
  domOk && codOk && propOk && modOk

end Query

def CertifiedLibrary.queryHeaders (lib : CertifiedLibrary) (q : Query) : List ProgramHeader :=
  lib.programs.filterMap (fun p => if q.satisfies p then some p.header else none)

end Certified
end HeytingLean
