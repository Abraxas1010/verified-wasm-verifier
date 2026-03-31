import Lean
import Lean.Data.Json
import HeytingLean.Certified.Types
import HeytingLean.Certified.Properties

namespace HeytingLean
namespace Certified

open Lean

/-- A demo "Bauer-style" modality profile: a nucleus modeled as adjoining a finite core. -/
structure ModalityProfile where
  name : String
  core : List Nat
deriving Inhabited, Repr

def ModalityProfile.constructiveCore : ModalityProfile :=
  { name := "ConstructiveCore", core := [0] }

def ModalityProfile.classicalLimit : ModalityProfile :=
  { name := "ClassicalLimit", core := [] }

def ModalityProfile.core100 : ModalityProfile :=
  { name := "Core100", core := [100] }

def ModalityProfile.core0_100 : ModalityProfile :=
  { name := "Core0_100", core := [0, 100] }

def ModalityProfile.ofName? (s : String) : Option ModalityProfile :=
  if s = ModalityProfile.constructiveCore.name then
    some ModalityProfile.constructiveCore
  else if s = ModalityProfile.classicalLimit.name then
    some ModalityProfile.classicalLimit
  else if s = ModalityProfile.core100.name then
    some ModalityProfile.core100
  else if s = ModalityProfile.core0_100.name then
    some ModalityProfile.core0_100
  else
    none

instance : ToJson ModalityProfile where
  toJson m := Json.mkObj [("name", Json.str m.name), ("core", toJson m.core.toArray)]

/-- A conservative closedness check for the demo: a range property is "closed" if it contains the core. -/
def ModalityProfile.propertyClosed (m : ModalityProfile) (p : Property) : Bool :=
  match p with
  | .boundedNat lo hi =>
      m.core.all (fun k => decide (lo ≤ k ∧ k ≤ hi))
  | .monotone =>
      true
  | .conservative =>
      true
  | .nonnegInt =>
      true
  | .custom _ =>
      true

/-- A program is admissible in a modality if all declared invariants are closed. -/
def ModalityProfile.admissible (m : ModalityProfile) (invariants : List Property) : Bool :=
  invariants.all (m.propertyClosed ·)

end Certified
end HeytingLean
