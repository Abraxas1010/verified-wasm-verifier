import Lean.Data.Json
import HeytingLean.KernelAssurance.Surface
import HeytingLean.Meta.LeanTT0.ExportCAB

namespace HeytingLean.KernelAssurance

open Lean
open HeytingLean.LoF.ICCKernel
open HeytingLean.Meta.LeanTT0.ExportCAB

def structuralDigest [ToJson α] (a : α) : String :=
  hexEncode (hashString (toJson a).compress)

def exportedDeclDigest (d : ExportedDecl) : String :=
  structuralDigest d

def moduleNameText (d : ExportedDecl) : String :=
  d.moduleName.structuralKey

def declNameText (d : ExportedDecl) : String :=
  d.name.structuralKey

structure FamilyHistogramRow where
  family : FamilyId
  declCount : Nat
  deriving Repr, Inhabited, BEq, ToJson, FromJson

def familyHistogram (decls : Array ExportedDecl) : Array FamilyHistogramRow :=
  allFamilies.filterMap fun family =>
    let count := decls.foldl (fun acc d => if familyOfDecl d = family then acc + 1 else acc) 0
    if count = 0 then
      none
    else
      some { family := family, declCount := count }

end HeytingLean.KernelAssurance
