import Std.Data.HashMap
import HeytingLean.Certified.ComposeCore
import HeytingLean.Certified.Program
import HeytingLean.Certified.DemoPrograms
import HeytingLean.Certified.ThermoPrograms
import HeytingLean.Certified.CryptoPrograms

namespace HeytingLean
namespace Certified

open Std

structure CertifiedLibrary where
  programs : List CertifiedProgram

namespace CertifiedLibrary

def demo : CertifiedLibrary :=
  { programs := Demo.libraryPrograms ++ Thermo.libraryPrograms }

def crypto : CertifiedLibrary :=
  { programs := Crypto.libraryPrograms }

def all : CertifiedLibrary :=
  { programs := Demo.libraryPrograms ++ Thermo.libraryPrograms ++ Crypto.libraryPrograms }

def indexById (lib : CertifiedLibrary) : HashMap ProgramId CertifiedProgram :=
  lib.programs.foldl (init := {}) (fun acc p => acc.insert p.id p)

def resolve? (lib : CertifiedLibrary) (id : ProgramId) : Option CertifiedProgram := do
  let m := lib.indexById
  match m.get? id with
  | some p => some p
  | none =>
      let parts := (id.splitOn "∘").filter (· ≠ "")
      match parts with
      | [] => none
      | [_] => none
      | p0 :: rest =>
          let base0 ← m.get? p0
          let bases ← rest.mapM (fun s => m.get? s)
          let rec fold (acc : CertifiedProgram) (xs : List CertifiedProgram) : Option CertifiedProgram := do
            match xs with
            | [] => some acc
            | p :: ps =>
                let acc' ← CertifiedLibrary.composePrograms? acc p
                fold acc' ps
          fold base0 bases

def find? (lib : CertifiedLibrary) (id : ProgramId) : Option CertifiedProgram :=
  lib.resolve? id

def headers (lib : CertifiedLibrary) : List ProgramHeader :=
  lib.programs.map (·.header)

end CertifiedLibrary

end Certified
end HeytingLean
