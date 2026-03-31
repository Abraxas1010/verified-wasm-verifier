import Lean
import Lean.Data.Json

namespace HeytingLean
namespace Certified

open Lean

/-- Semantic version (minimal). -/
structure SemVer where
  major : Nat
  minor : Nat
  patch : Nat
deriving DecidableEq, Inhabited, Repr

def SemVer.toString (v : SemVer) : String :=
  s!"{v.major}.{v.minor}.{v.patch}"

instance : ToString SemVer := ⟨SemVer.toString⟩

instance : ToJson SemVer where
  toJson v :=
    Json.mkObj
      [ ("major", toJson v.major)
      , ("minor", toJson v.minor)
      , ("patch", toJson v.patch)
      ]

abbrev ProgramId := String

/-- A tiny type universe for the demo. -/
inductive Ty where
  | nat
  | int
  | listNat
  | u32
  | prod (a b : Ty)
deriving DecidableEq, Inhabited, Repr

def Ty.toString : Ty → String
  | .nat     => "Nat"
  | .int     => "Int"
  | .listNat => "ListNat"
  | .u32     => "UInt32"
  | .prod a b => s!"Prod({a.toString},{b.toString})"

instance : ToString Ty := ⟨Ty.toString⟩

abbrev Ty.interp : Ty → Type
  | .nat     => Nat
  | .int     => Int
  | .listNat => List Nat
  | .u32     => UInt32
  | .prod a b => a.interp × b.interp

instance : ToJson Ty := ⟨fun t => Json.str t.toString⟩

private def splitTopComma? (s : String) : Option (String × String) :=
  let rec go (depth : Nat) (acc : List Char) : List Char → Option (String × String)
    | [] => none
    | c :: cs =>
        if c = '(' then
          go (depth + 1) (c :: acc) cs
        else if c = ')' then
          go (depth - 1) (c :: acc) cs
        else if c = ',' && depth = 0 then
          some (String.mk acc.reverse, String.mk cs)
        else
          go depth (c :: acc) cs
  go 0 [] s.toList

private def Ty.ofStringAux? : Nat → String → Option Ty
  | 0, _ => none
  | Nat.succ fuel, s =>
      let s := s.trim
      if s = "Nat" then
        some .nat
      else if s = "Int" then
        some .int
      else if s = "ListNat" || s = "List Nat" then
        some .listNat
      else if s = "UInt32" || s = "U32" then
        some .u32
      else if s.startsWith "Prod(" && s.endsWith ")" then
        let body := s.drop 5 |>.dropRight 1 |>.trim
        match splitTopComma? body with
        | none => none
        | some (aS, bS) =>
            match Ty.ofStringAux? fuel aS, Ty.ofStringAux? fuel bS with
            | some a, some b => some (.prod a b)
            | _, _ => none
      else
        none

def Ty.ofString? (s : String) : Option Ty :=
  Ty.ofStringAux? (Nat.succ s.length) s

/-- Minimal lens tags (expand later as transports land). -/
inductive Lens where
  | core
  | c
deriving DecidableEq, Inhabited, Repr

def Lens.toString : Lens → String
  | .core => "Core"
  | .c    => "C"

instance : ToString Lens := ⟨Lens.toString⟩

instance : ToJson Lens := ⟨fun t => Json.str t.toString⟩

def Lens.ofString? (s : String) : Option Lens :=
  let s := s.trim
  if s = "Core" || s = "core" then
    some .core
  else if s = "C" || s = "c" then
    some .c
  else
    none

/-- Dimensional logic tag (demo-level; aligns with the Symbolica/Symolica notes). -/
inductive Dimension where
  | D1_Heyting
  | D3_Classical
deriving DecidableEq, Inhabited, Repr

def Dimension.toString : Dimension → String
  | .D1_Heyting   => "D1_Heyting"
  | .D3_Classical => "D3_Classical"

instance : ToString Dimension := ⟨Dimension.toString⟩

instance : ToJson Dimension := ⟨fun t => Json.str t.toString⟩

def Dimension.ofString? (s : String) : Option Dimension :=
  let s := s.trim
  if s = "D1_Heyting" then
    some .D1_Heyting
  else if s = "D3_Classical" then
    some .D3_Classical
  else
    none

end Certified
end HeytingLean
