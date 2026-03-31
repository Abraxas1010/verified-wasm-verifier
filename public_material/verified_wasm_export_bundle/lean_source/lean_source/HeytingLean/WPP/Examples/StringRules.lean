import Std

namespace HeytingLean
namespace WPP
namespace Examples

open Std

/-! # Simple string rewriting rules for WPP demos -/

structure StrRule where
  lhs : Char
  rhs : String

abbrev StrSystem := List StrRule

namespace StrRule

private def replaceAt (cs : List Char) (i : Nat) (rhs : List Char) : List Char :=
  (cs.take i) ++ rhs ++ (cs.drop (i+1))

private def enumerate (cs : List Char) : List (Nat × Char) := Id.run do
  let mut out : List (Nat × Char) := []
  let mut i := 0
  for c in cs do
    out := (i, c) :: out
    i := i + 1
  return out.reverse

def stepOne (r : StrRule) (s : String) : Array String := Id.run do
  let cs := s.data
  let rhs := r.rhs.data
  let mut out : Array String := #[]
  for (i, c) in (enumerate cs) do
    if c = r.lhs then
      let outStr := String.mk (replaceAt cs i rhs)
      out := out.push outStr
  return out

def step (sys : StrSystem) (s : String) : Array String :=
  sys.foldl (init := (#[] : Array String)) (fun acc r => acc ++ r.stepOne s)

def stepOneLabeled (r : StrRule) (s : String) : Array (String × String) := Id.run do
  let cs := s.data
  let rhs := r.rhs.data
  let mut out : Array (String × String) := #[]
  for (i, c) in (enumerate cs) do
    if c = r.lhs then
      let outStr := String.mk (replaceAt cs i rhs)
      let lab := s!"{r.lhs}@{i}"
      out := out.push (outStr, lab)
  return out

def stepLabeled (sys : StrSystem) (s : String) : Array (String × String) :=
  sys.foldl (init := (#[] : Array (String × String))) (fun acc r => acc ++ r.stepOneLabeled s)

/-! Example systems -/

def fibSys : StrSystem := [⟨'A', "AB"⟩, ⟨'B', "A"⟩]
def dupSys : StrSystem := [⟨'A', "AA"⟩, ⟨'B', "BB"⟩]
def simpleSys : StrSystem := [⟨'X', "XY"⟩]

end StrRule

end Examples
end WPP
end HeytingLean
