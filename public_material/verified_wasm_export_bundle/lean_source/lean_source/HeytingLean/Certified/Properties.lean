import Lean
import Lean.Data.Json
import Mathlib.Data.Set.Basic
import HeytingLean.Certified.Types

namespace HeytingLean
namespace Certified

open Lean

/-- Searchable properties (demo subset). -/
inductive Property where
  | boundedNat (lo hi : Nat)
  | monotone
  | conservative
  | nonnegInt
  | custom (name : String)
deriving DecidableEq, Inhabited, Repr

def Property.toString : Property → String
  | .boundedNat lo hi => s!"BoundedNat({lo},{hi})"
  | .monotone         => "Monotone"
  | .conservative     => "Conservative"
  | .nonnegInt        => "NonnegInt"
  | .custom name      => s!"Custom({name})"

instance : ToString Property := ⟨Property.toString⟩

instance : ToJson Property := ⟨fun p => Json.str p.toString⟩

def Property.ofString? (s : String) : Option Property :=
  let s := s.trim
  let parseBounds (pfx : String) : Option Property :=
    if s.startsWith pfx && s.endsWith ")" then
      let body := s.drop pfx.length |>.dropRight 1
      match body.splitOn "," with
      | [loS, hiS] =>
          match loS.trim.toNat?, hiS.trim.toNat? with
          | some lo, some hi => some (.boundedNat lo hi)
          | _, _ => none
      | _ => none
    else
      none
  parseBounds "BoundedNat(" <|> parseBounds "Bounded(" <|>
    (if s = "Monotone" then some .monotone else none) <|>
    (if s = "Conservative" then some .conservative else none) <|>
    (if s = "NonnegInt" then some .nonnegInt else none) <|>
    if s.startsWith "Custom(" && s.endsWith ")" then
      some (.custom (s.drop 7 |>.dropRight 1))
    else
      none

/-- Semantics: when a property makes sense for a given typed function. -/
def Property.Holds (p : Property) (dom cod : Ty) (fn : dom.interp → cod.interp) : Prop :=
  match p with
  | .boundedNat lo hi =>
      match cod with
      | .nat =>
          ∀ x : dom.interp, lo ≤ fn x ∧ fn x ≤ hi
      | _ =>
          False
  | .monotone =>
      match dom, cod with
      | .nat, .nat => Monotone fn
      | .nat, .int => Monotone fn
      | .int, .int => Monotone fn
      | .int, .nat => Monotone fn
      | _, _ => False
  | .conservative =>
      match dom, cod with
      | .nat, .nat => ∀ x : Nat, fn x = x
      | .int, .int => ∀ x : Int, fn x = x
      | _, _ => False
  | .nonnegInt =>
      match cod with
      | .int =>
          ∀ x : dom.interp, (0 : Int) ≤ fn x
      | _ => False
  | .custom _ =>
      True

/-- Properties stable under precomposition (closed under `f ↦ f ∘ g`). -/
def Property.precompStable : Property → Bool
  | .boundedNat _ _ => true
  | .nonnegInt      => true
  | .custom _       => true
  | _               => false

/-- A `Set Nat` view for range-style properties (used by modality filters). -/
def Property.toNatSet? : Property → Option (Set Nat)
  | .boundedNat lo hi => some { n : Nat | lo ≤ n ∧ n ≤ hi }
  | .monotone         => none
  | .conservative     => none
  | .nonnegInt        => none
  | .custom _         => none

end Certified
end HeytingLean
