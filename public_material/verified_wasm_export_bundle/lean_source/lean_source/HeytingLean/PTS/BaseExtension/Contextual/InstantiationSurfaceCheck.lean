import HeytingLean.PTS.BaseExtension.Contextual.Derives

namespace HeytingLean.PTS.BaseExtension.Contextual

/-!
# Bounded executable check for universal-instantiation

This file does not prove `derives_all_elim`. It checks the executable kernel
surface for shallow counterexamples to the search-level analogue:

`SearchSupports P (.all g) -> SearchSupports P (substGoal g 0 atm)`.

Any discovered counterexample would refute the theorem-level target outright.
-/

def instantiationCheckAtoms : List Atom :=
  [⟨0⟩, ⟨1⟩]

def instantiationCheckAtomVars : List AtomVar :=
  instantiationCheckAtoms.map AtomVar.atom ++ [.bvar 0]

def instantiationConcatMap {α β : Type} (xs : List α) (f : α → List β) : List β :=
  match xs with
  | [] => []
  | x :: xs => f x ++ instantiationConcatMap xs f

def instantiationCheckGoals : Nat → List Goal
  | 0 => instantiationCheckAtomVars.map Goal.atom
  | n + 1 =>
      let prev := instantiationCheckGoals n
      prev ++
        instantiationConcatMap prev (fun g₁ => prev.map fun g₂ => Goal.imp g₁ g₂) ++
        prev.map Goal.all

def instantiationCheckPrograms (goals : List Goal) : List Program :=
  [[]] ++ goals.map List.singleton ++
    instantiationConcatMap goals (fun g₁ => goals.map fun g₂ => [g₁, g₂])

def searchSupportsUpTo (fuelMax : Nat) (P : Program) (g : Goal) : Bool :=
  (List.range (fuelMax + 1)).any fun fuel => search fuel P g

def boundedInstantiationCounterexamples (fuelMax depth : Nat) :
    List (Program × Goal × Atom) :=
  let goals := instantiationCheckGoals depth
  let programs := instantiationCheckPrograms goals
  instantiationConcatMap programs <| fun P =>
    instantiationConcatMap goals <| fun g =>
      instantiationCheckAtoms.filterMap fun atm =>
        if searchSupportsUpTo fuelMax P (.all g) &&
            !(searchSupportsUpTo fuelMax P (substGoal g 0 atm)) then
          some (P, g, atm)
        else
          none

def boundedInstantiationCounterexampleCount (fuelMax depth : Nat) : Nat :=
  (boundedInstantiationCounterexamples fuelMax depth).length

example : boundedInstantiationCounterexampleCount 12 1 = 0 := by
  native_decide

def boundedReverseInstantiationCounterexamples (fuelMax depth : Nat) :
    List (Program × Goal × Atom) :=
  let goals := instantiationCheckGoals depth
  let programs := instantiationCheckPrograms goals
  instantiationConcatMap programs <| fun P =>
    instantiationConcatMap goals <| fun g =>
      let c := freshAtomForGoal P g
      instantiationCheckAtoms.filterMap fun atm =>
        if searchSupportsUpTo fuelMax P (substGoal g 0 c) &&
            !(searchSupportsUpTo fuelMax P (substGoal g 0 atm)) then
          some (P, g, atm)
        else
          none

def boundedReverseInstantiationCounterexampleCount (fuelMax depth : Nat) : Nat :=
  (boundedReverseInstantiationCounterexamples fuelMax depth).length

example : boundedReverseInstantiationCounterexampleCount 12 1 = 0 := by
  native_decide

end Contextual
end HeytingLean.PTS.BaseExtension
