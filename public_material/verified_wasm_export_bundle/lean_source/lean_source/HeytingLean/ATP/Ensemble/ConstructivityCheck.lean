import HeytingLean.ATP.Ensemble.HHResolver

namespace HeytingLean
namespace ATP
namespace Ensemble

open PTS.BaseExtension

structure ConstructivityReport where
  fuel : Nat
  accepted : Bool
  peirceRejected : Bool
  doubleNegationRejected : Bool
  deriving Repr

def defaultFuel : Nat := 7

def rejectsPeirce (fuel : Nat := defaultFuel) : Bool :=
  hh_search fuel [] (extractPeirce ⟨0⟩ ⟨1⟩) = false

def rejectsDoubleNegationElim (fuel : Nat := defaultFuel) : Bool :=
  hh_search fuel [] (extractDoubleNegationElim ⟨0⟩) = false

def checkSkeleton (fuel : Nat := defaultFuel) (P : Program) (s : GoalSkeleton) : ConstructivityReport :=
  { fuel := fuel
    accepted := hh_search fuel P s
    peirceRejected := rejectsPeirce fuel
    doubleNegationRejected := rejectsDoubleNegationElim fuel }

example : rejectsPeirce = true := by
  have h : search defaultFuel [] (encode (peirceFormula ⟨0⟩ ⟨1⟩)) = false := by
    native_decide
  simpa [rejectsPeirce, defaultFuel, hh_search, extractPeirce, peirceFormula] using h

example : rejectsDoubleNegationElim = true := by
  have h : search defaultFuel [] (encode (.imp (.imp (.imp (.atom ⟨0⟩) .bot) .bot) (.atom ⟨0⟩))) = false := by
    native_decide
  simpa [rejectsDoubleNegationElim, defaultFuel, hh_search, extractDoubleNegationElim, GoalSkeleton.toIPL] using h

example : (checkSkeleton 5 [] (extractIdentity ⟨0⟩)).accepted = true := by
  have h : search 5 [] (encode (identityFormula ⟨0⟩)) = true := by
    native_decide
  simpa [checkSkeleton, hh_search, extractIdentity, identityFormula] using h

end Ensemble
end ATP
end HeytingLean
