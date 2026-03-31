import Mathlib.Data.Set.Lattice
import HeytingLean.CPP.All
import HeytingLean.Quantum.QGIContext

namespace HeytingLean.Tests.CPP

open HeytingLean.CPP

/-! Smoke checks for the CPP weakness layer. -/

section SetBool

def H : Set (Bool × Bool) := { (true, false) }

def μ : Bool → MeetQuantale (Set Bool)
  | true => (({true} : Set Bool) : MeetQuantale (Set Bool))
  | false => (({false} : Set Bool) : MeetQuantale (Set Bool))

-- Regression guard: the CPP layer should *not* create a global `Mul` instance on `Set Bool`
-- (pointwise set multiplication is intentionally scoped in Mathlib).
example : True := by
  fail_if_success
    have : Mul (Set Bool) := inferInstance
  trivial

#check weakness (H := H) μ

example : weakness (H := (∅ : Set (Bool × Bool))) μ = (⊥ : MeetQuantale (Set Bool)) := by
  simp [weakness]

example : μ true * μ false ≤ weakness (H := H) μ := by
  apply mul_le_weakness (H := H) (μ := μ)
  simp [H]

end SetBool

section QuantumQGI

open HeytingLean.Quantum
open HeytingLean.Quantum.Translate
open HeytingLean.Quantum.QGIContext

-- Use the already-landed concrete QGI context: a coarse `QLMap` into `Set β`
-- with identity modality; its Ω-core is a frame, so the CPP layer applies.
noncomputable def T : QLMap β (Set β) := qgiQLMap

abbrev Ω : Type := Omega T.M

def μΩ (_ : Bool) : MeetQuantale Ω :=
  Omega.mk (M := T.M) (∅ : Set β) (by
    -- Identity modality: all sets are fixed points.
    simp [T, qgiQLMap, idModalitySetQGI])

def HΩ : Set (Bool × Bool) := { (true, false) }

#check weakness (H := HΩ) μΩ

example : μΩ true * μΩ false ≤ weakness (H := HΩ) μΩ := by
  apply mul_le_weakness (H := HΩ) (μ := μΩ)
  simp [HΩ]

end QuantumQGI

end HeytingLean.Tests.CPP
