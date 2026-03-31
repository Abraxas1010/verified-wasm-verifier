import Mathlib.Order.Hom.Basic
import Mathlib.Data.Fin.SuccPredOrder

/-!
# Bridge.Veselov.DAOFRatchet

Constructive P2 bridge surface:
- a 4-valued DAOF carrier,
- a 4-stage ratchet carrier,
- explicit order isomorphism.
-/

namespace HeytingLean.Bridge.Veselov

/-- DAOF carrier encoded as four ordered truth-status levels. -/
abbrev DAOFValue : Type := Fin 4

/-- Ratchet carrier encoded as four ordered stages. -/
abbrev RatchetStage : Type := Fin 4

/-- DAOF bottom stage. -/
def daofBottom : DAOFValue := ⟨0, by decide⟩

/-- DAOF top stage. -/
def daofTop : DAOFValue := ⟨3, by decide⟩

/-- Ordered-set isomorphism witness (P2 core). -/
abbrev daofRatchetOrderIso : DAOFValue ≃o RatchetStage :=
  OrderIso.refl _

/-- Component-level order preservation. -/
theorem daof_to_ratchet_monotone {a b : DAOFValue} (h : a ≤ b) :
    daofRatchetOrderIso a ≤ daofRatchetOrderIso b := h

/-- Component-level order reflection. -/
theorem daof_to_ratchet_reflects {a b : DAOFValue}
    (h : daofRatchetOrderIso a ≤ daofRatchetOrderIso b) :
    a ≤ b := h

/-- P2 packaged theorem: DAOF and ratchet are isomorphic ordered sets. -/
theorem daof_ratchet_isomorphic : Nonempty (DAOFValue ≃o RatchetStage) :=
  ⟨daofRatchetOrderIso⟩

/-- Transport a DAOF endomorphism across the DAOF↔ratchet order isomorphism. -/
def transportToRatchet (f : DAOFValue →o DAOFValue) : RatchetStage →o RatchetStage where
  toFun := fun r => daofRatchetOrderIso (f (daofRatchetOrderIso.symm r))
  monotone' := by
    intro a b hab
    exact daofRatchetOrderIso.monotone (f.monotone (daofRatchetOrderIso.symm.monotone hab))

/--
P2 naturality theorem: transporting a DAOF endomorphism to ratchet space
commutes with the DAOF↔ratchet order-isomorphism map.
-/
@[simp] theorem daof_ratchet_naturality
    (f : DAOFValue →o DAOFValue) (a : DAOFValue) :
    transportToRatchet f (daofRatchetOrderIso a) = daofRatchetOrderIso (f a) :=
  rfl

end HeytingLean.Bridge.Veselov
