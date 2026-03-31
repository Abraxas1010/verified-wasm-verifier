import Mathlib.Data.Int.Basic

namespace HeytingLean.Chem.Bonding

/-!
# Bond types (chemistry-facing)

This is a lightweight vocabulary layer for bonds that is independent of any
particular energetic model. Downstream layers can map these into Hamiltonians,
force fields, etc.
-/

inductive BondOrder where
  | single
  | double
  | triple
  | aromatic
deriving Repr, DecidableEq

namespace BondOrder

def weight : BondOrder → Nat
  | .single => 1
  | .double => 2
  | .triple => 3
  | .aromatic => 1

end BondOrder

inductive BondKind where
  | covalent
  | ionic
  | metallic
  | hydrogen
  | vanDerWaals
  | unknown
deriving Repr, DecidableEq

structure BondType where
  kind : BondKind := .unknown
  order : Option BondOrder := none
deriving Repr, DecidableEq

namespace BondType

def orderWeight (ty : BondType) : Nat :=
  match ty.order with
  | none => 1
  | some o => BondOrder.weight o

end BondType

end HeytingLean.Chem.Bonding
