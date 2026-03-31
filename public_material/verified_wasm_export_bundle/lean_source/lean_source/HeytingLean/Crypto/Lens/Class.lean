import HeytingLean.Contracts.RoundTrip
import HeytingLean.Bridges.Tensor
import HeytingLean.Bridges.Graph
import HeytingLean.Bridges.Clifford

namespace HeytingLean
namespace Crypto

open HeytingLean.LoF

universe u v w

variable {α : Type u} [PrimaryAlgebra α]

/-- Uniform interface bundling a bridge carrier together with its certified round-trip. -/
structure Lens (R : Reentry α) where
  Carrier : Type v
  contract : Contracts.RoundTrip (R := R) Carrier

namespace Lens

variable {R : Reentry α} (L : Lens (R := R))

def enc : R.Omega → L.Carrier :=
  L.contract.encode

def dec : L.Carrier → R.Omega :=
  L.contract.decode

@[simp] lemma dec_enc (a : R.Omega) :
    L.dec (L.enc a) = a :=
  L.contract.round a

noncomputable def logicalShadow : L.Carrier → α :=
  Contracts.interiorized (R := R) L.contract

@[simp] lemma logicalShadow_enc (a : R.Omega) :
    L.logicalShadow (L.enc a) = ((a : R.Omega) : α) := by
  unfold logicalShadow Lens.enc Contracts.interiorized
  simp [Reentry.Omega.apply_coe, L.contract.round]

/-- Lift booleans/constants/operations through the round-trip, keeping decoding compositional. -/
def top : L.Carrier := L.enc ⊤

def bot : L.Carrier := L.enc ⊥

def and (x y : L.Carrier) : L.Carrier :=
  L.enc (L.dec x ⊓ L.dec y)

def or (x y : L.Carrier) : L.Carrier :=
  L.enc (L.dec x ⊔ L.dec y)

def imp (x y : L.Carrier) : L.Carrier :=
  L.enc (L.dec x ⇨ L.dec y)

@[simp] lemma dec_top :
    L.dec L.top = (⊤ : R.Omega) := by
  simp [Lens.top]

@[simp] lemma dec_bot :
    L.dec L.bot = (⊥ : R.Omega) := by
  simp [Lens.bot]

@[simp] lemma dec_and (x y : L.Carrier) :
    L.dec (L.and x y) = L.dec x ⊓ L.dec y := by
  simp [Lens.and]

@[simp] lemma dec_or (x y : L.Carrier) :
    L.dec (L.or x y) = L.dec x ⊔ L.dec y := by
  simp [Lens.or]

@[simp] lemma dec_imp (x y : L.Carrier) :
    L.dec (L.imp x y) = L.dec x ⇨ L.dec y := by
  simp [Lens.imp]

end Lens

namespace Lens
namespace Instances

open HeytingLean.Bridges

noncomputable def tensor (M : Tensor.Model α) :
    Lens (R := M.R) :=
  { Carrier := M.Carrier
    contract := M.contract }

noncomputable def graph (M : Graph.Model α) :
    Lens (R := M.R) :=
  { Carrier := M.Carrier
    contract := M.contract }

noncomputable def clifford (M : Clifford.Model α) :
    Lens (R := M.R) :=
  { Carrier := M.Carrier
    contract := M.contract }

end Instances
end Lens

end Crypto
end HeytingLean
