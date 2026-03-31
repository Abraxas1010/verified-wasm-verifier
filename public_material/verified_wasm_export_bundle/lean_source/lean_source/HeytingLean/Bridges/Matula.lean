import HeytingLean.Bridges.Graph
import HeytingLean.Matula.Algebra.HeytingCore
import HeytingLean.Matula.Compute.Decoder
import HeytingLean.Matula.Compute.Encoder

namespace HeytingLean
namespace Bridges
namespace Matula

open HeytingLean.Contracts
open HeytingLean.Matula
open HeytingLean.Matula.Algebra

/-- Bridge carrier is the Phase II Matula nucleus carrier. -/
abbrev Carrier := HeytingCore.Carrier

/-- Reentry used by the Matula bridge. -/
noncomputable abbrev R := HeytingCore.R

/-- Fixed-point domain for the Matula bridge. -/
abbrev Omega := HeytingCore.Omega

/-- Matula bridge encoder (inherits the Phase II contract). -/
noncomputable def encode : Omega → Carrier :=
  HeytingCore.encode

/-- Matula bridge decoder (inherits the Phase II contract). -/
noncomputable def decode : Carrier → Omega :=
  HeytingCore.decode

/-- RoundTrip contract required for bridge-level transport composition. -/
noncomputable def contract : RoundTrip (R := R) Carrier :=
  HeytingCore.contract

@[simp] theorem decode_encode (a : Omega) : decode (encode a) = a :=
  HeytingCore.decode_encode a

/-- Executable projection of rooted trees to their Matula code. -/
def toPlatoTree : RTree → Nat :=
  matulaEncode

/-- Executable reconstruction of rooted trees from Matula code. -/
def fromPlatoTree : Nat → RTree :=
  matulaDecode

/--
Graph transport path for WS3:
instantiate `Bridges.Graph.Model` on the same Matula carrier and use
identity transport between bridge-local carrier aliases.
-/
noncomputable def graphModel : Graph.Model Carrier where
  R := R

abbrev GraphCarrier : Type := graphModel.Carrier

noncomputable def toGraph : Carrier → GraphCarrier := id
noncomputable def fromGraph : GraphCarrier → Carrier := id

@[simp] theorem fromGraph_toGraph (x : Carrier) : fromGraph (toGraph x) = x := rfl
@[simp] theorem toGraph_fromGraph (x : GraphCarrier) : toGraph (fromGraph x) = x := rfl

/-- RT-1 style carrier-level transport check (`from ∘ to = id`). -/
@[simp] theorem rt1 (x : Carrier) : fromGraph (toGraph x) = x := rfl

/-- RT-2 style carrier-level transport check (`to ∘ from = id`). -/
@[simp] theorem rt2 (x : GraphCarrier) : toGraph (fromGraph x) = x := rfl

end Matula
end Bridges
end HeytingLean
