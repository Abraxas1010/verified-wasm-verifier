import HeytingLean.ATP.DifferentiableATP.SheafResolution
import HeytingLean.Embeddings.PerspectivalDescentCarrier

/-!
# ATP.DifferentiableATP.SheafTransport

Lax cross-lens transport for multi-scale sheaf resolution.

Strict RT-2 cannot hold for non-trivial restriction maps, so we use an
idempotent round-trip contract instead of exact invertibility.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.Embeddings
open HeytingLean.LoF.Combinators.Differential.Compute

structure LaxCrossLensTransport (Carrier : LensID → Type) (Plato : Type) where
  toPlato : ∀ lens, Carrier lens → Plato
  fromPlato : ∀ lens, Plato → Carrier lens
  rt1_lax :
    ∀ lens (x : Carrier lens),
      fromPlato lens (toPlato lens x) =
        fromPlato lens (toPlato lens (fromPlato lens (toPlato lens x)))
  rt2_lax :
    ∀ lens (p : Plato),
      toPlato lens (fromPlato lens p) =
        toPlato lens (fromPlato lens (toPlato lens (fromPlato lens p)))

namespace LaxCrossLensTransport

variable {Carrier : LensID → Type} {Plato : Type}

def forward (T : LaxCrossLensTransport Carrier Plato) (src dst : LensID) :
    Carrier src → Carrier dst :=
  fun x => T.fromPlato dst (T.toPlato src x)

def backward (T : LaxCrossLensTransport Carrier Plato) (src dst : LensID) :
    Carrier dst → Carrier src :=
  fun y => T.fromPlato src (T.toPlato dst y)

/-- Lax transports induce a PDC structure via fixed points of local idempotent round-trips. -/
def toPDC (T : LaxCrossLensTransport Carrier Plato) :
    PerspectivalDescentCarrier LensID Carrier where
  integral lens := {x | T.fromPlato lens (T.toPlato lens x) = x}
  finiteness x := by
    refine
      (Finset.finite_toSet (s :=
        ({LensID.omega, LensID.region, LensID.graph, LensID.clifford,
          LensID.tensor, LensID.topology, LensID.matula} : Finset LensID))).subset ?_
    intro lens _
    cases lens <;> simp
  truncate lens _ x := T.fromPlato lens (T.toPlato lens x)

end LaxCrossLensTransport

abbrev SheafCarrier (_ : LensID) := FSum

def sheafTransport : LaxCrossLensTransport SheafCarrier FSum where
  toPlato := fun _ x => x
  fromPlato := fun lens p => lensProjection lens p
  rt1_lax := by
    intro lens x
    simpa using (lensProjection_idempotent lens x).symm
  rt2_lax := by
    intro lens p
    simpa using (lensProjection_idempotent lens p).symm

/-- Concrete PDC instance used by differentiable ATP sheaf transport. -/
instance sheafTransportPDC : PerspectivalDescentCarrier LensID SheafCarrier :=
  LaxCrossLensTransport.toPDC sheafTransport

theorem sheaf_forward_compose_of_subset
    (src mid dst : LensID)
    (x : FSum)
    (hsubset : basisSubset mid dst) :
    LaxCrossLensTransport.forward sheafTransport mid dst
      (LaxCrossLensTransport.forward sheafTransport src mid x) =
    LaxCrossLensTransport.forward sheafTransport src dst x := by
  simp [LaxCrossLensTransport.forward, sheafTransport, lensProjection]
  exact projectToBasis_compose_of_subset
    (fine := basisForLens mid)
    (coarse := basisForLens dst)
    (w := x)
    hsubset

theorem sheaf_forward_cocycle
    (a b c : LensID)
    (x : FSum)
    (hab : basisSubset a b)
    (hbc : basisSubset b c) :
    LaxCrossLensTransport.forward sheafTransport b c
      (LaxCrossLensTransport.forward sheafTransport a b x) =
    LaxCrossLensTransport.forward sheafTransport a c x := by
  let _ := hab
  exact sheaf_forward_compose_of_subset a b c x hbc

def sheafTransportMode : String :=
  "lax_sheaf_transport"

end DifferentiableATP
end ATP
end HeytingLean
