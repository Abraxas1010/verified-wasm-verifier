import HeytingLean.Embeddings.GenericCrossLensTransport
import HeytingLean.Embeddings.CrossLensTransport
import HeytingLean.PerspectivalPlenum.SheafLensCategory
import HeytingLean.QuantumActiveInference.SheafGluing
import HeytingLean.LoF.Combinators.InfinityGroupoid.SSet

/-!
# PerspectivalPlenum.PDCDescentBridge

Bridge transport-level PDC data into lens-site descent language.
-/

namespace HeytingLean
namespace PerspectivalPlenum

open CategoryTheory
open HeytingLean.Embeddings
open HeytingLean.Embeddings.GenericCrossLensTransport
open HeytingLean.PerspectivalPlenum.LensSheaf

universe u v

/-- Canonical coverage choice: use `pairCover` at each lens object. -/
def pdcCoverage (A : Type u) : (U : LensObj A) → CoveringFamily U :=
  fun U => pairCover U

/-- Constant presheaf over the lens category. -/
def constantLensPresheaf (A : Type u) (P : Type u) : LensPresheaf A where
  obj _ := P
  map := by
    intro U V f
    exact id
  map_id := by
    intro U
    rfl
  map_comp := by
    intro U V W f g
    rfl

/-- Trivial base object for transport-to-descent translation. -/
def trivialLensObj (A : Type u) : LensObj A where
  lens :=
    { profile :=
        { name := "pdc-trivial"
          contradictionPolicy := Lens.ContradictionPolicy.paraconsistent
          dimension := 0
          languageTag := "pdc"
          metricTag := "" }
      witness := fun _ => True
      contradicts := fun _ => False }

/--
Convert a transport gluing pair into a matching family over a pair cover for
the constant-presheaf lens-site view.
-/
def transportMatchingFamily
    {Carrier : LensID → Type} {Plato : Type}
    (T : GenericTransport LensID Carrier Plato)
    (l1 l2 : LensID) (x : Carrier l1) (y : Carrier l2) :
    MatchingFamily
      (constantLensPresheaf LensID Plato)
      (trivialLensObj LensID)
      (pairCover (trivialLensObj LensID)) where
  sec i := by
    cases i with
    | false => exact T.toPlato l1 x
    | true => exact T.toPlato l2 y

/-- Reinterpret a generic LensID transport as the legacy cross-lens transport. -/
def toLegacyCrossLensTransport
    {Carrier : LensID → Type} {Plato : Type}
    (T : GenericTransport LensID Carrier Plato) :
    CrossLensTransport Carrier Plato where
  toPlato := T.toPlato
  fromPlato := T.fromPlato
  rt1 := T.rt1
  rt2 := T.rt2

/-- Legacy sheaf gluing condition is exactly Plato-level equality. -/
theorem gluingCondition_iff_transport_eq
    {Carrier : LensID → Type} {Plato : Type}
    (T : GenericTransport LensID Carrier Plato)
    (l1 l2 : LensID) (x : Carrier l1) (y : Carrier l2) :
    QuantumActiveInference.GluingCondition (toLegacyCrossLensTransport T) l1 l2 x y
      ↔ T.toPlato l1 x = T.toPlato l2 y :=
  Iff.rfl

/-- Transport gluing equality induces pair-cover amalgamation. -/
theorem transport_gluing_to_pairCover_amalgamates
    {Carrier : LensID → Type} {Plato : Type}
    (T : GenericTransport LensID Carrier Plato)
    (l1 l2 : LensID) (x : Carrier l1) (y : Carrier l2)
    (hGlue : T.toPlato l1 x = T.toPlato l2 y) :
    Amalgamates
      (constantLensPresheaf LensID Plato)
      (trivialLensObj LensID)
      (pairCover (trivialLensObj LensID))
      (transportMatchingFamily T l1 l2 x y) := by
  refine ⟨T.toPlato l1 x, ?_⟩
  intro i
  cases i with
  | false =>
      simp [transportMatchingFamily, constantLensPresheaf, pairCover]
  | true =>
      simpa [transportMatchingFamily, constantLensPresheaf, pairCover] using hGlue

/-- Transport cocycle law in descent-friendly naming. -/
theorem transport_forward_cocycle
    {τ : Type u} {Carrier : τ → Type v} {Plato : Type v}
    (T : GenericTransport τ Carrier Plato) :
    GenericTransport.ForwardCocycle T :=
  GenericTransport.forward_comp_is_cocycle T

/-- `SKYInfty` carries quasicategory descent data. -/
theorem skyInfty_supports_quasicategory_descent :
    SSet.Quasicategory HeytingLean.LoF.Combinators.InfinityGroupoid.SKYInfty := by
  infer_instance

end PerspectivalPlenum
end HeytingLean
