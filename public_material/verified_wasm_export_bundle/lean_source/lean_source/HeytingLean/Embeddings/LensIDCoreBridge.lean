import HeytingLean.Embeddings.Adelic
import HeytingLean.Embeddings.CoreLenses

namespace HeytingLean
namespace Embeddings
namespace LensIDCoreBridge

/-- Embed the 7 original `LensID` values into `CoreLensTag`.

Note: `LensID.region` intentionally maps to `CoreLensTag.radial`.
This preserves the legacy "region" slot while aligning with the expanded
core-lens naming in the new registry. -/
def toCoreLensTag : LensID → CoreLensTag
  | .omega => .omega
  | .region => .radial
  | .graph => .graph
  | .clifford => .clifford
  | .tensor => .tensor
  | .topology => .topology
  | .matula => .matula

/-- Partial inverse from `CoreLensTag` to `LensID`.
Returns `some` exactly on the 7 bridgeable tags. -/
def fromCoreLensTag? : CoreLensTag → Option LensID
  | .omega => some .omega
  | .radial => some .region
  | .graph => some .graph
  | .clifford => some .clifford
  | .tensor => some .tensor
  | .topology => some .topology
  | .matula => some .matula
  | _ => none

/-- Round-trip: `toCoreLensTag` then `fromCoreLensTag?` recovers the original `LensID`. -/
theorem fromCoreLensTag?_toCoreLensTag (l : LensID) :
    fromCoreLensTag? (toCoreLensTag l) = some l := by
  cases l <;> rfl

/-- The embedding `toCoreLensTag` is injective. -/
theorem toCoreLensTag_injective :
    Function.Injective toCoreLensTag := by
  intro a b hab
  have h' := congrArg fromCoreLensTag? hab
  simpa [fromCoreLensTag?_toCoreLensTag] using h'

/-- `LensTag` instance for `LensID` via the `CoreLensTag` bridge metadata. -/
instance : LensTag LensID where
  name l := CoreLensTag.nameOf (toCoreLensTag l)
  id l := CoreLensTag.idOf (toCoreLensTag l)
  description l := CoreLensTag.descriptionOf (toCoreLensTag l)

/-- All 7 legacy `LensID` values. -/
def allLensIDs : List LensID :=
  [.omega, .region, .graph, .clifford, .tensor, .topology, .matula]

/-- Every bridged `LensID` maps into `CoreLensTag.all`. -/
theorem toCoreLensTag_range :
    ∀ l : LensID, toCoreLensTag l ∈ CoreLensTag.all := by
  intro l
  cases l <;> simp [toCoreLensTag, CoreLensTag.all]

/-- Convert a `LensSet CoreLensTag` to its `LensID` subset through the bridge. -/
def lensSetToLensIDs (s : LensSet CoreLensTag) : List LensID :=
  allLensIDs.filter (fun l => s.contains (toCoreLensTag l))

/-- Lift a list of `LensID`s into a `LensSet CoreLensTag` through the bridge. -/
def lensIDsToLensSet (ls : List LensID) : LensSet CoreLensTag :=
  LensSet.ofList (ls.map toCoreLensTag)

end LensIDCoreBridge
end Embeddings
end HeytingLean
