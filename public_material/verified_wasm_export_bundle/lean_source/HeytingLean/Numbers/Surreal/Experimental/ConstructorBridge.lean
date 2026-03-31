import HeytingLean.Constructor.SurrealAdapter

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Experimental

open HeytingLean.Constructor
open HeytingLean.Constructor.SurrealAdapter
open HeytingLean.Numbers.SurrealCore

/-- Constructor-theory network alias on the Surreal adapter carrier. -/
abbrev CNetwork : Type := Network

/-- Canonical atom used by the Surreal constructor bridge. -/
def canonicalAtom : CNetwork := .atom canonicalCore

theorem possible_rcl (S : Carrier) :
    Constructor.possible Rcl S := by
  intro hBot
  have hMem : PreGame.build [] [] ∈ Rcl S :=
    build_in_closure (S := S)
  simp [hBot] at hMem

theorem canonicalAtom_regular : networkRegular canonicalAtom := by
  simp [canonicalAtom, networkRegular]
  exact possible_rcl canonicalCore

theorem canonicalAtom_composes_possible :
    Constructor.possible Rcl (networkDenote canonicalAtom) := by
  letI := surrealMeta
  apply Constructor.Meta.composition_principle (R := Rcl) (N := canonicalAtom)
  · exact canonicalAtom_regular
  · intro a _ha
    exact possible_rcl a

end Experimental
end Surreal
end Numbers
end HeytingLean
