/-!
# Genesis.EigenformSoup.DependencyAudit

WS0 dependency/name reconciliation table for LES implementation.
-/

namespace HeytingLean.Genesis.EigenformSoup

/-- Resolution status for LES dependency labels. -/
inductive BindingStatus
  | mapped
  | missing
deriving DecidableEq, Repr

/-- One LES dependency mapped to the in-repo symbol/module target. -/
structure DependencyBinding where
  lesName : String
  repoTarget : String
  status : BindingStatus
  note : String := ""
deriving DecidableEq, Repr

/-- Core LES mapping table used during WS0/WS1 implementation. -/
def coreBindings : List DependencyBinding :=
  [ { lesName := "LoF.Axioms"
      repoTarget := "HeytingLean/LoF/Axioms/GenerativeLaws.lean"
      status := .mapped }
  , { lesName := "LoF.Reentry"
      repoTarget := "HeytingLean/LoF/Nucleus.lean"
      status := .mapped }
  , { lesName := "Genesis.Stabilization"
      repoTarget := "HeytingLean/Genesis/Stabilization.lean"
      status := .mapped }
  , { lesName := "Genesis.Observer"
      repoTarget := "HeytingLean/Genesis/Observer.lean"
      status := .mapped }
  , { lesName := "Knot.Transport"
      repoTarget := "HeytingLean/Topology/Knot/VirtualTransport.lean"
      status := .mapped }
  , { lesName := "Plenum.Projection"
      repoTarget := "HeytingLean/PerspectivalPlenum/ProjectionObligations.lean"
      status := .mapped }
  , { lesName := "Soup.CLI"
      repoTarget := "HeytingLean/Genesis/EigenformSoup/Main.lean"
      status := .mapped }
  ]

/-- Any unresolved mapping obligations in the current implementation milestone. -/
def missingBindings : List DependencyBinding :=
  coreBindings.filter (fun b => b.status = .missing)

/-- All mapped bindings (used for milestone readiness checks). -/
def mappedBindings : List DependencyBinding :=
  coreBindings.filter (fun b => b.status = .mapped)

theorem missingBindings_subset_core :
    ∀ b, b ∈ missingBindings → b ∈ coreBindings := by
  intro b hb
  simpa [missingBindings] using (List.mem_filter.mp hb).1

theorem mappedBindings_subset_core :
    ∀ b, b ∈ mappedBindings → b ∈ coreBindings := by
  intro b hb
  simpa [mappedBindings] using (List.mem_filter.mp hb).1

end HeytingLean.Genesis.EigenformSoup
