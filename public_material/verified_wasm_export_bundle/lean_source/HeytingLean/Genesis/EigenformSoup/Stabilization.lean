import HeytingLean.Genesis.EigenformSoup.Interaction

open scoped Classical

/-!
# Genesis.EigenformSoup.Stabilization

WS3 stabilization and replication layer.
-/

namespace HeytingLean.Genesis.EigenformSoup

/-- Eigenform predicate at soup level: nucleus fixedness of a support carrier. -/
abbrev isEigenform (nuc : SoupNucleus) (S : Support) : Prop :=
  isFixed nuc S

/-- Stabilization event extracted from one epoch. -/
structure StabilizationEvent (nuc : SoupNucleus) where
  epoch : Nat
  thesis : Support
  antithesis : Support
  support : Support
  fixed : isEigenform nuc support

/-- Build stabilization events from interaction outputs at a given epoch. -/
def stabilizationEvents
    (nuc : SoupNucleus)
    (epoch : Nat)
    (events : List (InteractionEvent nuc)) :
    List (StabilizationEvent nuc) :=
  events.map
    (fun ev =>
      { epoch := epoch
        thesis := thesisSupport nuc ev
        antithesis := antithesisSupport nuc ev
        support := synthesisSupport nuc ev
        fixed := by
          simpa [isEigenform] using synthesisSupport_fixed (nuc := nuc) ev })

theorem stabilizationEvent_support_eq_synthesis
    {nuc : SoupNucleus}
    (epoch : Nat)
    (ev : InteractionEvent nuc) :
    (stabilizationEvents nuc epoch [ev]).head?.map (fun e => e.support) =
      some (synthesisSupport nuc ev) := by
  simp [stabilizationEvents]

/-- Replication rate measured as number of fixed supports in a finite history. -/
noncomputable def replicationRate (nuc : SoupNucleus) (history : List Support) : Nat :=
  history.countP (fun S => isEigenform nuc S)

/-- Replicative eigenform criterion over finite trace history. -/
def isReplicativeEigenform
    (nuc : SoupNucleus)
    (history : List Support)
    (threshold : Nat) : Prop :=
  replicationRate nuc history ≥ threshold

theorem stabilizationEvent_sound {nuc : SoupNucleus} (e : StabilizationEvent nuc) :
    isEigenform nuc e.support :=
  e.fixed

theorem supports_from_interactions_are_eigenforms
    {nuc : SoupNucleus}
    (events : List (InteractionEvent nuc))
    (S : Support)
    (hS : S ∈ stabilizedSupports nuc events) :
    isEigenform nuc S :=
  mem_stabilizedSupports_fixed (nuc := nuc) (events := events) (S := S) hS

theorem replicationRate_mono_append
    (nuc : SoupNucleus)
    (xs ys : List Support) :
    replicationRate nuc xs ≤ replicationRate nuc (xs ++ ys) := by
  unfold replicationRate
  rw [List.countP_append]
  exact Nat.le_add_right (xs.countP fun S => isEigenform nuc S)
    (ys.countP fun S => isEigenform nuc S)

end HeytingLean.Genesis.EigenformSoup
