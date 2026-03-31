import HeytingLean.Physics.FreeWill.KochenSpecker

set_option autoImplicit false

namespace HeytingLean.Physics.FreeWill

/-- A LoF marking over Peres directions (`true`=marked, `false`=unmarked). -/
abbrev LoFMarking : Type := Dir → Bool

/-- LoF local law: each orthogonal frame has exactly one unmarked direction. -/
def LoFFrameLaw (μ : LoFMarking) : Prop :=
  ∀ f : PeresFrame, ExactlyOneFalse (μ f.x) (μ f.y) (μ f.z)

/-- In this encoding, the LoF frame law is exactly the `Is101` condition. -/
theorem lofFrameLaw_iff_is101 (μ : LoFMarking) :
    LoFFrameLaw μ ↔ Is101 Orth μ := by
  rfl

/-- No global LoF marking satisfies the Peres frame law. -/
theorem no_global_lof_marking : ¬ ∃ μ : LoFMarking, LoFFrameLaw μ := by
  intro h
  apply no101_peres33
  simpa [LoFFrameLaw] using h

/-- Equivalent exported spelling for ontology-facing layers. -/
theorem no_global_marking_for_peres : ¬ ∃ μ : LoFMarking, LoFFrameLaw μ :=
  no_global_lof_marking

end HeytingLean.Physics.FreeWill
