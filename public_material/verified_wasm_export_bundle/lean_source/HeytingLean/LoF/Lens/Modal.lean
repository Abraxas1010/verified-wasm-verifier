import Mathlib.Data.Set.Lattice

open scoped Classical

namespace HeytingLean.LoF.Lens

/-- A Kripke frame with carrier `W` and accessibility relation `R`. -/
structure Frame (W : Type _) where
  R : W → W → Prop

namespace Modal

variable {W : Type _} (F : Frame W)

/-- Box-interior: points whose successors all lie in `X`. -/
def I (X : Set W) : Set W :=
  { w | ∀ v, F.R w v → v ∈ X }

variable {F}

@[simp] lemma mem_I_iff {X : Set W} {w : W} : w ∈ I (F := F) X ↔ ∀ v, F.R w v → v ∈ X := Iff.rfl

lemma subset_of_reflexive (X : Set W) (hRefl : ∀ w, F.R w w) : I (F := F) X ⊆ X := by
  intro w hw
  have : w ∈ X := (mem_I_iff (F := F) (X := X)).mp hw w (hRefl w)
  simpa using this

lemma monotone {X Y : Set W} (hXY : X ⊆ Y) : I (F := F) X ⊆ I (F := F) Y := by
  intro w hw v hv
  exact hXY ((mem_I_iff (F := F) (X := X)).mp hw v hv)

lemma idempotent (X : Set W)
    (hRefl : ∀ w, F.R w w)
    (hTrans : ∀ {u v z}, F.R u v → F.R v z → F.R u z) :
    I (F := F) (I (F := F) X) = I (F := F) X := by
  apply Set.Subset.antisymm
  · intro w hw v hv
    have hvIX : v ∈ I (F := F) X := (mem_I_iff (F := F) (X := I (F := F) X)).mp hw v hv
    exact (mem_I_iff (F := F) (X := X)).mp hvIX v (hRefl v)
  · intro w hw v hv
    refine (mem_I_iff (F := F) (X := X)).mpr ?_
    intro z hz
    exact (mem_I_iff (F := F) (X := X)).mp hw z (hTrans hv hz)

lemma inf_preserving (X Y : Set W) :
  I (F := F) (X ∩ Y) = I (F := F) X ∩ I (F := F) Y := by
  ext w
  constructor
  · intro hw
    constructor
    · intro v hv
      exact ((mem_I_iff (F := F) (X := X ∩ Y)).mp hw v hv).1
    · intro v hv
      exact ((mem_I_iff (F := F) (X := X ∩ Y)).mp hw v hv).2
  · intro hw
    rcases hw with ⟨hX, hY⟩
    exact (mem_I_iff (F := F) (X := X ∩ Y)).mpr (fun v hv => ⟨hX v hv, hY v hv⟩)

/-- Polarity-reversed dual closure generated from the modal interior `I`. -/
def dualClosure (X : Set W) : Set W :=
  (I (F := F) Xᶜ)ᶜ

/-- The dual-closure is definitionally the complement of interior on complement. -/
@[simp] lemma dualClosure_eq_compl_interior_compl (X : Set W) :
    dualClosure (F := F) X = (I (F := F) Xᶜ)ᶜ := rfl

/-- Interior is complement-of-dual-closure on complement (polarity reversal). -/
@[simp] lemma interior_eq_compl_dualClosure_compl (X : Set W) :
    I (F := F) X = (dualClosure (F := F) Xᶜ)ᶜ := by
  ext w
  simp [dualClosure]

/--
Queue anchor theorem for `ontology_closure_interior_duality_20260219`:
polarity reverses through complement.
--/
theorem ontology_closure_interior_duality_20260219 {W : Type _} (F : Frame W) (X : Set W) :
    I (F := F) X = (dualClosure (F := F) Xᶜ)ᶜ :=
  interior_eq_compl_dualClosure_compl (F := F) (X := X)

end Modal

end HeytingLean.LoF.Lens
