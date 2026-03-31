import HeytingLean.Genesis.LatticeEmergence
import HeytingLean.Topos.JRatchet.FrameCore
import Mathlib.Order.Nucleus

/-!
# Genesis.LatticeNucleusBridge

Phase-3 bridge from emergent lattice regions to the canonical nucleus fixed-point core.
-/

namespace HeytingLean.Genesis

open CoGame

universe u

/-- Distinguished boundary class used for closure on emergent regions. -/
def anchorClass : EmergentClass := toEmergentClass CoGame.Void

/-- Closure nucleus on emergent regions (adds the boundary class). -/
def regionNucleus : Nucleus EmergentRegion where
  toInfHom :=
    { toFun := fun U => U ∪ ({anchorClass} : Set EmergentClass)
      map_inf' := by
        intro A B
        apply Set.ext
        intro x
        constructor
        · intro hx
          rcases hx with hx | hx
          · exact ⟨Or.inl hx.1, Or.inl hx.2⟩
          · exact ⟨Or.inr hx, Or.inr hx⟩
        · intro hx
          rcases hx with ⟨hxA, hxB⟩
          rcases hxA with hxA | hxA
          · rcases hxB with hxB | hxB
            · exact Or.inl ⟨hxA, hxB⟩
            · exact Or.inr hxB
          · exact Or.inr hxA }
  idempotent' := by
    intro U
    intro x hx
    simp at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  le_apply' := by
    intro U
    intro x hx
    exact Or.inl hx

@[simp] theorem regionNucleus_apply (U : EmergentRegion) :
    regionNucleus U = U ∪ ({anchorClass} : Set EmergentClass) := rfl

/-- Phase-3 emergent fixed carrier. -/
abbrev EmergentFixed := {U : EmergentRegion // regionNucleus U = U}

/-- Canonical fixed-point core from the nucleus. -/
abbrev LoFFixed := regionNucleus.toSublocale

/-- Forward map from explicit fixedness witness into `toSublocale`. -/
def emergent_to_lof_fixed (U : EmergentFixed) : LoFFixed :=
  ⟨U.1, U.1, U.2⟩

/-- Backward map from `toSublocale` into explicit fixedness witness. -/
def lof_to_emergent_fixed (V : LoFFixed) : EmergentFixed := by
  refine ⟨(V : EmergentRegion), ?_⟩
  rcases V with ⟨U, W, hW⟩
  change regionNucleus U = U
  calc
    regionNucleus U = regionNucleus (regionNucleus W) := by simp [hW]
    _ = regionNucleus W := Nucleus.idempotent (n := regionNucleus) (x := W)
    _ = U := by simp [hW]

@[simp] theorem emergent_to_lof_fixed_val (U : EmergentFixed) :
    ((emergent_to_lof_fixed U : LoFFixed) : EmergentRegion) = U.1 := rfl

@[simp] theorem lof_to_emergent_fixed_val (V : LoFFixed) :
    (lof_to_emergent_fixed V).1 = (V : EmergentRegion) := by
  rfl

/-- Fixed-point meet on explicit emergent fixed witnesses. -/
def emergent_fixed_inf (U V : EmergentFixed) : EmergentFixed := by
  refine ⟨U.1 ∩ V.1, ?_⟩
  calc
    regionNucleus (U.1 ∩ V.1) = regionNucleus U.1 ∩ regionNucleus V.1 := by
      exact Nucleus.map_inf (n := regionNucleus) (x := U.1) (y := V.1)
    _ = U.1 ∩ V.1 := by simp [U.2, V.2]

/-- Fixed-point top on explicit emergent fixed witnesses. -/
def emergent_fixed_top : EmergentFixed := by
  refine ⟨(Set.univ : EmergentRegion), ?_⟩
  ext x
  constructor
  · intro _; trivial
  · intro _; exact Or.inl trivial

/-- Meet in the `toSublocale` view via closure of ambient meet. -/
def lof_fixed_inf (U V : LoFFixed) : LoFFixed :=
  regionNucleus.toSublocale.restrict ((U : EmergentRegion) ∩ (V : EmergentRegion))

/-- Top in the `toSublocale` view. -/
def lof_fixed_top : LoFFixed :=
  regionNucleus.toSublocale.restrict (Set.univ : EmergentRegion)

@[simp] theorem lof_fixed_inf_val (U V : LoFFixed) :
    ((lof_fixed_inf U V : LoFFixed) : EmergentRegion)
      = regionNucleus ((U : EmergentRegion) ∩ (V : EmergentRegion)) := by
  calc
    ((lof_fixed_inf U V : LoFFixed) : EmergentRegion)
        = ((regionNucleus.toSublocale.restrict
            ((U : EmergentRegion) ∩ (V : EmergentRegion)) : LoFFixed) : EmergentRegion) := rfl
    _ = regionNucleus ((U : EmergentRegion) ∩ (V : EmergentRegion)) :=
      Topos.JRatchet.coe_restrict_toSublocale (n := regionNucleus)
        ((U : EmergentRegion) ∩ (V : EmergentRegion))

@[simp] theorem lof_fixed_top_val :
    ((lof_fixed_top : LoFFixed) : EmergentRegion) = regionNucleus (Set.univ : EmergentRegion) := by
  calc
    ((lof_fixed_top : LoFFixed) : EmergentRegion)
        = ((regionNucleus.toSublocale.restrict (Set.univ : EmergentRegion) : LoFFixed) :
            EmergentRegion) := rfl
    _ = regionNucleus (Set.univ : EmergentRegion) :=
      Topos.JRatchet.coe_restrict_toSublocale (n := regionNucleus) (Set.univ : EmergentRegion)

theorem fixed_map_inf (U V : EmergentFixed) :
    ((emergent_to_lof_fixed (emergent_fixed_inf U V) : LoFFixed) : EmergentRegion)
      = ((lof_fixed_inf (emergent_to_lof_fixed U) (emergent_to_lof_fixed V) : LoFFixed) :
          EmergentRegion) := by
  calc
    ((emergent_to_lof_fixed (emergent_fixed_inf U V) : LoFFixed) : EmergentRegion)
        = (U.1 ∩ V.1 : EmergentRegion) := rfl
    _ = regionNucleus (U.1 ∩ V.1) := (emergent_fixed_inf U V).2.symm
    _ = ((lof_fixed_inf (emergent_to_lof_fixed U) (emergent_to_lof_fixed V) : LoFFixed) :
          EmergentRegion) := by
        symm
        simp [lof_fixed_inf_val]

theorem fixed_map_top :
    ((emergent_to_lof_fixed emergent_fixed_top : LoFFixed) : EmergentRegion)
      = ((lof_fixed_top : LoFFixed) : EmergentRegion) := by
  calc
    ((emergent_to_lof_fixed emergent_fixed_top : LoFFixed) : EmergentRegion)
        = (Set.univ : EmergentRegion) := rfl
    _ = regionNucleus (Set.univ : EmergentRegion) := by simp [regionNucleus_apply]
    _ = ((lof_fixed_top : LoFFixed) : EmergentRegion) := by
        symm
        exact lof_fixed_top_val

/-- Phase-3 bridge equivalence (explicit fixed witnesses <-> nucleus range core). -/
def fixed_map_equiv_or_embedding : EmergentFixed ≃ LoFFixed where
  toFun := emergent_to_lof_fixed
  invFun := lof_to_emergent_fixed
  left_inv := by
    intro U
    apply Subtype.ext
    rfl
  right_inv := by
    intro V
    apply Subtype.ext
    rfl

/-- Meet-preservation in ambient carrier form. -/
theorem fixed_map_inf_val (U V : EmergentFixed) :
    ((emergent_to_lof_fixed (emergent_fixed_inf U V) : LoFFixed) : EmergentRegion)
      = U.1 ∩ V.1 := rfl

/-- Top-preservation in ambient carrier form. -/
theorem fixed_map_top_val :
    ((emergent_to_lof_fixed emergent_fixed_top : LoFFixed) : EmergentRegion)
      = (Set.univ : EmergentRegion) := rfl

/-! ## Tier-1 claim-surface theorems (LEP T1.2) -/

/-- Order relation on explicit fixed witnesses (inclusion on underlying regions). -/
def fixedLe (U V : EmergentFixed) : Prop := U.1 ⊆ V.1

/-- The fixed-point bridge packaged as the lattice/LoF isomorphism witness. -/
def lattice_lof_isomorphism : EmergentFixed ≃ LoFFixed :=
  fixed_map_equiv_or_embedding

/-- The bridge map is monotone w.r.t. inclusion on fixed regions. -/
theorem fixed_map_mono {U V : EmergentFixed} (hUV : fixedLe U V) :
    ((emergent_to_lof_fixed U : LoFFixed) : EmergentRegion) ⊆
      ((emergent_to_lof_fixed V : LoFFixed) : EmergentRegion) := by
  intro x hx
  exact hUV hx

/-- The bridge map reflects inclusion on fixed regions. -/
theorem fixed_map_reflects_le {U V : EmergentFixed}
    (h :
      ((emergent_to_lof_fixed U : LoFFixed) : EmergentRegion) ⊆
      ((emergent_to_lof_fixed V : LoFFixed) : EmergentRegion)) :
    fixedLe U V := by
  intro x hx
  exact h hx

/-- Underlying meet compatibility in explicit fixed-point form. -/
theorem fixed_map_inf_underlying (U V : EmergentFixed) :
    ((emergent_to_lof_fixed (emergent_fixed_inf U V) : LoFFixed) : EmergentRegion)
      =
      ((emergent_to_lof_fixed U : LoFFixed) : EmergentRegion)
        ∩
      ((emergent_to_lof_fixed V : LoFFixed) : EmergentRegion) := by
  rfl

end HeytingLean.Genesis
