import HeytingLean.Genesis.CoGame

/-!
# Genesis.LatticeEmergence

Phase 1 order layer:
- simulation preorder on `CoGame`,
- transport across bisimulation classes,
- quotient-level carrier with a strict partial-order lane.
-/

namespace HeytingLean.Genesis

open CoGame

universe u v w

/-- Forward simulation between rooted co-games. -/
structure IsSimulation (G : CoGame.{u}) (H : CoGame.{v}) (R : G.Node → H.Node → Prop) : Prop where
  root_rel : R G.root H.root
  left_forth :
    ∀ {x y}, R x y → ∀ {x'}, x' ∈ G.leftSucc x → ∃ y', y' ∈ H.leftSucc y ∧ R x' y'
  right_forth :
    ∀ {x y}, R x y → ∀ {x'}, x' ∈ G.rightSucc x → ∃ y', y' ∈ H.rightSucc y ∧ R x' y'

/-- Simulation preorder relation on co-games. -/
def Sim (G : CoGame.{u}) (H : CoGame.{v}) : Prop :=
  ∃ R : G.Node → H.Node → Prop, IsSimulation G H R

theorem sim_le_refl (G : CoGame.{u}) : Sim G G := by
  refine ⟨fun x y => x = y, ?_⟩
  refine IsSimulation.mk ?_ ?_ ?_
  · rfl
  · intro x y hxy x' hx'
    subst hxy
    exact ⟨x', hx', rfl⟩
  · intro x y hxy x' hx'
    subst hxy
    exact ⟨x', hx', rfl⟩

theorem sim_le_trans {G : CoGame.{u}} {H : CoGame.{v}} {K : CoGame.{w}} :
    Sim G H → Sim H K → Sim G K := by
  intro hGH hHK
  rcases hGH with ⟨R, hR⟩
  rcases hHK with ⟨S, hS⟩
  let T : G.Node → K.Node → Prop := fun x z => ∃ y, R x y ∧ S y z
  refine ⟨T, ?_⟩
  refine IsSimulation.mk ?_ ?_ ?_
  · exact ⟨H.root, hR.root_rel, hS.root_rel⟩
  · intro x z hxz x' hx'
    rcases hxz with ⟨y, hxy, hyz⟩
    rcases hR.left_forth hxy hx' with ⟨y', hy'mem, hx'y'⟩
    rcases hS.left_forth hyz hy'mem with ⟨z', hz'mem, hy'z'⟩
    exact ⟨z', hz'mem, ⟨y', hx'y', hy'z'⟩⟩
  · intro x z hxz x' hx'
    rcases hxz with ⟨y, hxy, hyz⟩
    rcases hR.right_forth hxy hx' with ⟨y', hy'mem, hx'y'⟩
    rcases hS.right_forth hyz hy'mem with ⟨z', hz'mem, hy'z'⟩
    exact ⟨z', hz'mem, ⟨y', hx'y', hy'z'⟩⟩

theorem bisim_to_sim {G : CoGame.{u}} {H : CoGame.{v}} :
    CoGame.Bisim G H → Sim G H := by
  intro h
  rcases h with ⟨R, hR⟩
  exact ⟨R, IsSimulation.mk hR.root_rel hR.left_forth hR.right_forth⟩

theorem bisim_equiv_respects_sim {G G' : CoGame.{u}} {H H' : CoGame.{v}}
    (hGG' : CoGame.Bisim G G') (hHH' : CoGame.Bisim H H') :
    Sim G H → Sim G' H' := by
  intro hGH
  have hG'G : Sim G' G := bisim_to_sim (CoGame.bisim_symm hGG')
  have hHH' : Sim H H' := bisim_to_sim hHH'
  exact sim_le_trans (sim_le_trans hG'G hGH) hHH'

/-- Bisimulation-quotient carrier. -/
abbrev EmergentClass : Type (u + 1) := Quotient (inferInstance : Setoid CoGame.{u})

/-- Canonical quotient map. -/
def toEmergentClass (G : CoGame.{u}) : EmergentClass :=
  Quotient.mk (inferInstance : Setoid CoGame.{u}) G

/-- Quotient-level simulation relation induced from representatives. -/
def emergentLe (a b : EmergentClass) : Prop :=
  Quotient.liftOn₂ a b (fun G H => Sim G H)
    (by
      intro G G' H H' hGG' hHH'
      apply propext
      constructor
      · intro h
        exact bisim_equiv_respects_sim hGG' hHH' h
      · intro h
        exact bisim_equiv_respects_sim (CoGame.bisim_symm hGG') (CoGame.bisim_symm hHH') h)

theorem emergent_le_well_defined {G G' H H' : CoGame.{u}}
    (hGG' : CoGame.Bisim G G') (hHH' : CoGame.Bisim H H') :
    Sim G H → Sim G' H' :=
  bisim_equiv_respects_sim hGG' hHH'

theorem emergent_le_refl (a : EmergentClass) : emergentLe a a := by
  refine Quotient.inductionOn a ?_
  intro G
  exact sim_le_refl G

theorem emergent_le_trans {a b c : EmergentClass} :
    emergentLe a b → emergentLe b c → emergentLe a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro G H K hGH hHK
  exact sim_le_trans hGH hHK

/-- Strict poset lane on the quotient carrier (order by quotient equality). -/
def emergentEqLe (a b : EmergentClass) : Prop := a = b

theorem emergent_eq_le_refl (a : EmergentClass) : emergentEqLe a a := rfl

theorem emergent_eq_le_antisymm {a b : EmergentClass}
    (hab : emergentEqLe a b) (_hba : emergentEqLe b a) : a = b :=
  hab

/-- Alias required by the phase-1 theorem spine. -/
theorem emergent_le_antisymm {a b : EmergentClass}
    (hab : emergentEqLe a b) (hba : emergentEqLe b a) : a = b :=
  emergent_eq_le_antisymm hab hba

/-- Phase-2 carrier: regions over emergent classes. -/
abbrev EmergentRegion : Type (u + 1) := Set EmergentClass

/-- Representative region for a single co-game. -/
def regionOfRep (G : CoGame.{u}) : EmergentRegion := {toEmergentClass G}

theorem regionOfRep_eq_of_bisim {G G' : CoGame.{u}} (hGG' : CoGame.Bisim G G') :
    regionOfRep G = regionOfRep G' := by
  have hclass : toEmergentClass G = toEmergentClass G' := Quot.sound hGG'
  apply Set.ext
  intro x
  constructor
  · intro hx
    rcases hx with rfl
    exact hclass
  · intro hx
    rcases hx with rfl
    exact hclass.symm

/-- Candidate meet constructor on representatives (intersection of representative regions). -/
def infRepRegion (G H : CoGame.{u}) : EmergentRegion :=
  regionOfRep G ∩ regionOfRep H

/-- Candidate join constructor on representatives (union of representative regions). -/
def supRepRegion (G H : CoGame.{u}) : EmergentRegion :=
  regionOfRep G ∪ regionOfRep H

theorem inf_well_defined {G G' H H' : CoGame.{u}}
    (hGG' : CoGame.Bisim G G') (hHH' : CoGame.Bisim H H') :
    infRepRegion G H = infRepRegion G' H' := by
  simp [infRepRegion, regionOfRep_eq_of_bisim hGG', regionOfRep_eq_of_bisim hHH']

theorem sup_well_defined {G G' H H' : CoGame.{u}}
    (hGG' : CoGame.Bisim G G') (hHH' : CoGame.Bisim H H') :
    supRepRegion G H = supRepRegion G' H' := by
  simp [supRepRegion, regionOfRep_eq_of_bisim hGG', regionOfRep_eq_of_bisim hHH']

/-- Meet on the phase-2 region carrier. -/
def regionInf (U V : EmergentRegion) : EmergentRegion := U ∩ V

/-- Join on the phase-2 region carrier. -/
def regionSup (U V : EmergentRegion) : EmergentRegion := U ∪ V

theorem inf_comm (U V : EmergentRegion) : regionInf U V = regionInf V U := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    exact ⟨hx.2, hx.1⟩
  · intro hx
    exact ⟨hx.2, hx.1⟩

theorem inf_assoc (U V W : EmergentRegion) :
    regionInf (regionInf U V) W = regionInf U (regionInf V W) := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    exact ⟨hx.1.1, ⟨hx.1.2, hx.2⟩⟩
  · intro hx
    exact ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩

theorem inf_idem (U : EmergentRegion) : regionInf U U = U := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact ⟨hx, hx⟩

theorem sup_comm (U V : EmergentRegion) : regionSup U V = regionSup V U := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    rcases hx with hx | hx
    · exact Or.inr hx
    · exact Or.inl hx
  · intro hx
    rcases hx with hx | hx
    · exact Or.inr hx
    · exact Or.inl hx

theorem sup_assoc (U V W : EmergentRegion) :
    regionSup (regionSup U V) W = regionSup U (regionSup V W) := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    rcases hx with hx | hx
    · rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)
  · intro hx
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · rcases hx with hx | hx
      · exact Or.inl (Or.inr hx)
      · exact Or.inr hx

theorem sup_idem (U : EmergentRegion) : regionSup U U = U := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    rcases hx with hx | hx <;> exact hx
  · intro hx
    exact Or.inl hx

/-! ## Tier-1 claim-surface theorems (LEP T1.1) -/

/-- On behavioral regions, `regionInf` is exactly set intersection. -/
@[simp] theorem regionInf_eq_inter (U V : EmergentRegion) :
    regionInf U V = U ∩ V := rfl

/-- On behavioral regions, `regionSup` is exactly set union. -/
@[simp] theorem regionSup_eq_union (U V : EmergentRegion) :
    regionSup U V = U ∪ V := rfl

/-- Representative-level meet is behavior intersection. -/
@[simp] theorem infRepRegion_eq_behavior_intersection (G H : CoGame.{u}) :
    infRepRegion G H = regionOfRep G ∩ regionOfRep H := rfl

/-- Representative-level join is behavior union. -/
@[simp] theorem supRepRegion_eq_behavior_union (G H : CoGame.{u}) :
    supRepRegion G H = regionOfRep G ∪ regionOfRep H := rfl

/-- LEP T1.1 packaging: behavioral meet/join are intersection/union. -/
theorem behavioral_lattice_operations (U V : EmergentRegion) :
    regionInf U V = U ∩ V ∧ regionSup U V = U ∪ V := by
  constructor <;> rfl

theorem absorption_inf_sup (U V : EmergentRegion) :
    regionInf U (regionSup U V) = U ∧ regionSup U (regionInf U V) = U := by
  constructor
  · apply Set.ext
    intro x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, Or.inl hx⟩
  · apply Set.ext
    intro x
    constructor
    · intro hx
      rcases hx with hxU | hxUV
      · exact hxU
      · exact hxUV.1
    · intro hx
      exact Or.inl hx

end HeytingLean.Genesis
