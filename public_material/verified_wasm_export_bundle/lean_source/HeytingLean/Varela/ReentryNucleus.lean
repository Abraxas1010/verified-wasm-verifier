import Mathlib.Data.Fintype.Order
import Mathlib.Order.Heyting.Hom
import Mathlib.Order.Sublocale
import HeytingLean.ClosingTheLoop.Semantics.NucleusFixedPoints
import HeytingLean.Varela.ECI

/-!
# Varela Re-Entry as an Honest Nucleus Bridge

`cross` itself is not a nucleus. Instead we place Varela's three-valued carrier
inside a slightly larger ambient stage lattice and put the nucleus there. The
fixed points of that ambient nucleus recover the ECI carrier exactly.
-/

namespace HeytingLean.Varela

open IndVal

/-- Ambient carrier: a latent precursor closes to the autonomous state. -/
inductive ReentryStage : Type
  | unmarked
  | latent
  | autonomous
  | marked
  deriving DecidableEq, Repr

instance : Fintype ReentryStage where
  elems := {.unmarked, .latent, .autonomous, .marked}
  complete x := by
    cases x <;> simp

namespace ReentryStage

def rank : ReentryStage → Nat
  | .unmarked => 0
  | .latent => 1
  | .autonomous => 2
  | .marked => 3

theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> simp [rank] at h
  · rfl
  · rfl
  · rfl
  · rfl

instance : LinearOrder ReentryStage :=
  LinearOrder.lift' rank rank_injective

instance : OrderBot ReentryStage where
  bot := .unmarked
  bot_le := by
    intro a
    cases a <;> decide

instance : OrderTop ReentryStage where
  top := .marked
  le_top := by
    intro a
    cases a <;> decide

instance : BoundedOrder ReentryStage := ⟨⟩

instance : DistribLattice ReentryStage := inferInstance

noncomputable instance : CompleteLinearOrder ReentryStage :=
  Fintype.toCompleteLinearOrder ReentryStage

/-- The genuine closure operator: only the latent stage closes upward. -/
def stageClosure : ReentryStage → ReentryStage
  | .latent => .autonomous
  | x => x

def stageNucleus : Nucleus ReentryStage where
  toFun := stageClosure
  map_inf' x y := by
    cases x <;> cases y <;> decide
  idempotent' x := by
    cases x <;> rfl
  le_apply' x := by
    cases x <;> decide

abbrev StageOmega : Type := stageNucleus.toSublocale

def eciToStage : IndVal → ReentryStage
  | .unmarked => .unmarked
  | .autonomous => .autonomous
  | .marked => .marked

@[simp] theorem stageClosure_eciToStage (x : IndVal) :
    stageClosure (eciToStage x) = eciToStage x := by
  cases x <;> rfl

theorem stageClosure_fixed_iff (s : ReentryStage) :
    stageClosure s = s ↔ ∃ x : IndVal, eciToStage x = s := by
  cases s
  · constructor
    · intro _
      exact ⟨.unmarked, rfl⟩
    · rintro ⟨x, hx⟩
      cases x
      · cases hx
        rfl
      · cases hx
      · cases hx
  · constructor
    · intro h
      simp [stageClosure] at h
    · rintro ⟨x, hx⟩
      cases x <;> simp [eciToStage] at hx
  · constructor
    · intro _
      exact ⟨.autonomous, rfl⟩
    · rintro ⟨x, hx⟩
      cases x
      · cases hx
      · cases hx
        rfl
      · cases hx
  · constructor
    · intro _
      exact ⟨.marked, rfl⟩
    · rintro ⟨x, hx⟩
      cases x
      · cases hx
      · cases hx
      · cases hx
        rfl

def eciToOmega (x : IndVal) : StageOmega :=
  ⟨eciToStage x, ⟨eciToStage x, stageClosure_eciToStage x⟩⟩

@[simp] theorem coe_eciToOmega (x : IndVal) :
    ((eciToOmega x : StageOmega) : ReentryStage) = eciToStage x := rfl

theorem mem_stageOmega_iff_stageClosure_fixed {s : ReentryStage} :
    s ∈ (stageNucleus.toSublocale : Set ReentryStage) ↔ stageClosure s = s := by
  exact ClosingTheLoop.Semantics.mem_Ω_iff_fixed (n := stageNucleus)

theorem mem_stageOmega_ne_latent {s : ReentryStage} (hs : s ∈ stageNucleus.toSublocale) :
    s ≠ .latent := by
  intro hsLat
  rcases hs with ⟨y, hy⟩
  subst hsLat
  change stageClosure y = .latent at hy
  cases y <;> simp [stageClosure] at hy

theorem omega_ne_latent (s : StageOmega) : (s : ReentryStage) ≠ .latent :=
  mem_stageOmega_ne_latent s.property

theorem mem_stageOmega_iff_eci_image {s : ReentryStage} :
    s ∈ (stageNucleus.toSublocale : Set ReentryStage) ↔ ∃ x : IndVal, eciToStage x = s := by
  rw [mem_stageOmega_iff_stageClosure_fixed]
  exact stageClosure_fixed_iff s

/-- Collapse the ambient stage carrier onto the three ECI values. -/
def collapseStage : ReentryStage → IndVal
  | .unmarked => .unmarked
  | .latent => .autonomous
  | .autonomous => .autonomous
  | .marked => .marked

def stageToECI (s : StageOmega) : IndVal :=
  collapseStage s

@[simp] theorem stageToECI_eciToOmega (x : IndVal) :
    stageToECI (eciToOmega x) = x := by
  cases x <;> rfl

@[simp] theorem eciToOmega_stageToECI (s : StageOmega) :
    eciToOmega (stageToECI s) = s := by
  rcases s with ⟨s, hs⟩
  cases s
  · rfl
  · exact False.elim (mem_stageOmega_ne_latent hs rfl)
  · rfl
  · rfl

def omegaEquivECI : StageOmega ≃ IndVal where
  toFun := stageToECI
  invFun := eciToOmega
  left_inv := eciToOmega_stageToECI
  right_inv := stageToECI_eciToOmega

@[simp] theorem omegaEquivECI_apply (s : StageOmega) :
    omegaEquivECI s = stageToECI s := rfl

@[simp] theorem omegaEquivECI_symm_apply (x : IndVal) :
    omegaEquivECI.symm x = eciToOmega x := rfl

/-- Order comparison on `StageOmega` transported to the concrete ECI carrier. -/
theorem stageToECI_le_iff {a b : StageOmega} :
    stageToECI a ≤ stageToECI b ↔ a ≤ b := by
  rcases a with ⟨s, hs⟩
  rcases b with ⟨t, ht⟩
  change collapseStage s ≤ collapseStage t ↔ s ≤ t
  cases s <;> cases t <;>
    first
    | exact False.elim (mem_stageOmega_ne_latent hs rfl)
    | exact False.elim (mem_stageOmega_ne_latent ht rfl)
    | decide

/-- The fixed-point carrier is not just equivalent to ECI; it is order-isomorphic. -/
def omegaOrderIsoECI : StageOmega ≃o IndVal where
  toEquiv := omegaEquivECI
  map_rel_iff' := stageToECI_le_iff

@[simp] theorem omegaOrderIsoECI_apply (s : StageOmega) :
    omegaOrderIsoECI s = stageToECI s := rfl

@[simp] theorem omegaOrderIsoECI_symm_apply (x : IndVal) :
    omegaOrderIsoECI.symm x = eciToOmega x := rfl

@[simp] theorem stageToECI_inf (a b : StageOmega) :
    stageToECI (a ⊓ b) = stageToECI a ⊓ stageToECI b := by
  rcases a with ⟨s, hs⟩
  rcases b with ⟨t, ht⟩
  change collapseStage (s ⊓ t) = collapseStage s ⊓ collapseStage t
  cases s <;> cases t <;>
    first
    | exact False.elim (mem_stageOmega_ne_latent hs rfl)
    | exact False.elim (mem_stageOmega_ne_latent ht rfl)
    | decide

@[simp] theorem stageToECI_sup (a b : StageOmega) :
    stageToECI (a ⊔ b) = stageToECI a ⊔ stageToECI b := by
  apply le_antisymm
  · have ha :
        a ≤ eciToOmega (stageToECI a ⊔ stageToECI b) := by
      rw [← stageToECI_le_iff]
      simp
    have hb :
        b ≤ eciToOmega (stageToECI a ⊔ stageToECI b) := by
      rw [← stageToECI_le_iff]
      simp
    have hab : a ⊔ b ≤ eciToOmega (stageToECI a ⊔ stageToECI b) :=
      sup_le ha hb
    rw [← stageToECI_le_iff] at hab
    simpa [stageToECI_eciToOmega] using hab
  · apply sup_le
    · rw [stageToECI_le_iff]
      exact le_sup_left
    · rw [stageToECI_le_iff]
      exact le_sup_right

@[simp] theorem stageToECI_bot :
    stageToECI (⊥ : StageOmega) = .unmarked := by
  have hbot :
      (⊥ : StageOmega) = stageNucleus.toSublocale.restrict (⊥ : ReentryStage) := by
    exact
      (stageNucleus.toSublocale.giRestrict.gc.l_bot :
        stageNucleus.toSublocale.restrict (⊥ : ReentryStage) = (⊥ : StageOmega)).symm
  rw [hbot, Nucleus.restrict_toSublocale]
  rfl

@[simp] theorem stageToECI_top :
    stageToECI (⊤ : StageOmega) = .marked := rfl

theorem omega_compl_autonomous :
    (eciToOmega .autonomous : StageOmega)ᶜ = eciToOmega .unmarked := by
  let a : StageOmega := eciToOmega .autonomous
  have hinf :
      .autonomous ⊓ stageToECI (aᶜ) = .unmarked := by
    calc
      .autonomous ⊓ stageToECI (aᶜ)
          = stageToECI a ⊓ stageToECI (aᶜ) := by simp [a, stageToECI_eciToOmega]
      _ = stageToECI (a ⊓ aᶜ) := by rw [stageToECI_inf]
      _ = stageToECI (⊥ : StageOmega) := by rw [inf_compl_self]
      _ = .unmarked := stageToECI_bot
  have hshape : stageToECI (aᶜ) = .unmarked := by
    cases h : stageToECI (aᶜ)
    · rfl
    · have hcontra : IndVal.autonomous = .unmarked := by
        simp [h] at hinf
      cases hcontra
    · have hmin : min IndVal.autonomous IndVal.marked = .unmarked := by
        simp [h] at hinf
        exact hinf
      have hnot : ¬ min IndVal.autonomous IndVal.marked = .unmarked := by
        decide
      exact False.elim (hnot hmin)
  simpa [a, hshape] using (eciToOmega_stageToECI (aᶜ)).symm

theorem omega_autonomous_not_classical :
    ¬ (eciToOmega .autonomous ⊔ (eciToOmega .autonomous)ᶜ = (⊤ : StageOmega)) := by
  let a : StageOmega := eciToOmega .autonomous
  have hsup : a ⊔ aᶜ = a := by
    rw [omega_compl_autonomous]
    exact sup_of_le_left (by
      rw [← stageToECI_le_iff]
      decide)
  intro h
  have htop : a = ⊤ := by
    calc
      a = a ⊔ aᶜ := hsup.symm
      _ = ⊤ := by simpa [a] using h
  have hcontra := congrArg stageToECI htop
  simp [a, stageToECI_top, stageToECI_eciToOmega] at hcontra

end ReentryStage

open ReentryStage

export ReentryStage (stageClosure stageNucleus StageOmega eciToStage eciToOmega
  stageToECI stageClosure_fixed_iff omegaEquivECI omegaOrderIsoECI
  omega_autonomous_not_classical)

end HeytingLean.Varela
