import HeytingLean.LoF.Bauer.DomainTheory
import HeytingLean.LoF.Nucleus

/-!
# Eigenforms (Phase 3 bridge)

This module connects Kauffman-style eigenform equations `J = F J` to the ωCPPO fixed-point
construction from `HeytingLean.LoF.Bauer.DomainTheory`, and relates it to `Reentry` fixed
points `Ω_R` from `HeytingLean.LoF.Nucleus`.

The bridge is intentionally minimal and QA-friendly:

* for any complete lattice `D`, the ω-continuous endomap `x ↦ x ⊔ p` has least fixed point `p`;
* applying this inside `Ω_R` shows `Reentry.process` is a Bauer-style least fixed point in `Ω_R`.
-/

namespace HeytingLean
namespace LoF
namespace Bauer

namespace Eigenforms

open FixedPoint
open OmegaCPPO

universe u

section JoinConst

variable {D : Type u} [CompleteLattice D]

-- Make the ωCPPO structure explicit so `simp` can unfold `ωSup` to `iSup`.
local instance : OmegaCPPO D := instOmegaCPPO_ofCompleteLattice (D := D)

/-- The endomap `x ↦ x ⊔ p`. -/
def joinConst (p : D) : D → D := fun x => x ⊔ p

lemma joinConst_mono (p : D) : Monotone (joinConst (D := D) p) := by
  intro a b hab
  exact sup_le_sup_right hab p

lemma joinConst_ωcontinuous (p : D) :
    OmegaContinuous (D := D) (joinConst (D := D) p) where
  mono := joinConst_mono (D := D) p
  map_ωSup := by
    intro α _
    simpa [OmegaCPPO.ωSup, instOmegaCPPO_ofCompleteLattice, joinConst] using
      (iSup_sup (f := α) (a := p))

theorem lfp_joinConst_eq (p : D) :
    lfp (D := D) (joinConst (D := D) p) (joinConst_ωcontinuous (D := D) p) = p := by
  have hp : joinConst (D := D) p p = p := by simp [joinConst]
  apply le_antisymm
  · exact lfp_le_of_isFixed (D := D)
      (f := joinConst (D := D) p)
      (hf := joinConst_ωcontinuous (D := D) p)
      (q := p)
      hp
  · simpa [lfp, kleeneChain, joinConst] using
      (le_ωSup (D := D)
        (α := kleeneChain (D := D) (joinConst (D := D) p))
        (hα := monotone_kleeneChain (D := D) (joinConst_ωcontinuous (D := D) p).mono)
        1)

end JoinConst

section ReentryBridge

variable {α : Type u} [PrimaryAlgebra α]
variable (R : Reentry α)

theorem lfp_join_process_eq_process :
    FixedPoint.lfp (D := R.Omega)
      (joinConst (D := R.Omega) (p := R.process))
      (joinConst_ωcontinuous (D := R.Omega) (p := R.process))
      = R.process := by
  simpa using (lfp_joinConst_eq (D := R.Omega) (p := R.process))

end ReentryBridge

end Eigenforms

end Bauer
end LoF
end HeytingLean
