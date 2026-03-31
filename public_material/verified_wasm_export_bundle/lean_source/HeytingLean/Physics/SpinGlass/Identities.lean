import HeytingLean.Physics.SpinGlass.Model

/-
# Spin-glass P₁/P₂ gauge identities (Chaos lens)

This module records, at the spec level, the key algebraic identities
between magnetisation and overlap distributions used in the
Nishimori–Ohzeki–Okuyama analysis of temperature chaos:

* Nishimori & Ohzeki & Okuyama, "Temperature chaos as a logical
  consequence of the reentrant transition in spin glasses",
  Phys. Rev. E 112, 044140 (2025), DOI: 10.1103/qp1w-qcbs.

These are **not** re-proved here. Instead, they are exposed as
named laws that the Chaos & Reentrance lens uses as rewrite rules
and consistency checks against empirical reports.

All assumptions in this file are intended to be local to the
spin-glass Chaos lens; they should not be imported into unrelated
modules without reflection.
-/

namespace HeytingLean
namespace Physics
namespace SpinGlass
namespace Identities

open SpinGlass

/-- Magnetisation distribution family `P₁`:
for each parameter triple `(β, βp, γ)` we have a 1D histogram
describing the distribution of magnetisation. -/
abbrev P1 := SGParams → Dist

/-- Overlap distribution family `P₂`:
for each triple `(β₁, β₂, γ)` we have a 1D histogram describing
the distribution of replica overlaps.  We reuse `SGParams` as
the parameter record, with the convention
`β := β₁`, `βp := β₂`, `γ := γ`. -/
abbrev P2 := SGParams → Dist

/--
Lens-local “gauge” identities used by the Chaos & Reentrance verifier.

These are packaged as an explicit assumption record (rather than global declarations)
so downstream developments remain parametric.
-/
structure Laws (P1 : P1) (P2 : P2) : Prop where
  /-- EA mapping identity: on the Edwards–Anderson plane (`EA_plane p`),
  the magnetisation distribution `P₁` at `(β, βp, γ)` coincides with the
  overlap distribution `P₂` at the same parameter triple. -/
  P1_eq_P2 : ∀ (p : SGParams), EA_plane p → P1 p = P2 { β := p.β, βp := p.βp, γ := p.γ }

  /-- Swap invariance of `P₁` in `(β, βp)` at fixed `γ`. -/
  P1_swap : ∀ (p : SGParams),
    P1 { β := p.β, βp := p.βp, γ := p.γ } =
      P1 { β := p.βp, βp := p.β, γ := p.γ }

  /-- Disorder-temperature independence for `P₂` (schematic, spec-level):
  varying `βp` while holding `(β, γ)` fixed does not change `P₂`. -/
  P2_indep_beta_p : ∀ (β γ βp1 βp2 : ℝ),
    P2 { β := β, βp := βp1, γ := γ } =
      P2 { β := β, βp := βp2, γ := γ }

namespace Toy

/-! A tiny non-physics “model” (constant distributions) that satisfies the laws by `rfl`.
This keeps the API exercised without introducing global axioms. -/

def trivialDist : Dist where
  bins := [0]
  mass := [1]
  mass_nonneg := by
    intro m hm
    simp at hm
    simp [hm]
  norm := by simp

def P1 : Identities.P1 := fun _ => trivialDist
def P2 : Identities.P2 := fun _ => trivialDist

def laws : Laws P1 P2 where
  P1_eq_P2 := by intro _ _; rfl
  P1_swap := by intro _; rfl
  P2_indep_beta_p := by intro _ _ _ _; rfl

end Toy

end Identities
end SpinGlass
end Physics
end HeytingLean
