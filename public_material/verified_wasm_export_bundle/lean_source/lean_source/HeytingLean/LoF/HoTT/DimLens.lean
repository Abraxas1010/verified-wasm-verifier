import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Lattice
import HeytingLean.LoF.ComparisonNucleus.Spec
import HeytingLean.LoF.ComparisonNucleus.Examples
import HeytingLean.LoF.HoTT.Confluence
import HeytingLean.LoF.Combinators.SKY
import HeytingLean.LoF.HoTT.SKYBridge

/-
Dimensional lenses: finite comparison nuclei equipped with SKY
encodings and a joinability property mirroring RT-1.

Each `DimLens` packages:
- a comparison nucleus `S : CompSpec L Ω`,
- a SKY encoding `code : ΩR S → Comb` for its fixed-point core, and
- a proof that the two RT-1 branches at any `a : ΩR S` have a
  combinatorial join for their encoded SKY terms.

The small examples `boolDimLens` and `fin2DimLens` provide concrete
1-bit and 2-bit ΩR windows (Bool and Set(Fin 2)) for the dimensional
correspondence story.
-/

namespace HeytingLean
namespace LoF
namespace HoTT

open Comparison Comb

universe u v

/-- SKY regime tags, following the Dimensional Correspondence
intuition:
- `K1D`  : K-only regime (1D),
- `S2D`  : S-only regime (2D),
- `SK3D` : SK regime (3D),
- `SKY4D`: SK+Y regime (4D).

These tags are metadata; the mathematical content lives in the
`DimLens.join` field. -/
inductive SkyRegime
  | K1D
  | S2D
  | SK3D
  | SKY4D
deriving Repr, DecidableEq

/-- A dimensional lens over a comparison nucleus: a (typically finite)
ΩR core equipped with a SKY encoding and a joinability lemma
reflecting RT-1 at the combinatorial level. -/
structure DimLens (L : Type u) (Ω : Type v)
    [CompleteLattice L] [CompleteLattice Ω] where
  /-- Informal regime tag (K-only, S-only, SK, or SKY). -/
  regime : SkyRegime
  /-- Underlying comparison nucleus. -/
  S : CompSpec L Ω
  /-- SKY encoding of the fixed-point core. -/
  code : ΩR S → Comb
  /-- RT-1 ⇒ combinatorial joinability: for any peak of the two-branch
  system at `a`, the encoded targets have a common reduct in the SKY
  reduction system. -/
  join :
    ∀ {a b₁ b₂ : ΩR S},
      stepComparison (S := S) a b₁ →
      stepComparison (S := S) a b₂ →
      ∃ c, Comb.Steps (code b₁) c ∧ Comb.Steps (code b₂) c

/-- A 1-bit dimensional lens based on the Boolean comparison nucleus.

The underlying ΩR core is `Bool`, and the encoding sends `false` to
`K` and `true` to `S`.  The `join` field is provided by the generic
`comparison_peak_join_code` lemma instantiated with this encoding. -/
noncomputable def boolDimLens : DimLens Bool Bool :=
by
  classical
  refine
    { regime := SkyRegime.SK3D
      S := Comparison.boolCompSpec
      code := fun a =>
        codeBool (Comparison.boolΩREquiv a)
      join := ?_ }
  · intro a b₁ b₂ h₁ h₂
    -- Use the abstract comparison/SKY join lemma with this concrete code.
    have h :=
      comparison_peak_join_code
        (S := Comparison.boolCompSpec)
        (code :=
          fun x => codeBool (Comparison.boolΩREquiv x))
        h₁ h₂
    simpa using h

/-- A 2-bit dimensional lens based on the four-element Boolean lattice
`Set (Fin 2)`.  The encoding `codeFin2` distinguishes the four
subsets by membership of `0` and `1`. -/
noncomputable def fin2DimLens :
    DimLens (Set (Fin 2)) (Set (Fin 2)) :=
by
  classical
  refine
    { regime := SkyRegime.SKY4D
      S := Comparison.fin2CompSpec
      code := fun a =>
        codeFin2 (Comparison.fin2ΩREquiv a)
      join := ?_ }
  · intro a b₁ b₂ h₁ h₂
    have h :=
      comparison_peak_join_code
        (S := Comparison.fin2CompSpec)
        (code :=
          fun x => codeFin2 (Comparison.fin2ΩREquiv x))
        h₁ h₂
    simpa using h

end HoTT
end LoF
end HeytingLean
