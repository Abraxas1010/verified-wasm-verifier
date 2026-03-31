import HeytingLean.Bridges.Nucleus.Conversions
import HeytingLean.Bridges.Nucleus.InteriorDuality
import HeytingLean.LoF.Nucleus
import HeytingLean.Constructor.CT.Nucleus
import HeytingLean.LoF.Bauer.SyntheticComputability

namespace HeytingLean
namespace Bridges
namespace Nucleus

open Set
open HeytingLean.LoF
open HeytingLean.Quantum
open HeytingLean.Constructor.CT
open HeytingLean.LoF.Bauer.SyntheticComputability

universe u

/-- Two nucleus definition types glue when conversions are mutually inverse. -/
def NucleusDefsGlue (α β : Type*) : Prop :=
  ∃ (f : α → β) (g : β → α),
    (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y)

/--
Any two nucleus definition types that both convert to/from a common hub type glue.
-/
theorem nucleusDefsGlue_via_hub {N₁ N₂ Hub : Type*}
    (f₁ : N₁ → Hub) (g₁ : Hub → N₁)
    (f₂ : N₂ → Hub) (g₂ : Hub → N₂)
    (h₁L : ∀ n, g₁ (f₁ n) = n)
    (h₁R : ∀ h, f₁ (g₁ h) = h)
    (h₂L : ∀ n, g₂ (f₂ n) = n)
    (h₂R : ∀ h, f₂ (g₂ h) = h) :
    NucleusDefsGlue N₁ N₂ := by
  refine ⟨fun n₁ => g₂ (f₁ n₁), fun n₂ => g₁ (f₂ n₂), ?_, ?_⟩
  · intro n₁
    simp [h₂R, h₁L]
  · intro n₂
    simp [h₁R, h₂L]

/-- One-directional bridge witness for forgetful projections. -/
def NucleusProjects (α β : Type*) : Prop :=
  ∃ (_f : α → β), True

/-- A nucleus variant embeds into another when a structure-preserving injection exists. -/
def NucleusEmbeds (α β : Type*) : Prop :=
  ∃ (f : α → β), Function.Injective f

/-- Core ↔ Mathlib. -/
theorem thm_sheaf_glue_nucleus_core_to_nucleus_mathlib
    {L : Type*} [SemilatticeInf L] [OrderBot L] :
    NucleusDefsGlue (HeytingLean.Core.Nucleus L) (_root_.Nucleus L) := by
  exact ⟨coreToMathlib, mathlibToCore,
    mathlibToCore_coreToMathlib, coreToMathlib_mathlibToCore⟩

theorem thm_sheaf_glue_nucleus_mathlib_to_nucleus_core
    {L : Type*} [SemilatticeInf L] [OrderBot L] :
    NucleusDefsGlue (_root_.Nucleus L) (HeytingLean.Core.Nucleus L) := by
  exact ⟨mathlibToCore, coreToMathlib,
    coreToMathlib_mathlibToCore, mathlibToCore_coreToMathlib⟩

/-- Core ↔ Heyting via Mathlib hub. -/
theorem thm_sheaf_glue_nucleus_core_to_nucleus_heyting
    {α : Type*} [HeytingAlgebra α] :
    NucleusDefsGlue (HeytingLean.Core.Nucleus α) (HeytingLean.Core.Heyting.Nucleus α) := by
  exact nucleusDefsGlue_via_hub coreToMathlib mathlibToCore
    heytingToMathlib mathlibToHeyting
    mathlibToCore_coreToMathlib coreToMathlib_mathlibToCore
    mathlibToHeyting_heytingToMathlib heytingToMathlib_mathlibToHeyting

theorem thm_sheaf_glue_nucleus_heyting_to_nucleus_core
    {α : Type*} [HeytingAlgebra α] :
    NucleusDefsGlue (HeytingLean.Core.Heyting.Nucleus α) (HeytingLean.Core.Nucleus α) := by
  exact nucleusDefsGlue_via_hub heytingToMathlib mathlibToHeyting
    coreToMathlib mathlibToCore
    mathlibToHeyting_heytingToMathlib heytingToMathlib_mathlibToHeyting
    mathlibToCore_coreToMathlib coreToMathlib_mathlibToCore

/-- Core ↔ Rule via Mathlib hub. -/
theorem thm_sheaf_glue_nucleus_core_to_nucleus_rule :
    NucleusDefsGlue
      (HeytingLean.Core.Nucleus (Set (ℝ → ℝ)))
      HeytingLean.Calculus.RuleNucleus := by
  exact nucleusDefsGlue_via_hub
    (coreToMathlib (L := Set (ℝ → ℝ))) (mathlibToCore (L := Set (ℝ → ℝ)))
    ruleToMathlib mathlibToRule
    (mathlibToCore_coreToMathlib (L := Set (ℝ → ℝ)))
    (coreToMathlib_mathlibToCore (L := Set (ℝ → ℝ)))
    mathlibToRule_ruleToMathlib
    ruleToMathlib_mathlibToRule

theorem thm_sheaf_glue_nucleus_rule_to_nucleus_core :
    NucleusDefsGlue
      HeytingLean.Calculus.RuleNucleus
      (HeytingLean.Core.Nucleus (Set (ℝ → ℝ))) := by
  exact nucleusDefsGlue_via_hub
    ruleToMathlib mathlibToRule
    (coreToMathlib (L := Set (ℝ → ℝ))) (mathlibToCore (L := Set (ℝ → ℝ)))
    mathlibToRule_ruleToMathlib
    ruleToMathlib_mathlibToRule
    (mathlibToCore_coreToMathlib (L := Set (ℝ → ℝ)))
    (coreToMathlib_mathlibToCore (L := Set (ℝ → ℝ)))

/-- Core ↔ Calculus via Mathlib hub. -/
theorem thm_sheaf_glue_nucleus_core_to_nucleus_calculus
    {α : Type*} [CompleteLattice α] :
    NucleusDefsGlue (HeytingLean.Core.Nucleus α) (HeytingLean.Calculus.CalculusNucleus α) := by
  exact nucleusDefsGlue_via_hub coreToMathlib mathlibToCore
    calculusToMathlib mathlibToCalculus
    mathlibToCore_coreToMathlib coreToMathlib_mathlibToCore
    mathlibToCalculus_calculusToMathlib calculusToMathlib_mathlibToCalculus

theorem thm_sheaf_glue_nucleus_calculus_to_nucleus_core
    {α : Type*} [CompleteLattice α] :
    NucleusDefsGlue (HeytingLean.Calculus.CalculusNucleus α) (HeytingLean.Core.Nucleus α) := by
  exact nucleusDefsGlue_via_hub calculusToMathlib mathlibToCalculus
    coreToMathlib mathlibToCore
    mathlibToCalculus_calculusToMathlib calculusToMathlib_mathlibToCalculus
    mathlibToCore_coreToMathlib coreToMathlib_mathlibToCore

/-- Mathlib ↔ Heyting. -/
theorem thm_sheaf_glue_nucleus_mathlib_to_nucleus_heyting
    {α : Type*} [HeytingAlgebra α] :
    NucleusDefsGlue (_root_.Nucleus α) (HeytingLean.Core.Heyting.Nucleus α) := by
  exact ⟨mathlibToHeyting, heytingToMathlib,
    heytingToMathlib_mathlibToHeyting, mathlibToHeyting_heytingToMathlib⟩

theorem thm_sheaf_glue_nucleus_heyting_to_nucleus_mathlib
    {α : Type*} [HeytingAlgebra α] :
    NucleusDefsGlue (HeytingLean.Core.Heyting.Nucleus α) (_root_.Nucleus α) := by
  exact ⟨heytingToMathlib, mathlibToHeyting,
    mathlibToHeyting_heytingToMathlib, heytingToMathlib_mathlibToHeyting⟩

/-- Mathlib ↔ Rule. -/
theorem thm_sheaf_glue_nucleus_mathlib_to_nucleus_rule :
    NucleusDefsGlue (_root_.Nucleus (Set (ℝ → ℝ))) HeytingLean.Calculus.RuleNucleus := by
  exact ⟨mathlibToRule, ruleToMathlib,
    ruleToMathlib_mathlibToRule, mathlibToRule_ruleToMathlib⟩

theorem thm_sheaf_glue_nucleus_rule_to_nucleus_mathlib :
    NucleusDefsGlue HeytingLean.Calculus.RuleNucleus (_root_.Nucleus (Set (ℝ → ℝ))) := by
  exact ⟨ruleToMathlib, mathlibToRule,
    mathlibToRule_ruleToMathlib, ruleToMathlib_mathlibToRule⟩

/-- Mathlib ↔ Calculus. -/
theorem thm_sheaf_glue_nucleus_mathlib_to_nucleus_calculus
    {α : Type*} [CompleteLattice α] :
    NucleusDefsGlue (_root_.Nucleus α) (HeytingLean.Calculus.CalculusNucleus α) := by
  exact ⟨mathlibToCalculus, calculusToMathlib,
    calculusToMathlib_mathlibToCalculus, mathlibToCalculus_calculusToMathlib⟩

theorem thm_sheaf_glue_nucleus_calculus_to_nucleus_mathlib
    {α : Type*} [CompleteLattice α] :
    NucleusDefsGlue (HeytingLean.Calculus.CalculusNucleus α) (_root_.Nucleus α) := by
  exact ⟨calculusToMathlib, mathlibToCalculus,
    mathlibToCalculus_calculusToMathlib, calculusToMathlib_mathlibToCalculus⟩

/-- Heyting ↔ Rule via Mathlib hub. -/
theorem thm_sheaf_glue_nucleus_heyting_to_nucleus_rule :
    NucleusDefsGlue
      (HeytingLean.Core.Heyting.Nucleus (Set (ℝ → ℝ)))
      HeytingLean.Calculus.RuleNucleus := by
  exact nucleusDefsGlue_via_hub
    (heytingToMathlib (α := Set (ℝ → ℝ))) (mathlibToHeyting (α := Set (ℝ → ℝ)))
    ruleToMathlib mathlibToRule
    (mathlibToHeyting_heytingToMathlib (α := Set (ℝ → ℝ)))
    (heytingToMathlib_mathlibToHeyting (α := Set (ℝ → ℝ)))
    mathlibToRule_ruleToMathlib
    ruleToMathlib_mathlibToRule

theorem thm_sheaf_glue_nucleus_rule_to_nucleus_heyting :
    NucleusDefsGlue
      HeytingLean.Calculus.RuleNucleus
      (HeytingLean.Core.Heyting.Nucleus (Set (ℝ → ℝ))) := by
  exact nucleusDefsGlue_via_hub
    ruleToMathlib mathlibToRule
    (heytingToMathlib (α := Set (ℝ → ℝ))) (mathlibToHeyting (α := Set (ℝ → ℝ)))
    mathlibToRule_ruleToMathlib
    ruleToMathlib_mathlibToRule
    (mathlibToHeyting_heytingToMathlib (α := Set (ℝ → ℝ)))
    (heytingToMathlib_mathlibToHeyting (α := Set (ℝ → ℝ)))

/-- Heyting ↔ Calculus via Mathlib hub. -/
theorem thm_sheaf_glue_nucleus_heyting_to_nucleus_calculus
    {α : Type*} [Order.Frame α] :
    NucleusDefsGlue
      (HeytingLean.Core.Heyting.Nucleus α)
      (HeytingLean.Calculus.CalculusNucleus α) := by
  exact nucleusDefsGlue_via_hub
    (heytingToMathlib (α := α)) (mathlibToHeyting (α := α))
    (calculusToMathlib (α := α)) (mathlibToCalculus (α := α))
    (mathlibToHeyting_heytingToMathlib (α := α))
    (heytingToMathlib_mathlibToHeyting (α := α))
    (mathlibToCalculus_calculusToMathlib (α := α))
    (calculusToMathlib_mathlibToCalculus (α := α))

theorem thm_sheaf_glue_nucleus_calculus_to_nucleus_heyting
    {α : Type*} [Order.Frame α] :
    NucleusDefsGlue
      (HeytingLean.Calculus.CalculusNucleus α)
      (HeytingLean.Core.Heyting.Nucleus α) := by
  exact nucleusDefsGlue_via_hub
    (calculusToMathlib (α := α)) (mathlibToCalculus (α := α))
    (heytingToMathlib (α := α)) (mathlibToHeyting (α := α))
    (mathlibToCalculus_calculusToMathlib (α := α))
    (calculusToMathlib_mathlibToCalculus (α := α))
    (mathlibToHeyting_heytingToMathlib (α := α))
    (heytingToMathlib_mathlibToHeyting (α := α))

/-- Rule ↔ Calculus via Mathlib hub. -/
theorem thm_sheaf_glue_nucleus_rule_to_nucleus_calculus :
    NucleusDefsGlue
      HeytingLean.Calculus.RuleNucleus
      (HeytingLean.Calculus.CalculusNucleus (Set (ℝ → ℝ))) := by
  exact nucleusDefsGlue_via_hub
    ruleToMathlib mathlibToRule
    (calculusToMathlib (α := Set (ℝ → ℝ))) (mathlibToCalculus (α := Set (ℝ → ℝ)))
    mathlibToRule_ruleToMathlib
    ruleToMathlib_mathlibToRule
    (mathlibToCalculus_calculusToMathlib (α := Set (ℝ → ℝ)))
    (calculusToMathlib_mathlibToCalculus (α := Set (ℝ → ℝ)))

theorem thm_sheaf_glue_nucleus_calculus_to_nucleus_rule :
    NucleusDefsGlue
      (HeytingLean.Calculus.CalculusNucleus (Set (ℝ → ℝ)))
      HeytingLean.Calculus.RuleNucleus := by
  exact nucleusDefsGlue_via_hub
    (calculusToMathlib (α := Set (ℝ → ℝ))) (mathlibToCalculus (α := Set (ℝ → ℝ)))
    ruleToMathlib mathlibToRule
    (mathlibToCalculus_calculusToMathlib (α := Set (ℝ → ℝ)))
    (calculusToMathlib_mathlibToCalculus (α := Set (ℝ → ℝ)))
    mathlibToRule_ruleToMathlib
    ruleToMathlib_mathlibToRule

/-- Interior bridge: every QGI nucleus projects to Int nucleus. -/
theorem thm_sheaf_glue_nucleus_qgi_to_nucleus_int
    {α : Type u} [PrimaryAlgebra α] :
    NucleusProjects (QGINucleus α) (IntNucleus α) :=
  ⟨qgiToInt, trivial⟩

/-- Interior bridge: an Int nucleus lifts to QGI once support witness is supplied. -/
theorem thm_sheaf_glue_nucleus_int_to_nucleus_qgi_with_support
    {α : Type u} [PrimaryAlgebra α]
    (N : IntNucleus α)
    (support : α)
    (support_mem : N.act support = support)
    (support_nonbot : ⊥ < support) :
    ∃ Q : QGINucleus α, qgiToInt Q = N := by
  refine ⟨intToQgiWithSupport N support support_mem support_nonbot, ?_⟩
  exact qgiToInt_intToQgiWithSupport N support support_mem support_nonbot

/-- Interior bridge: QGI roundtrips through Int when keeping original support witness. -/
theorem thm_sheaf_glue_nucleus_qgi_roundtrip
    {α : Type u} [PrimaryAlgebra α]
    (N : QGINucleus α) :
    intToQgiWithSupport (qgiToInt N) N.support N.support_mem N.support_nonbot = N :=
  intToQgiWithSupport_qgiToInt N

/-- Conditional closure/interior duality witness on Boolean carriers. -/
theorem thm_sheaf_glue_nucleus_closure_dual_map_inf
    {α : Type u} [BooleanAlgebra α]
    (N : _root_.Nucleus α)
    (hmap_sup : ∀ a b, N (a ⊔ b) = N a ⊔ N b) :
    ∀ a b,
      closureDualAct N (a ⊓ b) = closureDualAct N a ⊓ closureDualAct N b :=
  closureDualAct_map_inf_of_map_sup N hmap_sup

/-- Reentry projects to the underlying Mathlib nucleus. -/
def reentryToMathlib {α : Type u} [PrimaryAlgebra α]
    (R : Reentry α) : _root_.Nucleus α :=
  R.nucleus

/-- Reentry projects to the core nucleus interface. -/
def reentryToCore {α : Type u} [PrimaryAlgebra α]
    (R : Reentry α) : HeytingLean.Core.Nucleus α :=
  mathlibToCore R.nucleus

/-- Constructor-theory nucleus projects to Mathlib nucleus. -/
def ctToMathlib {σ : Type u}
    (N : CTNucleus σ) : _root_.Nucleus (Set (HeytingLean.Constructor.CT.Task σ)) :=
  N.toNucleus

/-- Constructor-theory nucleus projects to core nucleus interface. -/
def ctToCore {σ : Type u}
    (N : CTNucleus σ) : HeytingLean.Core.Nucleus (Set (HeytingLean.Constructor.CT.Task σ)) :=
  mathlibToCore N.toNucleus

/-- Synthetic-computability world projects to Mathlib nucleus. -/
def worldToMathlib {Ω : Type u} [Order.Frame Ω]
    (W : World (Ω := Ω)) : _root_.Nucleus Ω :=
  W.J

/-- Synthetic-computability world projects to core nucleus interface. -/
def worldToCore {Ω : Type u} [Order.Frame Ω]
    (W : World (Ω := Ω)) : HeytingLean.Core.Nucleus Ω :=
  mathlibToCore W.J

private theorem ctNucleus_ext_by_J {σ : Type u}
    {N₁ N₂ : CTNucleus σ} (hJ : N₁.J = N₂.J) : N₁ = N₂ := by
  cases N₁
  cases N₂
  cases hJ
  simp

theorem ctToMathlib_injective {σ : Type u} :
    Function.Injective (ctToMathlib (σ := σ)) := by
  intro N₁ N₂ h
  apply ctNucleus_ext_by_J
  funext X
  exact congrArg (fun n : _root_.Nucleus (Set (HeytingLean.Constructor.CT.Task σ)) => n X) h

theorem ctToCore_injective {σ : Type u} :
    Function.Injective (ctToCore (σ := σ)) := by
  intro N₁ N₂ h
  apply ctToMathlib_injective (σ := σ)
  have h' := congrArg
    (fun n : HeytingLean.Core.Nucleus (Set (HeytingLean.Constructor.CT.Task σ)) => coreToMathlib n) h
  simpa [ctToCore, ctToMathlib] using h'

/-- Bundle projection glue witnesses. -/
theorem thm_sheaf_glue_nucleus_reentry_to_nucleus_mathlib
    {α : Type u} [PrimaryAlgebra α] :
    NucleusProjects (Reentry α) (_root_.Nucleus α) :=
  ⟨reentryToMathlib, trivial⟩

theorem thm_sheaf_glue_nucleus_reentry_to_nucleus_core
    {α : Type u} [PrimaryAlgebra α] :
    NucleusProjects (Reentry α) (HeytingLean.Core.Nucleus α) :=
  ⟨reentryToCore, trivial⟩

theorem thm_sheaf_glue_nucleus_ct_to_nucleus_mathlib
    {σ : Type u} :
    NucleusEmbeds (CTNucleus σ) (_root_.Nucleus (Set (HeytingLean.Constructor.CT.Task σ))) :=
  ⟨ctToMathlib, ctToMathlib_injective⟩

theorem thm_sheaf_glue_nucleus_ct_to_nucleus_core
    {σ : Type u} :
    NucleusEmbeds (CTNucleus σ) (HeytingLean.Core.Nucleus (Set (HeytingLean.Constructor.CT.Task σ))) :=
  ⟨ctToCore, ctToCore_injective⟩

theorem thm_sheaf_glue_nucleus_world_to_nucleus_mathlib
    {Ω : Type u} [Order.Frame Ω] :
    NucleusProjects (World (Ω := Ω)) (_root_.Nucleus Ω) :=
  ⟨worldToMathlib, trivial⟩

theorem thm_sheaf_glue_nucleus_world_to_nucleus_core
    {Ω : Type u} [Order.Frame Ω] :
    NucleusProjects (World (Ω := Ω)) (HeytingLean.Core.Nucleus Ω) :=
  ⟨worldToCore, trivial⟩

end Nucleus
end Bridges
end HeytingLean
