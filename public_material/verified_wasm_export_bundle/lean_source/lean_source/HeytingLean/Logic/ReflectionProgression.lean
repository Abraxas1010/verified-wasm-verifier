import Mathlib.Order.Nucleus
import Mathlib.Order.TransfiniteIteration
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.SuccPred.Basic
import Mathlib.Order.Heyting.Basic
import Mathlib.Data.Finset.Lattice.Fold



namespace HeytingLean
namespace Logic

open scoped Classical
open Ordinal
open Order

variable {α : Type*}

section ReflectionLaws

variable [Order.Frame α]

/-- `dominating f` collects the nuclei that sit above a given operator `f`. -/
def dominating (f : α → α) : Set (Nucleus α) :=
  {n | ∀ x, f x ≤ n x}

/-- The top nucleus always dominates any operator. -/
lemma top_mem_dominating (f : α → α) :
    (⊤ : Nucleus α) ∈ dominating (α := α) f := by
  intro x; simp

/-- `nucleusClosure f` is the least nucleus dominating a monotone operator `f`. -/
noncomputable def nucleusClosure (f : α → α) : Nucleus α :=
  sInf (dominating (α := α) f)

lemma nucleusClosure_le_of_mem {f : α → α} {n : Nucleus α}
    (hn : n ∈ dominating (α := α) f) :
    nucleusClosure (α := α) f ≤ n := by
  classical
  exact sInf_le hn

/-- `f` is always below its nucleus closure. -/
lemma le_nucleusClosure (f : α → α) :
    f ≤ nucleusClosure (α := α) f := by
  classical
  intro x
  have : f x ≤ ⨅ (n : Nucleus α) (hn : n ∈ dominating (α := α) f), n x := by
    refine le_iInf ?_; intro n
    refine le_iInf ?_; intro hn
    simpa [dominating] using hn x
  simpa [nucleusClosure, dominating, sInf_apply] using this

/-- If `f ≤ g`, then `nucleusClosure f ≤ nucleusClosure g`. -/
lemma nucleusClosure_mono {f g : α → α}
    (hfg : ∀ x, f x ≤ g x) :
    nucleusClosure (α := α) f ≤ nucleusClosure (α := α) g := by
  classical
  have hsubset : dominating (α := α) g ⊆ dominating (α := α) f := by
    intro n hn x
    exact (hfg x).trans (hn x)
  refine le_sInf ?_
  intro n hn
  exact sInf_le (hsubset hn)

section UniformReflection

/-- The open nucleus `j_u(x) := u ⟶ x`. -/
noncomputable def openNucleus (u : α) : Nucleus α where
  toFun x := u ⇨ x
  map_inf' x y := by
    exact himp_inf_distrib u x y
  idempotent' x := by
    exact le_of_eq (himp_idem (a := x) (b := u))
  le_apply' x := by
    exact (le_himp_iff (a := x) (b := u) (c := x)).2 inf_le_left

@[simp] lemma openNucleus_apply (u : α) (x : α) :
    openNucleus (α := α) u x = u ⇨ x := rfl

/-- Larger `u` results in a smaller open nucleus; monotonicity in `u`. -/
lemma openNucleus_le_of_le {u v : α} (hv : v ≤ u) :
    openNucleus (α := α) u ≤ openNucleus (α := α) v := by
  intro x
  simpa [openNucleus] using himp_le_himp_right hv

open scoped Classical

/-- The uniform reflection meet `⋀_{p∈Γ} (Rα p ⟶ p)`. -/
noncomputable def uniformLawMeet (Rα : Nucleus α) (Γ : Finset α) : α :=
  by classical exact Γ.inf (fun p => Rα p ⇨ p)

lemma uniformLawMeet_le_of_mem
    (Rα : Nucleus α) {Γ : Finset α} {p : α} (hp : p ∈ Γ) :
    uniformLawMeet (α := α) Rα Γ ≤ Rα p ⇨ p := by
  classical
  simpa [uniformLawMeet] using Finset.inf_le (s := Γ) (f := fun q => Rα q ⇨ q) hp

/-- If `Rα ≤ Rβ`, then the uniform meets satisfy the reverse inequality. -/
lemma uniformLawMeet_antitone {Rα Rβ : Nucleus α} {Γ : Finset α}
    (h : Rα ≤ Rβ) :
    uniformLawMeet (α := α) Rβ Γ ≤ uniformLawMeet (α := α) Rα Γ := by
  classical
  refine Finset.le_inf ?_
  intro p hp
  have h₁ := uniformLawMeet_le_of_mem (Rα := Rβ) (Γ := Γ) hp
  have h₂ : Rβ p ⇨ p ≤ Rα p ⇨ p :=
    himp_le_himp_right (h p)
  exact h₁.trans h₂

/-- Baseline operator used in the uniform reflection step. -/
private noncomputable def uniformBaseline (Rα : Nucleus α) (Γ : Finset α) : α → α :=
  fun x =>
    let U := uniformLawMeet (α := α) Rα Γ
    Rα (openNucleus (α := α) U x)

/-- Successor-step nucleus obtained from the uniform baseline. -/
noncomputable def succStepUniform (Rα : Nucleus α) (Γ : Finset α) : Nucleus α :=
  nucleusClosure (α := α) (uniformBaseline (α := α) Rα Γ)

/-- The uniform successor step extends the current nucleus. -/
lemma le_succStepUniform (Rα : Nucleus α) (Γ : Finset α) :
    Rα ≤ succStepUniform (α := α) Rα Γ := by
  intro x
  change Rα x ≤ _
  have hx : x ≤ openNucleus (α := α) (uniformLawMeet (α := α) Rα Γ) x := by
    dsimp [openNucleus]
    exact (le_himp_iff (a := x) (b := uniformLawMeet (α := α) Rα Γ) (c := x)).2 inf_le_left
  have hopen := Rα.monotone hx
  exact hopen.trans
    ((le_nucleusClosure (α := α) (uniformBaseline (α := α) Rα Γ)) x)

/-- Monotonicity of the baseline under pointwise larger nuclei. -/
lemma uniformBaseline_mono {Rα Rβ : Nucleus α} {Γ : Finset α}
    (h : Rα ≤ Rβ) :
    uniformBaseline (α := α) Rα Γ ≤ uniformBaseline (α := α) Rβ Γ := by
  intro x
  classical
  have hopen' := openNucleus_le_of_le
      (uniformLawMeet_antitone (α := α) (Rα := Rα) (Rβ := Rβ) (Γ := Γ) h)
  have hopen := hopen' x
  have hx : Rα (openNucleus (α := α) (uniformLawMeet (α := α) Rα Γ) x) ≤
      Rβ (openNucleus (α := α) (uniformLawMeet (α := α) Rα Γ) x) := h _
  have hmono := Rβ.monotone hopen
  exact hx.trans hmono

/-- The uniform successor operator is monotone on nuclei. -/
lemma succStepUniform_mono (Γ : Finset α) :
    Monotone (fun Rα : Nucleus α => succStepUniform (α := α) Rα Γ) := by
  intro Rα Rβ hαβ
  exact nucleusClosure_mono (α := α)
    (f := uniformBaseline (α := α) Rα Γ)
    (g := uniformBaseline (α := α) Rβ Γ)
    (uniformBaseline_mono (α := α) (Rα := Rα) (Rβ := Rβ) (Γ := Γ) hαβ)

/-- Each generator `p ∈ Γ` is sent to top by the successor step. -/
lemma succStepUniform_law_true {Rα : Nucleus α} {Γ : Finset α} {p : α}
    (hp : p ∈ Γ) :
    succStepUniform (α := α) Rα Γ (Rα p ⇨ p) = ⊤ := by
  classical
  have hmeet : uniformLawMeet (α := α) Rα Γ ≤ Rα p ⇨ p :=
    uniformLawMeet_le_of_mem (Rα := Rα) (Γ := Γ) hp
  have hopen : openNucleus (α := α) (uniformLawMeet (α := α) Rα Γ)
      (Rα p ⇨ p) = ⊤ := by
    simpa [openNucleus] using himp_eq_top_iff.2 hmeet
  have hbase : uniformBaseline (α := α) Rα Γ (Rα p ⇨ p) = ⊤ := by
    simp [uniformBaseline, hopen]
  have hle : ⊤ ≤ succStepUniform (α := α) Rα Γ (Rα p ⇨ p) := by
    simpa [succStepUniform, uniformBaseline, hopen, hbase]
      using (le_nucleusClosure (α := α)
        (uniformBaseline (α := α) Rα Γ) (Rα p ⇨ p))
  exact top_le_iff.1 hle

end UniformReflection

open scoped Classical in

/-- Default reflection step: close under `n` and the identity via nucleusClosure. -/
noncomputable def defaultReflectStep (n : Nucleus α) : Nucleus α :=
  nucleusClosure (α := α) fun a => n a ⊔ a

/-- Every nucleus is below its default reflection step. -/
lemma le_defaultReflectStep (n : Nucleus α) :
    n ≤ defaultReflectStep (α := α) n := by
  intro a; dsimp [defaultReflectStep]
  have : n a ≤ n a ⊔ a := by exact le_sup_left
  have h := le_nucleusClosure (α := α) (fun x => n x ⊔ x)
  exact this.trans (h a)

/-- The default reflection step is monotone. -/
lemma defaultReflectStep_mono :
    Monotone (defaultReflectStep (α := α)) := by
  intro n m hnm
  refine nucleusClosure_mono (α := α) ?_
  intro a; exact sup_le_sup (hnm a) le_rfl

/-- A `ReflectionLaw` supplies the successor step in the progression: it must
be monotone on nuclei and inflationary (`n ≤ step n`). -/
structure ReflectionLaw where
  step : Nucleus α → Nucleus α
  step_mono : Monotone step
  le_step : ∀ n, n ≤ step n

namespace ReflectionLaw

@[simp]
lemma le_step_apply (law : ReflectionLaw (α := α)) (n : Nucleus α) :
    n ≤ law.step n := law.le_step n

@[simp]
lemma step_le_step (law : ReflectionLaw (α := α)) {m n : Nucleus α}
    (h : m ≤ n) : law.step m ≤ law.step n := law.step_mono h

end ReflectionLaw

/-- Default reflection law obtained from `defaultReflectStep`. -/
noncomputable def defaultReflectionLaw : ReflectionLaw (α := α) where
  step := defaultReflectStep (α := α)
  step_mono := defaultReflectStep_mono (α := α)
  le_step := le_defaultReflectStep (α := α)

/-- Uniform reflection law driven by a finite set of formulas `Γ`. -/
noncomputable def ReflectionLaw.uniform [HeytingAlgebra α]
    (Γ : Finset α) : ReflectionLaw (α := α) where
  step R := succStepUniform (α := α) R Γ
  step_mono := succStepUniform_mono (α := α) Γ
  le_step R := le_succStepUniform (α := α) (Rα := R) (Γ := Γ)

/-- Datum for a reflection progression: a base nucleus and a reflection law. -/
structure ReflectionSeed where
  base : Nucleus α
  law : ReflectionLaw (α := α)

namespace ReflectionSeed

variable (seed : ReflectionSeed (α := α))

/-- The successor action extracted from the reflection law. -/
def succOp : Nucleus α → Nucleus α := seed.law.step

@[simp] lemma succOp_mono : Monotone seed.succOp := seed.law.step_mono
@[simp] lemma le_succOp (n : Nucleus α) : n ≤ seed.succOp n := seed.law.le_step n

open scoped Ordinal

/-- Ordinal-indexed progression of nuclei obtained via transfinite iteration
of the supplied successor operator. -/
noncomputable def progression (o : Ordinal) : Nucleus α :=
  transfiniteIterate seed.succOp o seed.base

@[simp] lemma progression_zero : seed.progression 0 = seed.base := by
  classical
  simpa [progression] using
    (transfiniteIterate_bot (φ := seed.succOp) (i₀ := seed.base) (J := Ordinal))

private lemma ordinal_not_isMax (o : Ordinal) : ¬ IsMax o :=
  not_isMax_of_lt (lt_succ o)

@[simp] lemma progression_succ (o : Ordinal) :
    seed.progression (Order.succ o) = seed.succOp (seed.progression o) := by
  classical
  have h := transfiniteIterate_succ (φ := seed.succOp) (i₀ := seed.base)
      (J := Ordinal) o (ordinal_not_isMax o)
  simpa [progression] using h

lemma progression_limit {o : Ordinal} (ho : Order.IsSuccLimit o) :
    seed.progression o =
      ⨆ (x : Set.Iio o), seed.progression x.1 := by
  classical
  have := transfiniteIterate_limit (φ := seed.succOp) (i₀ := seed.base)
      (J := Ordinal) o ho
  simpa [progression] using this

lemma progression_monotone : Monotone seed.progression := by
  classical
  have h := monotone_transfiniteIterate (φ := seed.succOp) (i₀ := seed.base)
      (J := Ordinal) (fun n => seed.le_succOp n)
  simpa [progression]

lemma le_progression_succ (o : Ordinal) :
    seed.progression o ≤ seed.progression (Order.succ o) := by
  classical
  simp [progression_succ]

lemma base_le_progression (o : Ordinal) : seed.base ≤ seed.progression o := by
  classical
  have hmono := seed.progression_monotone
  have hbase := hmono (show (0 : Ordinal) ≤ o from bot_le)
  simpa [seed.progression_zero] using hbase

universe w

/-- Any repetition in the transfinite progression forces an immediate stabilization:
if `progression j₁ = progression j₂` for some `j₁ < j₂`, then
`progression (succ j₁) = progression j₁`. -/
lemma progression_stabilizes_of_eq_of_lt {o₁ o₂ : Ordinal.{w}}
    (h : seed.progression o₁ = seed.progression o₂) (ho : o₁ < o₂) :
    seed.progression (Order.succ o₁) = seed.progression o₁ := by
  classical
  have hmono := seed.progression_monotone
  have h_le₁ : seed.progression o₁ ≤ seed.progression (Order.succ o₁) :=
    hmono (Order.le_succ o₁)
  have h_le₂ : seed.progression (Order.succ o₁) ≤ seed.progression o₁ := by
    have : seed.progression (Order.succ o₁) ≤ seed.progression o₂ :=
      hmono (Order.succ_le_of_lt ho)
    simpa [h] using this
  exact le_antisymm h_le₂ h_le₁

/-- Existence of a stabilization stage under the purely set-theoretic hypothesis that the
progression map is not injective. -/
lemma exists_stabilization_of_not_injective
    (H : ¬ Function.Injective (fun o : Ordinal.{w} => seed.progression o)) :
    ∃ o : Ordinal.{w}, seed.progression (Order.succ o) = seed.progression o := by
  classical
  dsimp [Function.Injective] at H
  push_neg at H
  rcases H with ⟨o₁, o₂, hEq, hne⟩
  rcases lt_or_gt_of_ne hne with ho | ho
  · exact ⟨o₁, progression_stabilizes_of_eq_of_lt (seed := seed) hEq ho⟩
  · exact ⟨o₂, progression_stabilizes_of_eq_of_lt (seed := seed) hEq.symm ho⟩

end ReflectionSeed

end ReflectionLaws

end Logic
end HeytingLean
