import Mathlib/Data/List/Basic
import Mathlib/Order/CompleteLattice

open scoped Classical

namespace HeytingLean.LoF.Lens

/-! # Trace Lens (prefix-closed interior)

We work on the carrier `Set (List α)` with the prefix relation. We define a
meet‑preserving interior operator `I` that removes any word whose prefixes are
not all inside the set. The fixed points of `I` are exactly the prefix‑closed
sets (safety properties).
-/

variable {α : Type _}

def Prefix (u w : List α) : Prop := ∃ s, u ++ s = w

namespace Prefix

@[simp] lemma refl (u : List α) : Prefix u u := ⟨[], by simp⟩

lemma trans {u v w : List α} : Prefix u v → Prefix v w → Prefix u w := by
  intro h₁ h₂
  rcases h₁ with ⟨s₁, hs₁⟩; rcases h₂ with ⟨s₂, hs₂⟩
  refine ⟨s₁ ++ s₂, ?_⟩
  simpa [List.append_assoc] using by
    simpa [hs₁] using congrArg (fun t => t ++ s₂) hs₁

end Prefix

/-- Interior operator: keep exactly those traces whose every prefix is in `X`. -/
def I (X : Set (List α)) : Set (List α) :=
  {u | ∀ v, Prefix v u → v ∈ X}

namespace I

variable (X Y : Set (List α))

@[simp] lemma mem_iff {u : List α} : u ∈ I (α := α) X ↔ ∀ v, Prefix v u → v ∈ X := Iff.rfl

lemma subset : I (α := α) X ⊆ X := by
  intro u hu
  have : u ∈ X := (mem_iff (X := X)).mp hu u (Prefix.refl u)
  simpa using this

lemma monotone (hXY : X ⊆ Y) : I (α := α) X ⊆ I (α := α) Y := by
  intro u hu
  exact fun v hv => hXY ((mem_iff (X := X)).mp hu v hv)

lemma idempotent : I (α := α) (I (α := α) X) = I (α := α) X := by
  apply Set.Subset.antisymm
  · intro u hu; -- u ∈ I(I X) ⇒ u ∈ I X
    intro v hv
    -- need v ∈ X; we know: v ∈ I X since v is prefix of u and u ∈ I(I X)
    have hvIX : v ∈ I (α := α) X := (mem_iff (X := I (α := α) X)).mp hu v hv
    -- from v ∈ I X we know every prefix w of v lies in X; pick w = v
    exact (mem_iff (X := X)).mp hvIX v (Prefix.refl v)
  · -- I X ⊆ I (I X) by monotonicity and X ⊆ I X is not true; use `⊆` direction explicitly
    intro u hu
    intro v hv
    -- If u ∈ I X then every prefix v of u lies in X; we must show v ∈ I X
    -- That is, every prefix w of v lies in X
    intro w hw
    -- v prefix u and w prefix v ⇒ w prefix u
    have hw' : Prefix w u := Prefix.trans hw hv
    exact (mem_iff (X := X)).mp hu w hw'

lemma inf_preserving : I (α := α) (X ∩ Y) = I (α := α) X ∩ I (α := α) Y := by
  apply Set.ext; intro u; constructor
  · intro hu
    have hX : u ∈ I (α := α) X :=
      fun v hv => (Set.mem_inter_iff.mp ((mem_iff (X := X ∩ Y)).mp hu v hv)).left
    have hY : u ∈ I (α := α) Y :=
      fun v hv => (Set.mem_inter_iff.mp ((mem_iff (X := X ∩ Y)).mp hu v hv)).right
    exact Set.mem_inter_iff.mpr ⟨hX, hY⟩
  · intro hu
    rcases Set.mem_inter_iff.mp hu with ⟨hX, hY⟩
    exact (mem_iff (X := X ∩ Y)).mpr (fun v hv => Set.mem_inter_iff.mpr ⟨hX v hv, hY v hv⟩)

end I

end HeytingLean.LoF.Lens

