import HeytingLean.Quantum.OML.Core
import HeytingLean.Quantum.OML.Sasaki
import HeytingLean.Quantum.Translate.Modality

open scoped Classical

namespace HeytingLean.Quantum.Translate

variable {β α : Type _}
variable [HeytingLean.Quantum.OML.OrthocomplementedLattice β]
variable [HeytingLean.Quantum.OML.OrthomodularLattice β]
variable [CompleteLattice α]

/-- A translation of an orthomodular lattice `β` into a complete lattice `α`
equipped with a modality `M`. The map `tr` preserves meets up to closure and
is subadditive for joins under closure. This abstracts negative/daseinisation
style embeddings used to obtain a Heyting image. -/
structure QLMap (β α : Type _)
  [HeytingLean.Quantum.OML.OrthocomplementedLattice β]
  [HeytingLean.Quantum.OML.OrthomodularLattice β] [CompleteLattice α] where
  M : Modality α
  tr : β → α
  map_inf : ∀ x y, tr (x ⊓ y) = M.close (tr x ⊓ tr y)
  map_sup_le : ∀ x y, M.close (tr x ⊔ tr y) ≥ tr (x ⊔ y)

namespace QLMap

variable (F : QLMap β α)

@[simp] lemma close_tr_inf (x y : β) :
  F.M.close (F.tr x ⊓ F.tr y) = F.tr (x ⊓ y) := by
  simpa using (F.map_inf x y).symm

lemma tr_sup_le (x y : β) : F.tr (x ⊔ y) ≤ F.M.close (F.tr x ⊔ F.tr y) :=
  (F.map_sup_le x y).trans_eq rfl

end QLMap

/-! ### Complement preservation and Sasaki bridge -/

open HeytingLean.Quantum.OML

namespace QLMap

variable (F : QLMap β α)

/-- Helper: closing a right argument before joining does not change the final closure. -/
private lemma close_sup_close_right (x y : α) :
    F.M.J (x ⊔ F.M.J y) = F.M.J (x ⊔ y) := by
  apply le_antisymm
  ·
    have hx : x ≤ F.M.J (x ⊔ y) := by
      have hx' : x ≤ x ⊔ y := le_sup_left
      have hx'' := F.M.J.monotone hx'
      exact (Nucleus.le_apply (n := F.M.J) (x := x)).trans hx''
    have hy : F.M.J y ≤ F.M.J (x ⊔ y) := by
      have hy' : y ≤ x ⊔ y := le_sup_right
      exact F.M.J.monotone hy'
    have h := sup_le hx hy
    have h' := F.M.J.monotone h
    simpa [Modality.close, F.M.idempotent] using h'
  ·
    have h_base : x ⊔ y ≤ x ⊔ F.M.J y :=
      sup_le_sup_left (Nucleus.le_apply (n := F.M.J) (x := y)) _
    have h := F.M.J.monotone h_base
    simpa [Modality.close] using h

/-- Symmetric helper: closing the left argument before joining does not change the final closure. -/
private lemma close_sup_close_left (x y : α) :
    F.M.J (F.M.J x ⊔ y) = F.M.J (x ⊔ y) := by
  simpa [sup_comm] using (close_sup_close_right (F := F) (x := y) (y := x))

/-- Raw bridge: translating a Sasaki hook is bounded by the nucleus applied to
`T (aᶜ) ⊔ T b`.  This does not require any complement-preservation property. -/
lemma sasakiHook_le_translated_nucleus_imp_raw (a b : β) :
    F.tr (sasakiHook a b)
      ≤ F.M.J (F.tr (OrthocomplementedLattice.compl a) ⊔ F.tr b) := by
  -- push Sasaki hook through the translation using join subadditivity
  have h_sup : F.tr (sasakiHook a b)
      ≤ F.M.close (F.tr (OrthocomplementedLattice.compl a) ⊔ F.tr (a ⊓ b)) := by
    change F.tr (OrthocomplementedLattice.compl a ⊔ (a ⊓ b)) ≤ _
    simpa [sasakiHook] using
      F.map_sup_le (x := OrthocomplementedLattice.compl a) (y := a ⊓ b)
  -- bound the translated meet by closing the right component
  have h_tr_inf : F.tr (a ⊓ b) = F.M.close (F.tr a ⊓ F.tr b) :=
    F.map_inf a b
  have h_tr_inf_le : F.tr (a ⊓ b) ≤ F.M.J (F.tr b) := by
    have h_mono : F.M.close (F.tr a ⊓ F.tr b) ≤ F.M.J (F.tr b) :=
      F.M.J.monotone (inf_le_right : F.tr a ⊓ F.tr b ≤ F.tr b)
    calc
      F.tr (a ⊓ b) = F.M.close (F.tr a ⊓ F.tr b) := h_tr_inf
      _ ≤ F.M.J (F.tr b) := h_mono
  have h_sup_args :
      F.tr (OrthocomplementedLattice.compl a) ⊔ F.tr (a ⊓ b)
        ≤ F.tr (OrthocomplementedLattice.compl a) ⊔ F.M.J (F.tr b) :=
    sup_le_sup_left h_tr_inf_le _
  have h_step :
      F.tr (sasakiHook a b)
        ≤ F.M.close (F.tr (OrthocomplementedLattice.compl a) ⊔ F.M.J (F.tr b)) :=
    h_sup.trans (F.M.J.monotone h_sup_args)
  -- collapse the redundant closure on the right join
  have h_collapse :
      F.M.J (F.tr (OrthocomplementedLattice.compl a) ⊔ F.M.J (F.tr b))
        = F.M.J (F.tr (OrthocomplementedLattice.compl a) ⊔ F.tr b) :=
    close_sup_close_right (F := F)
      (x := F.tr (OrthocomplementedLattice.compl a)) (y := F.tr b)
  have h_step' := h_step
  simp [Modality.close, h_collapse] at h_step'
  exact h_step'

variable [HasCompl α]

/-- A translation that preserves orthocomplements *after* closing by the modality. -/
class ComplPreserving (F : QLMap β α) : Prop where
  compl_closed :
    ∀ a : β,
      F.M.J (F.tr (OrthocomplementedLattice.compl a))
        = F.M.J ((F.tr a)ᶜ)

/-- Refined bridge: if the translation preserves complements up to the modality,
    the target inequality assumes the usual Heyting shape `J ((T a)ᶜ ⊔ T b)`. -/
lemma sasakiHook_le_translated_nucleus_imp
    (hCompl : ComplPreserving F) (a b : β) :
    F.tr (sasakiHook a b) ≤ F.M.J ((F.tr a)ᶜ ⊔ F.tr b) := by
  -- start from the raw bridge
  have h_raw := sasakiHook_le_translated_nucleus_imp_raw (F := F) (a := a) (b := b)
  -- rewrite the complement side inside the closure using complement preservation
  have h_left :
      F.tr (OrthocomplementedLattice.compl a) ≤ F.M.J ((F.tr a)ᶜ) := by
    have h_infl := Nucleus.le_apply (n := F.M.J)
        (x := F.tr (OrthocomplementedLattice.compl a))
    simpa [hCompl.compl_closed (a := a)] using h_infl
  have h_sup :
      F.tr (OrthocomplementedLattice.compl a) ⊔ F.tr b
        ≤ F.M.J ((F.tr a)ᶜ) ⊔ F.tr b := by
    refine sup_le ?_ ?_
    · exact le_sup_of_le_left h_left
    · exact le_sup_right
  have h_after_close := F.M.J.monotone h_sup
  have h_collapse :
      F.M.J (F.M.J ((F.tr a)ᶜ) ⊔ F.tr b)
        = F.M.J ((F.tr a)ᶜ ⊔ F.tr b) := by
    have h := close_sup_close_right (F := F) (x := F.tr b) (y := (F.tr a)ᶜ)
    simpa [sup_comm] using h
  exact h_raw.trans (h_after_close.trans (by
    simp [h_collapse]))

end QLMap

end HeytingLean.Quantum.Translate
