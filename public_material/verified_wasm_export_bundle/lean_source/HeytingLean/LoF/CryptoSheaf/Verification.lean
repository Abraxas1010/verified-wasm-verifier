import HeytingLean.LoF.CryptoSheaf.Presheaf

/-
CryptoSheaf/Verification

Local-to-global verification for computation sheaves over a `PosetSite` using
an abstract locality assumption packaged in the predicate.
-/

namespace HeytingLean
namespace LoF
namespace CryptoSheaf

variable {C : Type _} [PartialOrder C]

def restr {S : PosetSite C} {F : CompPresheaf S}
    {U V : C} (h : V ≤ U) (s : F.Sections U) : F.Sections V :=
  F.restrict (U := U) (V := V) h s

structure VerificationPredicate {S : PosetSite C} (F : CompSheaf S) where
  verify : ∀ U : C, F.toCompPresheaf.Sections U → Prop
  stable : ∀ {U V : C} (h : V ≤ U) (s : F.toCompPresheaf.Sections U),
    verify U s → verify V (restr (S := S) (F := F.toCompPresheaf) h s)
  locality : ∀ (U : C) (cover : List C) (cover_le : ∀ V ∈ cover, V ≤ U)
      (s : F.toCompPresheaf.Sections U),
      (∀ V (hV : V ∈ cover),
        verify V (restr (S := S) (F := F.toCompPresheaf) (cover_le V hV) s)) →
      verify U s

theorem local_to_global_verification
    {S : PosetSite C} (F : CompSheaf S) (vp : VerificationPredicate F)
    (U : C) (cover : List C) (cover_le : ∀ V ∈ cover, V ≤ U)
    (fam : CompatibleFamily S F.toCompPresheaf U cover cover_le)
    (local_verified : ∀ V (hV : V ∈ cover),
      vp.verify V (fam.local_sections V hV)) :
    vp.verify U (F.sheaf.glue U cover cover_le fam) := by
  -- Use locality with the glued section and glue_restrict
  refine vp.locality U cover cover_le (F.sheaf.glue U cover cover_le fam) ?h
  intro V hV
  have hres := F.sheaf.glue_restrict U cover cover_le fam V hV
  -- Rewrite restriction to the provided local section and apply locality
  have : vp.verify V (fam.local_sections V hV) := local_verified V hV
  simpa [restr, F.sheaf.glue_restrict U cover cover_le fam V hV] using this

/-! ## Value-oriented helpers -/

/-- Value-based verification: the section’s value entails the given property. -/
def ValueVerifies {S : PosetSite C} (F : CompPresheaf S)
    (U : C) (s : F.Sections U) (property : S.Logic U) : Prop :=
  F.value U s ≤ property

/-- If the cover contains `U` and every local value is `⊤`, then the glued value is `⊤`.

This uses identity-restriction at `U` together with `glue_restrict`. We phrase it
with the membership hypothesis `hU : U ∈ cover` because in general a cover need
not detect global top values unless it includes the identity. -/
theorem local_top_global_top
    {S : PosetSite C} (F : CompSheaf S) (U : C) (cover : List C)
    (cover_le : ∀ V ∈ cover, V ≤ U)
    (fam : CompatibleFamily S F.toCompPresheaf U cover cover_le)
    (hU : U ∈ cover)
    (local_tops : ∀ V (hV : V ∈ cover),
      F.toCompPresheaf.value V (fam.local_sections V hV) = ⊤) :
    F.toCompPresheaf.value U (F.sheaf.glue U cover cover_le fam) = ⊤ := by
  -- Reduce via value_restrict along the identity map at `U`.
  -- Chain equalities: use identity restriction, naturality of `value`, and glue-restrict.
  calc
    F.toCompPresheaf.value U (F.sheaf.glue U cover cover_le fam)
        = S.restrict (U := U) (V := U) (le_rfl : U ≤ U)
            (F.toCompPresheaf.value U (F.sheaf.glue U cover cover_le fam)) := by
          simpa using
            (S.restrict_id (U := U)
              (x := F.toCompPresheaf.value U (F.sheaf.glue U cover cover_le fam))).symm
    _   = F.toCompPresheaf.value U
            (F.toCompPresheaf.restrict (U := U) (V := U) (le_rfl : U ≤ U)
              (F.sheaf.glue U cover cover_le fam)) := by
          simpa using
            (F.toCompPresheaf.value_restrict (U := U) (V := U)
              (h := (le_rfl : U ≤ U)) (s := F.sheaf.glue U cover cover_le fam))
    _   = F.toCompPresheaf.value U (fam.local_sections U hU) := by
          exact congrArg (fun z => F.toCompPresheaf.value U z)
            (F.sheaf.glue_restrict U cover cover_le fam U hU)
    _   = ⊤ := local_tops U hU

end CryptoSheaf
end LoF
end HeytingLean
