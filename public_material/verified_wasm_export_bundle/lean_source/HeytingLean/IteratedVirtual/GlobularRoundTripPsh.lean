import HeytingLean.IteratedVirtual.GlobularFromPresheaf
import HeytingLean.IteratedVirtual.GlobularToPresheaf
import HeytingLean.IteratedVirtual.GlobularRoundTrip

/-!
# IteratedVirtual.GlobularRoundTripPsh

Phase‑8 strict-only hygiene: the presheaf→structured→presheaf round-trip is naturally isomorphic
to the original presheaf globular set.

Concretely, for `X : GlobularIndexᵒᵖ ⥤ Type u` we define:
- `X.toGlobularSet : GlobularSet` using `X.map` on the generating morphisms `src`, `tgt`;
- `(X.toGlobularSet).toPresheaf : GlobularIndexᵒᵖ ⥤ Type u` using the canonical `downSrc/downTgt`
  recursion induced by the globular identities.

This file proves `(X.toGlobularSet).toPresheaf ≅ X`.
-/

namespace HeytingLean
namespace IteratedVirtual

open CategoryTheory

universe u

namespace GlobularSetPsh

open GlobularIndex

private theorem toGlobularSet_toPresheaf_map_eq (X : GlobularSetPsh.{u})
    {a b : GlobularIndex.Objᵒᵖ} (f : a ⟶ b) :
    ((X.toGlobularSet).toPresheaf).map f = X.map f := by
  classical
  -- Reduce to the canonical object representatives `Opposite.op ⟨n⟩`.
  cases a with
  | op a0 =>
    cases b with
    | op b0 =>
      cases a0 with
      | mk na =>
        cases b0 with
        | mk nb =>
          -- Prove by induction on the top dimension `na`.
          have main :
              ∀ (na nb : Nat)
                (f : Opposite.op ({ n := na } : GlobularIndex.Obj) ⟶ Opposite.op ({ n := nb } : GlobularIndex.Obj)),
                ((X.toGlobularSet).toPresheaf).map f = X.map f := by
            intro na
            induction na with
            | zero =>
                intro nb f
                funext x
                -- If the top dimension is 0, the only morphism is the identity, so both maps are `id`.
                cases hk : f.unop.kind with
                | none =>
                    -- `f.unop.valid` forces `nb = 0`, and `f` is the identity.
                    have hab : ({ n := nb } : GlobularIndex.Obj) = { n := 0 } := by
                      simpa [hk] using f.unop.valid
                    cases hab
                    have hf_unop : f.unop = GlobularIndex.Hom.id ({ n := 0 } : GlobularIndex.Obj) := by
                      apply GlobularIndex.Hom.ext
                      simp [hk, GlobularIndex.Hom.id]
                    have hf : f = 𝟙 (Opposite.op ({ n := 0 } : GlobularIndex.Obj)) := by
                      simpa using congrArg Quiver.Hom.op hf_unop
                    simp [hf]
                | some choice =>
                    -- Impossible: would require `nb < 0`.
                    have : nb < 0 := by simpa [hk] using f.unop.valid
                    cases Nat.not_lt_zero nb this
            | succ na ih =>
                intro nb f
                funext x
                cases hk : f.unop.kind with
                | none =>
                    -- Identity case.
                    have hab : ({ n := nb } : GlobularIndex.Obj) = { n := na.succ } := by
                      simpa [hk] using f.unop.valid
                    cases hab
                    have hf_unop : f.unop = GlobularIndex.Hom.id ({ n := na.succ } : GlobularIndex.Obj) := by
                      apply GlobularIndex.Hom.ext
                      simp [hk, GlobularIndex.Hom.id]
                    have hf : f = 𝟙 (Opposite.op ({ n := na.succ } : GlobularIndex.Obj)) := by
                      simpa using congrArg Quiver.Hom.op hf_unop
                    simp [hf]
                | some choice =>
                    have hlt : nb < na.succ := by simpa [hk] using f.unop.valid
                    have hle : nb ≤ na := Nat.le_of_lt_succ hlt
                    cases choice with
                    | false =>
                        -- Source-branch: the unique “false” maps are recovered by iterating `src`.
                        cases Nat.lt_or_eq_of_le hle with
                        | inr hEq =>
                            -- One-step: `nb = na`.
                            cases hEq
                            have hf_unop : f.unop = GlobularIndex.Hom.src na := by
                              apply GlobularIndex.Hom.ext
                              simp [hk, GlobularIndex.Hom.src]
                            have hf : f = (GlobularIndex.src na).op := by
                              simpa [GlobularIndex.src] using congrArg Quiver.Hom.op hf_unop
                            -- Generator step: `src` agrees definitionally after the round-trip.
                            have hsrc :
                                ((X.toGlobularSet).toPresheaf).map (GlobularIndex.src na).op x =
                                  X.map (GlobularIndex.src na).op x := by
                              calc
                                ((X.toGlobularSet).toPresheaf).map (GlobularIndex.src na).op x =
                                    (X.toGlobularSet).src x := by
                                  simp
                                _ = X.map (GlobularIndex.src na).op x := by
                                  simp [GlobularSetPsh.toGlobularSet]
                            cases hf
                            exact hsrc
                        | inl hlt' =>
                            -- Multi-step: factor through the top `src` and apply IH.
                            let g : GlobularIndex.Hom ({ n := nb } : GlobularIndex.Obj) ({ n := na } : GlobularIndex.Obj) :=
                              { kind := some false
                                valid := hlt' }
                            let top : GlobularIndex.Hom ({ n := na } : GlobularIndex.Obj) ({ n := na.succ } : GlobularIndex.Obj) :=
                              GlobularIndex.Hom.src na
                            have hf_unop : f.unop = GlobularIndex.Hom.comp g top := by
                              apply GlobularIndex.Hom.ext
                              have hkind :
                                  (GlobularIndex.Hom.comp g top).kind = some false := by
                                simp [GlobularIndex.Hom.comp, g, top, GlobularIndex.Hom.src]
                              simp [hk, hkind]
                            have hf : f = Quiver.Hom.op top ≫ Quiver.Hom.op g := by
                              simpa using congrArg Quiver.Hom.op hf_unop
                            have htop :
                                ((X.toGlobularSet).toPresheaf).map (Quiver.Hom.op top) x =
                                  X.map (Quiver.Hom.op top) x := by
                              -- Generator step at the top boundary.
                              calc
                                ((X.toGlobularSet).toPresheaf).map (Quiver.Hom.op top) x =
                                    (X.toGlobularSet).src x := by
                                  simp [top]
                                _ = X.map (Quiver.Hom.op top) x := by
                                  simp [top, GlobularSetPsh.toGlobularSet]
                            have ihg :
                                ((X.toGlobularSet).toPresheaf).map (Quiver.Hom.op g) = X.map (Quiver.Hom.op g) := by
                              simpa using ih nb (Quiver.Hom.op g)
                            simp [hf, htop, ihg]
                    | true =>
                        -- Target-branch: the unique “true” maps are recovered by iterating `tgt`.
                        cases Nat.lt_or_eq_of_le hle with
                        | inr hEq =>
                            cases hEq
                            have hf_unop : f.unop = GlobularIndex.Hom.tgt na := by
                              apply GlobularIndex.Hom.ext
                              simp [hk, GlobularIndex.Hom.tgt]
                            have hf : f = (GlobularIndex.tgt na).op := by
                              simpa [GlobularIndex.tgt] using congrArg Quiver.Hom.op hf_unop
                            have htgt :
                                ((X.toGlobularSet).toPresheaf).map (GlobularIndex.tgt na).op x =
                                  X.map (GlobularIndex.tgt na).op x := by
                              calc
                                ((X.toGlobularSet).toPresheaf).map (GlobularIndex.tgt na).op x =
                                    (X.toGlobularSet).tgt x := by
                                  simp
                                _ = X.map (GlobularIndex.tgt na).op x := by
                                  simp [GlobularSetPsh.toGlobularSet]
                            cases hf
                            exact htgt
                        | inl hlt' =>
                            let g : GlobularIndex.Hom ({ n := nb } : GlobularIndex.Obj) ({ n := na } : GlobularIndex.Obj) :=
                              { kind := some true
                                valid := hlt' }
                            let top : GlobularIndex.Hom ({ n := na } : GlobularIndex.Obj) ({ n := na.succ } : GlobularIndex.Obj) :=
                              GlobularIndex.Hom.tgt na
                            have hf_unop : f.unop = GlobularIndex.Hom.comp g top := by
                              apply GlobularIndex.Hom.ext
                              have hkind :
                                  (GlobularIndex.Hom.comp g top).kind = some true := by
                                simp [GlobularIndex.Hom.comp, g, top, GlobularIndex.Hom.tgt]
                              simp [hk, hkind]
                            have hf : f = Quiver.Hom.op top ≫ Quiver.Hom.op g := by
                              simpa using congrArg Quiver.Hom.op hf_unop
                            have htop :
                                ((X.toGlobularSet).toPresheaf).map (Quiver.Hom.op top) x =
                                  X.map (Quiver.Hom.op top) x := by
                              calc
                                ((X.toGlobularSet).toPresheaf).map (Quiver.Hom.op top) x =
                                    (X.toGlobularSet).tgt x := by
                                  simp [top]
                                _ = X.map (Quiver.Hom.op top) x := by
                                  simp [top, GlobularSetPsh.toGlobularSet]
                            have ihg :
                                ((X.toGlobularSet).toPresheaf).map (Quiver.Hom.op g) = X.map (Quiver.Hom.op g) := by
                              simpa using ih nb (Quiver.Hom.op g)
                            simp [hf, htop, ihg]
          simpa using main na nb f

/-- Presheaf→structured→presheaf is naturally isomorphic to the original presheaf globular set. -/
def toGlobularSet_toPresheafIso (X : GlobularSetPsh.{u}) : (X.toGlobularSet).toPresheaf ≅ X where
  hom :=
    { app := fun _ x => x
      naturality := by
        intro a b f
        -- With identity components, naturality reduces to equality of maps.
        ext x
        simpa using congrArg (fun g => g x) (toGlobularSet_toPresheaf_map_eq (X := X) f) }
  inv :=
    { app := fun _ x => x
      naturality := by
        intro a b f
        ext x
        simpa using (congrArg (fun g => g x) (toGlobularSet_toPresheaf_map_eq (X := X) f)).symm }
  hom_inv_id := by
    ext a x
    rfl
  inv_hom_id := by
    ext a x
    rfl

end GlobularSetPsh

end IteratedVirtual
end HeytingLean
