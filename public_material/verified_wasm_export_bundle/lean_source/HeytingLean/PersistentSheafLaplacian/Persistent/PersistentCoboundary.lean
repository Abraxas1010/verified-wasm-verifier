import HeytingLean.PersistentSheafLaplacian.Persistent.Filtration
import HeytingLean.PersistentSheafLaplacian.Cochain.CochainComplex

namespace HeytingLean
namespace PersistentSheafLaplacian

open SimplicialComplex

namespace Persistent

open Cochain

variable {V : Type*} [DecidableEq V]

/-- Restrict an ambient orientation to a subcomplex by reusing the same ordered vertices on each
simplex of the subcomplex. -/
noncomputable def inducedOrientation {X Y : SimplicialComplex V}
    (hXY : X.IsSubcomplex Y) (oY : Orientation Y) : Orientation X where
  orderedVertices σ := oY.orderedVertices (inclusionSimplex hXY σ)
  nodup σ := oY.nodup (inclusionSimplex hXY σ)
  toFinset_eq σ := by
    simpa [inclusionSimplex] using oY.toFinset_eq (inclusionSimplex hXY σ)

/-- Explicit pullback witness for sheaves across a subcomplex inclusion. -/
structure IsPullbackSheaf {X Y : SimplicialComplex V}
    (hXY : X.IsSubcomplex Y) (F : CellularSheaf X) (G : CellularSheaf Y) where
  stalkIso :
    ∀ σ : X.Simplex, F.stalkType σ ≃ₗ[ℝ] G.stalkType (inclusionSimplex hXY σ)
  restriction_compat :
    ∀ {σ τ : X.Simplex} (hστ : σ ≤ τ),
      (stalkIso τ).toLinearMap ∘ₗ F.restriction hστ =
        G.restriction (inclusionSimplex_face hXY hστ) ∘ₗ (stalkIso σ).toLinearMap

/-- Data of a persistent sheaf pair `X ⊆ Y` together with a pullback witness. -/
structure PersistentSheafPair (X Y : SimplicialComplex V) where
  hXY : X.IsSubcomplex Y
  G : CellularSheaf Y
  F : CellularSheaf X
  hPullback : IsPullbackSheaf hXY F G

namespace PersistentSheafPair

variable {X Y : SimplicialComplex V} (P : PersistentSheafPair X Y)

/-- Transport a pulled-back restriction in `Y` back down to the corresponding restriction in `X`. -/
theorem stalkIso_symm_restriction_eq {σ τ : X.Simplex} (hστ : σ ≤ τ)
    (x : P.F.stalkType σ) :
    (P.hPullback.stalkIso τ).symm
      (P.G.restriction (inclusionSimplex_face P.hXY hστ) ((P.hPullback.stalkIso σ) x)) =
        P.F.restriction hστ x := by
  have hcompat := LinearMap.congr_fun (P.hPullback.restriction_compat hστ) x
  apply (P.hPullback.stalkIso τ).injective
  simpa using hcompat.symm

/-- Transfer a `q`-cochain on `Y` down to `X` via the pullback stalk isomorphisms. -/
noncomputable def projectionCochain (q : Nat) :
    CochainGroup P.G q →ₗ[ℝ] CochainGroup P.F q where
  toFun := fun g σ =>
    (P.hPullback.stalkIso σ.1).symm (g (inclusionqSimplex P.hXY q σ))
  map_add' := by
    intro g h
    ext σ
    simp
  map_smul' := by
    intro c g
    ext σ
    simp

/-- Transfer a `q`-cochain on `X` up to `Y` via the pullback stalk isomorphisms. -/
noncomputable def inclusionCochain (q : Nat) :
    CochainGroup P.F q →ₗ[ℝ] CochainGroup P.G q where
  toFun := fun f σ =>
    if hσ : σ.1.1 ∈ X.simplices then
      let σX : X.Simplex := ⟨σ.1.1, hσ⟩
      let hqX : σX ∈ X.qSimplices q := by
        rw [SimplicialComplex.mem_qSimplices (K := X)]
        exact (SimplicialComplex.mem_qSimplices (K := Y)).mp σ.2
      P.hPullback.stalkIso σX (f ⟨σX, hqX⟩)
    else
      0
  map_add' := by
    intro f g
    ext σ
    by_cases hσ : σ.1.1 ∈ X.simplices
    · simp [hσ]
    · simp [hσ]
  map_smul' := by
    intro c f
    ext σ
    by_cases hσ : σ.1.1 ∈ X.simplices
    · simp [hσ]
    · simp [hσ]

/-- On an included simplex, `inclusionCochain` is exactly the stalk isomorphism on the original
    cochain value. -/
@[simp] theorem inclusionCochain_apply_inclusionqSimplex (q : Nat)
    (f : CochainGroup P.F q) (σ : X.qSimplices q) :
    inclusionCochain P q f (inclusionqSimplex P.hXY q σ) =
      P.hPullback.stalkIso σ.1 (f σ) := by
  simp [inclusionCochain, inclusionqSimplex, inclusionSimplex]

/-- The current persistent coboundary surface: transport to the ambient sheaf, apply the ambient
    coboundary, then project back to the subcomplex sheaf. This keeps the development anchored on
    the explicit pullback-pair data instead of introducing an orthogonal-complement shortcut. -/
noncomputable def persistentCoboundary (q : Nat) (oY : Orientation Y) :
    CochainGroup P.F q →ₗ[ℝ] CochainGroup P.F (q + 1) :=
  projectionCochain P (q + 1) ∘ₗ Cochain.coboundary P.G oY q ∘ₗ inclusionCochain P q

@[simp] theorem inducedOrientation_signedIncidence {σ τ : X.Simplex} (hστ : σ ≤ τ)
    (oY : Orientation Y) :
    Orientation.signedIncidence (inducedOrientation P.hXY oY) hστ =
      Orientation.signedIncidence oY (inclusionSimplex_face P.hXY hστ) := by
  rfl

/-- Inclusion transports a basis `Pi.single` cochain on `X` to the corresponding included
`Pi.single` cochain on `Y`. -/
theorem inclusionCochain_piSingle (q : Nat) (σ : X.qSimplices q)
    (x : P.F.stalkType σ.1) :
    inclusionCochain P q (Pi.single σ x) =
      Pi.single (inclusionqSimplex P.hXY q σ) (P.hPullback.stalkIso σ.1 x) := by
  classical
  ext τ
  by_cases hτX : τ.1.1 ∈ X.simplices
  · let τX : X.Simplex := ⟨τ.1.1, hτX⟩
    have hqX : τX ∈ X.qSimplices q := by
      rw [SimplicialComplex.mem_qSimplices (K := X)]
      exact (SimplicialComplex.mem_qSimplices (K := Y)).mp τ.2
    have hneq :
        (⟨τX, hqX⟩ : X.qSimplices q) ≠ σ →
          τ ≠ inclusionqSimplex P.hXY q σ := by
      intro hτσ hEq
      apply hτσ
      apply Subtype.ext
      apply Subtype.ext
      simpa [inclusionqSimplex, inclusionSimplex] using congrArg (fun z => z.1.1) hEq
    by_cases hEq : (⟨τX, hqX⟩ : X.qSimplices q) = σ
    · have hτEq : τ = inclusionqSimplex P.hXY q σ := by
        have hset : τ.1.1 = σ.1.1 := by
          simpa using congrArg (fun z : X.qSimplices q => z.1.1) hEq
        apply Subtype.ext
        apply Subtype.ext
        simpa [inclusionqSimplex, inclusionSimplex] using hset
      subst hτEq
      simp [inclusionCochain, inclusionqSimplex, inclusionSimplex]
    · have hτneq : τ ≠ inclusionqSimplex P.hXY q σ := hneq hEq
      have hEq' : σ ≠ (⟨τX, hqX⟩ : X.qSimplices q) := by
        simpa [eq_comm] using hEq
      have hτEqX : τ = inclusionqSimplex P.hXY q ⟨τX, hqX⟩ := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      rw [hτEqX]
      rw [inclusionCochain_apply_inclusionqSimplex]
      have hincneq :
          inclusionqSimplex P.hXY q σ ≠ inclusionqSimplex P.hXY q ⟨τX, hqX⟩ := by
        intro hinc
        apply hτneq
        simpa [hτEqX] using hinc.symm
      have hincneq' :
          inclusionqSimplex P.hXY q ⟨τX, hqX⟩ ≠ inclusionqSimplex P.hXY q σ := by
        simpa [eq_comm] using hincneq
      simp [Pi.single, hEq, hincneq']
  · have hneq : τ ≠ inclusionqSimplex P.hXY q σ := by
      intro hEq
      apply hτX
      simpa [hEq] using P.hXY σ.1.2
    simp [inclusionCochain, hτX, hneq]

/-- The transported persistent coboundary agrees with the ordinary coboundary on the pullback
sheaf, provided we restrict the ambient orientation to the subcomplex. -/
theorem persistentCoboundary_piSingle_eq_coboundary_piSingle
    (q : Nat) (oY : Orientation Y) (σ : X.qSimplices q)
    (x : P.F.stalkType σ.1) (τ : X.qSimplices (q + 1)) :
    P.persistentCoboundary q oY (Pi.single σ x) τ =
      Cochain.coboundary P.F (inducedOrientation P.hXY oY) q (Pi.single σ x) τ := by
  classical
  by_cases hface : σ.1 ≤ τ.1
  · have hincFace : (inclusionqSimplex P.hXY q σ).1 ≤ (inclusionqSimplex P.hXY (q + 1) τ).1 :=
      inclusionSimplex_face P.hXY hface
    rw [persistentCoboundary, LinearMap.comp_apply, LinearMap.comp_apply]
    simp [projectionCochain]
    rw [inclusionCochain_piSingle]
    rw [Cochain.coboundary_piSingle P.G oY q
      (inclusionqSimplex P.hXY q σ) (P.hPullback.stalkIso σ.1 x)
      (inclusionqSimplex P.hXY (q + 1) τ)]
    rw [Cochain.coboundary_piSingle P.F (inducedOrientation P.hXY oY) q σ x τ]
    simp [hincFace, hface]
    rw [PersistentSheafPair.inducedOrientation_signedIncidence (P := P) (oY := oY) hface]
    exact congrArg
      (fun v => (((Orientation.signedIncidence oY hincFace : ℤ) : ℝ) • v))
      (P.stalkIso_symm_restriction_eq hface x)
  · have hincNotFace :
        ¬ (inclusionqSimplex P.hXY q σ).1 ≤ (inclusionqSimplex P.hXY (q + 1) τ).1 := by
      intro hinc
      exact hface hinc
    rw [persistentCoboundary, LinearMap.comp_apply, LinearMap.comp_apply]
    simp [projectionCochain]
    rw [inclusionCochain_piSingle]
    rw [Cochain.coboundary_piSingle P.G oY q
      (inclusionqSimplex P.hXY q σ) (P.hPullback.stalkIso σ.1 x)
      (inclusionqSimplex P.hXY (q + 1) τ)]
    rw [Cochain.coboundary_piSingle P.F (inducedOrientation P.hXY oY) q σ x τ]
    simp [hincNotFace, hface]

section SortedReduction

variable [LinearOrder V]

theorem persistentCoboundary_eq_coboundary_induced
    (q : Nat) (oY : Orientation Y) :
    P.persistentCoboundary q oY =
      Cochain.coboundary P.F (inducedOrientation P.hXY oY) q := by
  classical
  apply LinearMap.ext
  intro f
  ext τ
  calc
    P.persistentCoboundary q oY f τ =
        (P.persistentCoboundary q oY
          (∑ σ ∈ (X.qSimplices q).attach, Pi.single σ (f σ))) τ := by
            rw [cochain_eq_sum_piSingle P.F q f]
    _ =
        ∑ σ ∈ (X.qSimplices q).attach,
          P.persistentCoboundary q oY (Pi.single σ (f σ)) τ := by
            have hmap :
                P.persistentCoboundary q oY
                    (∑ σ ∈ (X.qSimplices q).attach, Pi.single σ (f σ)) =
                  ∑ σ ∈ (X.qSimplices q).attach,
                    P.persistentCoboundary q oY (Pi.single σ (f σ)) := by
                      rw [map_sum]
            simpa using congrArg (fun g => g τ) hmap
    _ =
        ∑ σ ∈ (X.qSimplices q).attach,
          Cochain.coboundary P.F (inducedOrientation P.hXY oY) q
            (Pi.single σ (f σ)) τ := by
              apply Finset.sum_congr rfl
              intro σ hσ
              exact persistentCoboundary_piSingle_eq_coboundary_piSingle P q oY σ (f σ) τ
    _ =
        (Cochain.coboundary P.F (inducedOrientation P.hXY oY) q
          (∑ σ ∈ (X.qSimplices q).attach, Pi.single σ (f σ))) τ := by
            have hmap :
                Cochain.coboundary P.F (inducedOrientation P.hXY oY) q
                    (∑ σ ∈ (X.qSimplices q).attach, Pi.single σ (f σ)) =
                  ∑ σ ∈ (X.qSimplices q).attach,
                    Cochain.coboundary P.F (inducedOrientation P.hXY oY) q
                      (Pi.single σ (f σ)) := by
                        rw [map_sum]
            simpa using congrArg (fun g => g τ) hmap.symm
    _ = Cochain.coboundary P.F (inducedOrientation P.hXY oY) q f τ := by
          rw [cochain_eq_sum_piSingle P.F q f]

@[simp] theorem inducedOrientation_sorted :
    inducedOrientation P.hXY (Orientation.sortedOrientation Y) =
      Orientation.sortedOrientation X :=
  rfl

theorem persistentCoboundary_eq_coboundary_sorted (q : Nat) :
    P.persistentCoboundary q (Orientation.sortedOrientation Y) =
      Cochain.coboundary P.F (Orientation.sortedOrientation X) q := by
  simpa [inducedOrientation_sorted] using
    (persistentCoboundary_eq_coboundary_induced P q (Orientation.sortedOrientation Y))

end SortedReduction

theorem projectionCochain_inclusionCochain (q : Nat) :
    projectionCochain P q ∘ₗ inclusionCochain P q = LinearMap.id := by
  apply LinearMap.ext
  intro f
  ext σ
  simp [projectionCochain, inclusionCochain, inclusionqSimplex, inclusionSimplex]

theorem projectionCochain_surjective (q : Nat) :
    Function.Surjective (projectionCochain P q) := by
  intro f
  refine ⟨inclusionCochain P q f, ?_⟩
  simpa using LinearMap.congr_fun (projectionCochain_inclusionCochain P q) f

theorem inclusionCochain_injective (q : Nat) :
    Function.Injective (inclusionCochain P q) :=
  Function.LeftInverse.injective <|
    fun f => by
      simpa using LinearMap.congr_fun (projectionCochain_inclusionCochain P q) f

end PersistentSheafPair

end Persistent

end PersistentSheafLaplacian
end HeytingLean
