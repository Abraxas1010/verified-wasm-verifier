import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal
import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Data.Fin.SuccPred
import HeytingLean.LoF.Combinators.Category.Groupoid

/-!
# InfinityGroupoid.SSet — SKY ∞-groupoid via Kan complexes (simplicial sets)

Mathlib works in (classical) homotopy theory, not HoTT.  A standard, fully formal way to model
an **∞-groupoid** is as a **Kan complex** (a fibrant simplicial set).

In this file we package the SKY “formal invertibility” layer as a simplicial set:

* `SKY∞ : SSet` is the nerve of the free groupoid completion `MWFreeGroupoid`.
* The main objective is to prove `SSet.KanComplex SKY∞`, giving a genuine ω/∞-groupoid object.
* We then expose the truncation tower using `SSet.truncation`.

Notes:
* The groupoid completion is **formal** (inverses are not computational SKY reductions).
* This file is intentionally `mathlib`-native: the ∞-groupoid is a Kan complex, and truncations are
  `SSet.Truncated n` objects.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace InfinityGroupoid

open CategoryTheory Simplicial Opposite Limits
open SSet

open scoped Simplicial
open scoped SSet.modelCategoryQuillen

/-! ## The SKY ∞-groupoid object -/

/-- The simplicial set modelling SKY as an ∞-groupoid: the nerve of the free groupoid completion. -/
abbrev SKYInfty : SSet :=
  CategoryTheory.nerve HeytingLean.LoF.Combinators.Category.MWFreeGroupoid

/-! ## Truncation tower (Postnikov-style) -/

/-- The `n`-truncation of `SKY∞` in the simplicial-set sense (as a truncated simplicial object). -/
abbrev SKYInftyTrunc (n : ℕ) : SSet.Truncated n :=
  (SSet.truncation n).obj SKYInfty

/-!
## Mathlib lemmas used in Kan-complex proofs

These are small “plumbing” lemmas that connect:
- horn face inclusions,
- `yonedaEquiv` for standard simplices,
- and simplicial face maps `δ`.

They are useful when proving horn-filling properties by reducing equalities of horn-restrictions
to equalities of `δ`-faces of a chosen filler simplex.
-/

section Plumbing

/-!
`yonedaEquiv` is Yoneda's lemma for standard simplices.  The following lemma packages the key
naturality statement specialized to the face maps `δ`.
-/
lemma delta_yonedaEquiv {X : SSet} {n : ℕ} (σ : Δ[n + 1] ⟶ X) (j : Fin (n + 2)) :
    X.δ j (yonedaEquiv σ) = yonedaEquiv (stdSimplex.δ j ≫ σ) := by
  simpa [SimplicialObject.δ, SSet.yonedaEquiv, SSet.stdSimplex] using
    (CategoryTheory.uliftYonedaEquiv_naturality (C := SimplexCategory) (F := X) (f := σ)
      (g := (SimplexCategory.δ j).op))

/-!
The horn face `horn.face i j h` is defined using `Subpresheaf.lift (stdSimplex.δ j)`; under the
coercion to `Δ[n+1]`, it is exactly the canonical simplex `yonedaEquiv (stdSimplex.δ j)`.
-/
lemma horn_face_val {n : ℕ} (i j : Fin (n + 2)) (h : j ≠ i) :
    (SSet.horn.face (n := n) i j h : (Λ[n + 1, i] : SSet) _⦋n⦌).val =
      yonedaEquiv (stdSimplex.δ j) := by
  simp [SSet.horn.face, SSet.Subcomplex.yonedaEquiv_coe]
  simpa using
    (CategoryTheory.Subpresheaf.lift_ι (f := stdSimplex.δ j)
      (G := (Λ[n + 1, i] : (Δ[n + 1] : SSet).Subcomplex))
      (hf := by
        simpa using (SSet.face_le_horn (n := n + 1) (i := j) (j := i) h)))

end Plumbing

/-!
## 2-truncation isomorphisms for high-dimensional horns

For horns `Λ[n+2, i]` with `n ≥ 2` (i.e. dimension ≥ 4), every 0/1/2-simplex involves at most
4 vertices, so it automatically lies in the horn (there are `n+3 ≥ 5` vertices total).  This
implies that the 2-truncation of the horn inclusion is an isomorphism.

These lemmas are used in the coskeleton-based extension argument below: if `X` is 2-coskeletal,
maps `A ⟶ X` are determined by the 2-truncation of `A`, so an isomorphism on 2-truncations is
enough to extend horn maps in dimensions ≥ 4.
-/

section Trunc2Horns

open Finset

private lemma horn_obj_one_top {n : ℕ} (i : Fin (n + 3)) (hn : 2 ≤ n) :
    (horn (n + 2) i).obj (op ⦋1⦌) = ⊤ := by
  ext x
  simp [horn, stdSimplex.asOrderHom, Set.eq_univ_iff_forall]
  classical
  let S : Finset (Fin (n + 3)) := {i, (stdSimplex.asOrderHom x) 0, (stdSimplex.asOrderHom x) 1}
  have hcard : S.card ≤ 3 := by
    simpa [S] using (Finset.card_le_three : S.card ≤ 3)
  have hS : S ≠ Finset.univ := by
    intro hSu
    have hEq : S.card = (Finset.univ : Finset (Fin (n + 3))).card := congrArg Finset.card hSu
    have hUniv : (Finset.univ : Finset (Fin (n + 3))).card = n + 3 := by
      simp
    have hN : n + 3 ≤ 3 := by
      have : n + 3 = S.card := by
        simpa [hUniv] using hEq.symm
      simpa [this] using hcard
    have h5 : (5 : Nat) ≤ n + 3 := by
      omega
    have h53 : (5 : Nat) ≤ 3 := h5.trans hN
    have : ¬ ((5 : Nat) ≤ 3) := by decide
    exact this h53
  have : ∃ v : Fin (n + 3), v ∉ S := by
    simpa [Finset.eq_univ_iff_forall] using hS
  rcases this with ⟨v, hv⟩
  refine ⟨v, ?_, ?_⟩
  · intro hvi
    apply hv
    simp [S, hvi]
  · intro a
    fin_cases a
    · intro hx
      apply hv
      have : v = (stdSimplex.asOrderHom x) 0 := by
        simpa [stdSimplex.asOrderHom] using hx.symm
      simp [S, this]
    · intro hx
      apply hv
      have : v = (stdSimplex.asOrderHom x) 1 := by
        simpa [stdSimplex.asOrderHom] using hx.symm
      simp [S, this]

private lemma horn_obj_two_top {n : ℕ} (i : Fin (n + 3)) (hn : 2 ≤ n) :
    (horn (n + 2) i).obj (op ⦋2⦌) = ⊤ := by
  ext x
  simp [horn, stdSimplex.asOrderHom, Set.eq_univ_iff_forall]
  classical
  let S : Finset (Fin (n + 3)) :=
    {i, (stdSimplex.asOrderHom x) 0, (stdSimplex.asOrderHom x) 1, (stdSimplex.asOrderHom x) 2}
  have hcard : S.card ≤ 4 := by
    simpa [S] using (Finset.card_le_four : S.card ≤ 4)
  have hS : S ≠ Finset.univ := by
    intro hSu
    have hEq : S.card = (Finset.univ : Finset (Fin (n + 3))).card := congrArg Finset.card hSu
    have hUniv : (Finset.univ : Finset (Fin (n + 3))).card = n + 3 := by
      simp
    have hN : n + 3 ≤ 4 := by
      have : n + 3 = S.card := by
        simpa [hUniv] using hEq.symm
      simpa [this] using hcard
    have h5 : (5 : Nat) ≤ n + 3 := by
      omega
    have h54 : (5 : Nat) ≤ 4 := h5.trans hN
    have : ¬ ((5 : Nat) ≤ 4) := by decide
    exact this h54
  have : ∃ v : Fin (n + 3), v ∉ S := by
    simpa [Finset.eq_univ_iff_forall] using hS
  rcases this with ⟨v, hv⟩
  refine ⟨v, ?_, ?_⟩
  · intro hvi
    apply hv
    simp [S, hvi]
  · intro a
    fin_cases a
    · intro hx
      apply hv
      have : v = (stdSimplex.asOrderHom x) 0 := by
        simpa [stdSimplex.asOrderHom] using hx.symm
      simp [S, this]
    · intro hx
      apply hv
      have : v = (stdSimplex.asOrderHom x) 1 := by
        simpa [stdSimplex.asOrderHom] using hx.symm
      simp [S, this]
    · intro hx
      apply hv
      have : v = (stdSimplex.asOrderHom x) 2 := by
        simpa [stdSimplex.asOrderHom] using hx.symm
      simp [S, this]

/-!
`rw`/`simp` sometimes fails to rewrite membership goals of the form `x ∈ S` using a hypothesis
`h : S = ⊤` when `S` comes from a `Subpresheaf.obj` projection.  The following helper turns
`S = ⊤` into a membership proof by applying both sides to the element.
-/
private lemma mem_of_eq_top {α : Type*} {S : Set α} (h : S = (⊤ : Set α)) (x : α) : x ∈ S := by
  change S x
  have hx := congrArg (fun (T : Set α) => T x) h
  dsimp at hx
  exact (hx ▸ trivial)

/-- For `n ≥ 2`, the 2-truncation of the horn inclusion `Λ[n+2,i] ⟶ Δ[n+2]` is an isomorphism. -/
lemma truncation₂_horn_ι_isIso {n : ℕ} (i : Fin (n + 3)) (hn : 2 ≤ n) :
    IsIso ((SSet.truncation 2).map (Λ[n + 2, i].ι)) := by
  classical
  rw [CategoryTheory.NatTrans.isIso_iff_isIso_app]
  intro X
  -- `X` ranges over objects in the 2-truncated simplex category, i.e. lengths 0/1/2.
  cases X using Opposite.rec with
  | op X =>
    rcases X with ⟨Δ, hΔ⟩
    cases Δ using SimplexCategory.rec with
    | _ m =>
      have hm : m ≤ 2 := by simpa using hΔ
      cases m with
      | zero =>
        -- length 0: Mathlib already proves horn.obj is ⊤
        refine
          (CategoryTheory.isIso_iff_bijective
                (((SSet.truncation 2).map (Λ[n + 2, i].ι)).app
                  (op ⟨SimplexCategory.mk 0, hm⟩))).2 ?_
        refine And.intro ?_ ?_
        · intro a b hab
          exact Subtype.ext hab
        · intro y
          refine ⟨⟨y, ?_⟩, rfl⟩
          change y ∈ (Λ[n + 2, i]).obj (op ⦋0⦌)
          simp [SSet.horn_obj_zero (n := n) (i := i)]
      | succ m =>
          cases m with
          | zero =>
            -- length 1
            have htop : (horn (n + 2) i).obj (op ⦋1⦌) = ⊤ := horn_obj_one_top (n := n) i hn
            refine
              (CategoryTheory.isIso_iff_bijective
                    (((SSet.truncation 2).map (Λ[n + 2, i].ι)).app
                      (op ⟨SimplexCategory.mk 1, hm⟩))).2 ?_
            refine And.intro ?_ ?_
            · intro a b hab
              exact Subtype.ext hab
            · intro y
              refine ⟨⟨y, ?_⟩, rfl⟩
              change y ∈ (Λ[n + 2, i]).obj (op ⦋1⦌)
              exact mem_of_eq_top htop y
          | succ m =>
              cases m with
              | zero =>
                -- length 2
                have htop : (horn (n + 2) i).obj (op ⦋2⦌) = ⊤ := horn_obj_two_top (n := n) i hn
                refine
                  (CategoryTheory.isIso_iff_bijective
                        (((SSet.truncation 2).map (Λ[n + 2, i].ι)).app
                          (op ⟨SimplexCategory.mk 2, hm⟩))).2 ?_
                refine And.intro ?_ ?_
                · intro a b hab
                  exact Subtype.ext hab
                · intro y
                  refine ⟨⟨y, ?_⟩, rfl⟩
                  change y ∈ (Λ[n + 2, i]).obj (op ⦋2⦌)
                  exact mem_of_eq_top htop y
              | succ m =>
                  -- impossible since `hm : (m+3) ≤ 2`
                  exfalso
                  omega

end Trunc2Horns

/-!
## Coskeletal bridge: maps into a 2-coskeletal simplicial set are determined by `truncation 2`.

Mathlib proves that the nerve of any category is 2-coskeletal.  The following equivalence is the
categorical mechanism we use to extend **high-dimensional horn maps**: for a 2-coskeletal target
`X`, giving a map `A ⟶ X` is equivalent to giving the truncated map
`(truncation 2).obj A ⟶ (truncation 2).obj X`.
-/

section CoskeletalBridge

open CategoryTheory

universe u

/-- If `X` is 2-coskeletal, maps `A ⟶ X` are equivalent to maps of 2-truncations. -/
noncomputable def homEquivTrunc2 {X A : SSet.{u}}
    [CategoryTheory.SimplicialObject.IsCoskeletal X 2] :
    (A ⟶ X) ≃ ((SSet.truncation 2).obj A ⟶ (SSet.truncation 2).obj X) := by
  classical
  let e : X ≅ (SSet.cosk 2).obj X :=
    CategoryTheory.SimplicialObject.isoCoskOfIsCoskeletal (X := X) 2
  have e1 : (A ⟶ X) ≃ (A ⟶ (SSet.cosk 2).obj X) :=
    (Iso.homCongr (Iso.refl A) e)
  have e2 :
      ((SSet.truncation 2).obj A ⟶ (SSet.truncation 2).obj X) ≃ (A ⟶ (SSet.cosk 2).obj X) :=
    (SSet.coskAdj 2).homEquiv A ((SSet.truncation 2).obj X)
  exact e1.trans e2.symm

/-- Naturality of `homEquivTrunc2` with respect to precomposition. -/
lemma homEquivTrunc2_naturality_left {X : SSet.{u}}
    [CategoryTheory.SimplicialObject.IsCoskeletal X 2]
    {A A' : SSet.{u}} (h : A' ⟶ A) (f : A ⟶ X) :
    homEquivTrunc2 (X := X) (A := A') (h ≫ f) =
      (SSet.truncation 2).map h ≫ homEquivTrunc2 (X := X) (A := A) f := by
  classical
  simp [homEquivTrunc2]
  simpa [Category.assoc] using
    (SSet.coskAdj 2).homEquiv_naturality_left_symm (f := h)
      (g := f ≫ (SimplicialObject.coskAdj 2).unit.app X)

/-- For `n ≥ 2`, any map from a high-dimensional horn `Λ[n+2,i]` into a 2-coskeletal simplicial set
extends to the simplex `Δ[n+2]`. -/
lemma hornFilling_ge4_of_isCoskeletal {X : SSet.{u}}
    [CategoryTheory.SimplicialObject.IsCoskeletal X 2]
    {n : ℕ} (i : Fin (n + 3)) (hn : 2 ≤ n) (σ₀ : (Λ[n + 2, i] : SSet.{u}) ⟶ X) :
    ∃ σ : (Δ[n + 2] : SSet.{u}) ⟶ X, σ₀ = Λ[n + 2, i].ι ≫ σ := by
  classical
  let eΛ := homEquivTrunc2 (X := X) (A := (Λ[n + 2, i] : SSet.{u}))
  let eΔ := homEquivTrunc2 (X := X) (A := (Δ[n + 2] : SSet.{u}))
  haveI : IsIso ((SSet.truncation 2).map (Λ[n + 2, i].ι)) :=
    truncation₂_horn_ι_isIso (n := n) i hn
  let tσ : (SSet.truncation 2).obj (Δ[n + 2] : SSet.{u}) ⟶ (SSet.truncation 2).obj X :=
    inv ((SSet.truncation 2).map (Λ[n + 2, i].ι)) ≫ eΛ σ₀
  refine ⟨eΔ.symm tσ, ?_⟩
  apply eΛ.injective
  simp [tσ, eΔ, eΛ, homEquivTrunc2_naturality_left]

end CoskeletalBridge

/-!
## Kan complex: the nerve of a groupoid

Mathlib gives:
* the nerve of any category is a quasicategory (inner horn filling);
* the nerve of any category is 2-coskeletal (so horns in dimensions ≥ 4 fill automatically).

For a **groupoid**, we additionally fill the remaining *outer* horns in dimensions 1–3, which
completes the Kan-complex proof.
-/

section NerveKan

universe u v

open SSet.modelCategoryQuillen

variable {C : Type u} [CategoryTheory.Groupoid.{v} C]

private abbrev N : SSet := CategoryTheory.nerve C

private lemma hornFilling_dim1 (i : Fin 2)
    (σ₀ : (Λ[1, i] : SSet) ⟶ N (C := C)) :
    ∃ σ : (Δ[1] : SSet) ⟶ N (C := C), σ₀ = Λ[1, i].ι ≫ σ := by
  classical
  -- The 1-dimensional horn is a single vertex; fill using the identity edge at that vertex.
  fin_cases i
  · -- `i = 0`: only face is `j = 1`.
    let j : Fin 2 := 1
    have hj : j ≠ (0 : Fin 2) := by decide
    let v : (Λ[1, (0 : Fin 2)] : SSet) _⦋0⦌ := SSet.horn.face (n := 0) 0 j hj
    let X : C := (σ₀.app _ v).obj' 0
    let τ : (N (C := C)) _⦋1⦌ := CategoryTheory.ComposableArrows.mk₁ (𝟙 X)
    refine ⟨SSet.yonedaEquiv.symm τ, ?_⟩
    apply SSet.horn.hom_ext
    intro j' hj'
    fin_cases j'
    · cases hj' rfl
    · -- `j' = 1`
      have hv : (SSet.horn.face (n := 0) (i := (0 : Fin 2)) (j := j) hj') = v := by
        apply Subtype.ext
        simp [v, horn_face_val]
      -- Compare 0-simplices by their unique object.
      apply CategoryTheory.ComposableArrows.ext₀
      -- First, normalize the varying proof of `j ≠ i`.
      have hX :
          (σ₀.app _ (SSet.horn.face (n := 0) (i := (0 : Fin 2)) (j := j) hj')).obj 0 =
            (σ₀.app _ v).obj 0 := by
        simp [hv]
      -- Then compute the RHS vertex of the degenerate 1-simplex `τ`.
      -- `simp` can now close the goal.
      simpa [hX, v, X, τ, horn_face_val, SSet.yonedaEquiv_comp, CategoryTheory.nerve.δ_obj]
  · -- `i = 1`: only face is `j = 0`.
    let j : Fin 2 := 0
    have hj : j ≠ (1 : Fin 2) := by decide
    let v : (Λ[1, (1 : Fin 2)] : SSet) _⦋0⦌ := SSet.horn.face (n := 0) 1 j hj
    let X : C := (σ₀.app _ v).obj' 0
    let τ : (N (C := C)) _⦋1⦌ := CategoryTheory.ComposableArrows.mk₁ (𝟙 X)
    refine ⟨SSet.yonedaEquiv.symm τ, ?_⟩
    apply SSet.horn.hom_ext
    intro j' hj'
    fin_cases j'
    · -- `j' = 0`
      have hv : (SSet.horn.face (n := 0) (i := (1 : Fin 2)) (j := j) hj') = v := by
        apply Subtype.ext
        simp [v, horn_face_val]
      apply CategoryTheory.ComposableArrows.ext₀
      have hX :
          (σ₀.app _ (SSet.horn.face (n := 0) (i := (1 : Fin 2)) (j := j) hj')).obj 0 =
            (σ₀.app _ v).obj 0 := by
        simp [hv]
      simpa [hX, v, X, τ, horn_face_val, SSet.yonedaEquiv_comp, CategoryTheory.nerve.δ_obj]
    · cases hj' rfl

/-- Naturality of `δ` with respect to a simplicial-set map. -/
private lemma delta_app {X Y : SSet} (η : X ⟶ Y) {n : ℕ} (i : Fin (n + 2))
    (x : X _⦋n + 1⦌) :
    Y.δ i (η.app _ x) = η.app _ (X.δ i x) := by
  simpa [SimplicialObject.δ] using
    congrArg (fun k => k x) (η.naturality (SimplexCategory.δ i).op).symm

/-!
### Dependent-typing helpers for `ComposableArrows`

In the nerve, 1-simplices are `ComposableArrows C 1`, and their field `hom` is dependently typed
(its domain/codomain are `left/right`). This lemma turns an equality of 1-simplices into a usable
equality of morphisms, inserting the necessary `eqToHom` casts.
-/

private lemma hom_conj_of_eq {a b : (N (C := C)) _⦋1⦌} (h : a = b) :
    a.hom =
      eqToHom (congrArg CategoryTheory.ComposableArrows.left h) ≫
        b.hom ≫
          eqToHom (congrArg CategoryTheory.ComposableArrows.right h).symm := by
  exact
    (conj_eqToHom_iff_heq (f := a.hom) (g := b.hom)
        (h := congrArg CategoryTheory.ComposableArrows.left h)
        (h' := congrArg CategoryTheory.ComposableArrows.right h)).2
      (congr_arg_heq (·.hom) h)

/-! ### Vertex identifications inside a 2-simplex in the nerve -/

private lemma delta0_left_eq_delta2_right (t : (N (C := C)) _⦋2⦌) :
    ((N (C := C)).δ (0 : Fin 3) t).left = ((N (C := C)).δ (2 : Fin 3) t).right := by
  change ((N (C := C)).δ (0 : Fin 3) t).obj ⟨0, by decide⟩ =
      ((N (C := C)).δ (2 : Fin 3) t).obj ⟨1, by decide⟩
  simp [CategoryTheory.nerve.δ_obj, Fin.succAbove_of_le_castSucc, Fin.succAbove_of_castSucc_lt]

private lemma delta1_right_eq_delta0_right (t : (N (C := C)) _⦋2⦌) :
    ((N (C := C)).δ (1 : Fin 3) t).right = ((N (C := C)).δ (0 : Fin 3) t).right := by
  change ((N (C := C)).δ (1 : Fin 3) t).obj ⟨1, by decide⟩ =
      ((N (C := C)).δ (0 : Fin 3) t).obj ⟨1, by decide⟩
  simp [CategoryTheory.nerve.δ_obj, Fin.succAbove_of_le_castSucc]

private lemma delta1_left_eq_delta2_left (t : (N (C := C)) _⦋2⦌) :
    ((N (C := C)).δ (1 : Fin 3) t).left = ((N (C := C)).δ (2 : Fin 3) t).left := by
  change ((N (C := C)).δ (1 : Fin 3) t).obj ⟨0, by decide⟩ =
      ((N (C := C)).δ (2 : Fin 3) t).obj ⟨0, by decide⟩
  simp [CategoryTheory.nerve.δ_obj, Fin.succAbove_of_castSucc_lt]

/-! ### Two-simplex bookkeeping in the nerve -/

private lemma triangle_rel (t : (N (C := C)) _⦋2⦌) :
    ((N (C := C)).δ (1 : Fin 3) t).hom =
      ((N (C := C)).δ (2 : Fin 3) t).hom ≫ ((N (C := C)).δ (0 : Fin 3) t).hom := by
  -- The long edge `0 ⟶ 2` is the composite of the short edges `0 ⟶ 1` and `1 ⟶ 2`.
  change t.map' 0 2 (hij := by decide) (hjn := by decide) =
    t.map' 0 1 (hij := by decide) (hjn := by decide) ≫
      t.map' 1 2 (hij := by decide) (hjn := by decide)
  simp [CategoryTheory.ComposableArrows.map'_comp (F := t) (i := 0) (j := 1) (k := 2)
      (hij := by decide) (hjk := by decide) (hk := by decide)]

private lemma mk2_of_simplex (t : (N (C := C)) _⦋2⦌) :
    t = CategoryTheory.ComposableArrows.mk₂ ((N (C := C)).δ (2 : Fin 3) t).hom
          ((N (C := C)).δ (0 : Fin 3) t).hom := by
  -- A 2-simplex in the nerve is determined by its two short edges.
  refine CategoryTheory.ComposableArrows.ext₂ rfl rfl rfl ?_ ?_
  · simp
    change t.map' 0 1 (hij := by decide) (hjn := by decide) =
      ((N (C := C)).δ (2 : Fin 3) t).hom
    rfl
  · simp
    change t.map' 1 2 (hij := by decide) (hjn := by decide) =
      ((N (C := C)).δ (0 : Fin 3) t).hom
    rfl

/-! ### Faces of `mk₃` in the nerve -/

private lemma delta₃_mk₃_eq {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) :
    (N (C := C)).δ (3 : Fin 4) (CategoryTheory.ComposableArrows.mk₃ f g h) =
      CategoryTheory.ComposableArrows.mk₂ f g := by
  refine CategoryTheory.ComposableArrows.ext₂ rfl rfl rfl ?_ ?_
  · simp
    change ((N (C := C)).δ (3 : Fin 4) (CategoryTheory.ComposableArrows.mk₃ f g h)).map'
        0 1 (hij := by decide) (hjn := by decide) =
      (CategoryTheory.ComposableArrows.mk₂ f g).map' 0 1 (hij := by decide) (hjn := by decide)
    rfl
  · simp
    change ((N (C := C)).δ (3 : Fin 4) (CategoryTheory.ComposableArrows.mk₃ f g h)).map'
        1 2 (hij := by decide) (hjn := by decide) =
      (CategoryTheory.ComposableArrows.mk₂ f g).map' 1 2 (hij := by decide) (hjn := by decide)
    rfl

private lemma delta₂_mk₃_eq {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) :
    (N (C := C)).δ (2 : Fin 4) (CategoryTheory.ComposableArrows.mk₃ f g h) =
      CategoryTheory.ComposableArrows.mk₂ f (g ≫ h) := by
  refine CategoryTheory.ComposableArrows.ext₂ rfl rfl rfl ?_ ?_
  · simp
    change ((N (C := C)).δ (2 : Fin 4) (CategoryTheory.ComposableArrows.mk₃ f g h)).map'
        0 1 (hij := by decide) (hjn := by decide) =
      (CategoryTheory.ComposableArrows.mk₂ f (g ≫ h)).map' 0 1 (hij := by decide) (hjn := by decide)
    rfl
  · simp
    change ((N (C := C)).δ (2 : Fin 4) (CategoryTheory.ComposableArrows.mk₃ f g h)).map'
        1 2 (hij := by decide) (hjn := by decide) =
      (CategoryTheory.ComposableArrows.mk₂ f (g ≫ h)).map' 1 2 (hij := by decide) (hjn := by decide)
    rfl

private lemma delta₁_mk₃_eq {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) :
    (N (C := C)).δ (1 : Fin 4) (CategoryTheory.ComposableArrows.mk₃ f g h) =
      CategoryTheory.ComposableArrows.mk₂ (f ≫ g) h := by
  refine CategoryTheory.ComposableArrows.ext₂ rfl rfl rfl ?_ ?_
  · simp
    change ((N (C := C)).δ (1 : Fin 4) (CategoryTheory.ComposableArrows.mk₃ f g h)).map'
        0 1 (hij := by decide) (hjn := by decide) =
      (CategoryTheory.ComposableArrows.mk₂ (f ≫ g) h).map' 0 1 (hij := by decide) (hjn := by decide)
    rfl
  · simp
    change ((N (C := C)).δ (1 : Fin 4) (CategoryTheory.ComposableArrows.mk₃ f g h)).map'
        1 2 (hij := by decide) (hjn := by decide) =
      (CategoryTheory.ComposableArrows.mk₂ (f ≫ g) h).map' 1 2 (hij := by decide) (hjn := by decide)
    rfl

/-!
### Outer 2-horns

For `Λ[2,0]`, the horn data are:
* an edge `0 ⟶ 1` (face `j=2`), and
* an edge `0 ⟶ 2` (face `j=1`),
and we solve for the missing edge `1 ⟶ 2` using the inverse of `0 ⟶ 1`.

The case `Λ[2,2]` is dual: solve for the missing `0 ⟶ 1` using the inverse of `1 ⟶ 2`.
-/

private lemma hornFilling_dim2_outer0
    (σ₀ : (Λ[2, (0 : Fin 3)] : SSet) ⟶ N (C := C)) :
    ∃ σ : (Δ[2] : SSet) ⟶ N (C := C), σ₀ = Λ[2, (0 : Fin 3)].ι ≫ σ := by
  classical
  let fFace : (Λ[2, (0 : Fin 3)] : SSet) _⦋1⦌ :=
    SSet.horn.face (n := 1) (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide)
  let hFace : (Λ[2, (0 : Fin 3)] : SSet) _⦋1⦌ :=
    SSet.horn.face (n := 1) (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)
  let f₁ : (N (C := C)) _⦋1⦌ := σ₀.app _ fFace
  let h₁ : (N (C := C)) _⦋1⦌ := σ₀.app _ hFace

  -- Show the two short faces share the same source vertex (vertex `0` in `Δ[2]`).
  have hVertex :
      (Λ[2, (0 : Fin 3)] : SSet).δ (1 : Fin 2) fFace =
        (Λ[2, (0 : Fin 3)] : SSet).δ (1 : Fin 2) hFace := by
    apply Subtype.ext
    -- identify the values in `Δ[2]`
    change (Δ[2] : SSet).δ (1 : Fin 2) fFace.val =
      (Δ[2] : SSet).δ (1 : Fin 2) hFace.val
    -- both sides are vertex `0`
    ext k
    fin_cases k
    -- `ext` reduces 0-simplices to their unique value, and this is definitional.
    simp [fFace, hFace, horn_face_val]
    rfl

  have hδ :
      (N (C := C)).δ (1 : Fin 2) f₁ = (N (C := C)).δ (1 : Fin 2) h₁ := by
    -- Rewrite both sides via `delta_app`, then use `hVertex`.
    calc
      (N (C := C)).δ (1 : Fin 2) f₁
          = σ₀.app _ ((Λ[2, (0 : Fin 3)] : SSet).δ (1 : Fin 2) fFace) := by
            simpa [f₁] using (delta_app (η := σ₀) (i := (1 : Fin 2)) (x := fFace))
      _ = σ₀.app _ ((Λ[2, (0 : Fin 3)] : SSet).δ (1 : Fin 2) hFace) := by
            simp [hVertex]
      _ = (N (C := C)).δ (1 : Fin 2) h₁ := by
            symm
            simpa [h₁] using (delta_app (η := σ₀) (i := (1 : Fin 2)) (x := hFace))

  have e0 : f₁.left = h₁.left := by
    have := congrArg (fun (x : (N (C := C)) _⦋0⦌) => x.obj ⟨0, by decide⟩) hδ
    simpa [CategoryTheory.nerve.δ_obj, f₁, h₁] using this

  -- Construct the missing edge `1 ⟶ 2` using inverses.
  let hAdj : f₁.left ⟶ h₁.right := eqToHom e0 ≫ h₁.hom
  let g : f₁.right ⟶ h₁.right := inv f₁.hom ≫ hAdj
  let τ : (N (C := C)) _⦋2⦌ := CategoryTheory.ComposableArrows.mk₂ f₁.hom g

  refine ⟨SSet.yonedaEquiv.symm τ, ?_⟩
  apply SSet.horn.hom_ext
  intro j hj
  fin_cases j <;> try (cases hj rfl)
  · -- `j = 1`: long edge `0 ⟶ 2`
    have hτ : (N (C := C)).δ 1 τ = CategoryTheory.ComposableArrows.mk₁ hAdj := by
      -- `δ₁` is the composite edge; simplify `f ≫ inv f`.
      have : (N (C := C)).δ 1 τ = CategoryTheory.ComposableArrows.mk₁ (f₁.hom ≫ g) := by
        simpa [τ] using (CategoryTheory.nerve.δ₁_mk₂_eq (C := C) (f := f₁.hom) (g := g))
      -- simplify the composite
      simpa [g, hAdj, Category.assoc, IsIso.hom_inv_id_assoc] using this
    have hhAdj : CategoryTheory.ComposableArrows.mk₁ hAdj = h₁ := by
      refine CategoryTheory.ComposableArrows.ext₁ (left := e0) (right := rfl) ?_
      simp [hAdj]
    -- Evaluate the filler on this face and compare.
    have hv : (SSet.horn.face (n := 1) (i := (0 : Fin 3)) (j := (1 : Fin 3)) hj) = hFace := by
      apply Subtype.ext
      simp [hFace, horn_face_val]
    -- Both sides are `h₁`, and the RHS computes as `δ₁ τ`.
    -- Left side:
    have hl : σ₀.app _ (SSet.horn.face (n := 1) (i := (0 : Fin 3)) (j := (1 : Fin 3)) hj) = h₁ := by
      simp [h₁, hv]
    -- Right side:
    have hr :
        (Λ[2, (0 : Fin 3)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 1) (i := (0 : Fin 3))
          (j := (1 : Fin 3)) hj) = h₁ := by
      have hRest :
          (Λ[2, (0 : Fin 3)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 1) (i := (0 : Fin 3))
              (j := (1 : Fin 3)) hj) =
            (N (C := C)).δ 1 τ := by
        -- evaluate the filler on the horn face, and identify it with the `δ₁`-face of `τ`
        calc
          (Λ[2, (0 : Fin 3)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 1) (i := (0 : Fin 3))
                (j := (1 : Fin 3)) hj)
              = (SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 1) (i := (0 : Fin 3))
                  (j := (1 : Fin 3)) hj).val := by
                    simp
          _ = (SSet.yonedaEquiv.symm τ).app _ (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3))) := by
                simp [horn_face_val]
          _ = SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm τ) := by
                simpa using
                  (SSet.yonedaEquiv_comp (f := stdSimplex.δ (1 : Fin 3)) (g := SSet.yonedaEquiv.symm τ)).symm
          _ = (N (C := C)).δ 1 τ := by
                -- this is exactly `delta_yonedaEquiv` with `σ = yonedaEquiv.symm τ`
                have := delta_yonedaEquiv (X := N (C := C)) (σ := SSet.yonedaEquiv.symm τ) (j := (1 : Fin 3))
                -- simplify `yonedaEquiv (yonedaEquiv.symm τ)` to `τ`
                simpa using this.symm
      -- finish using the computed face
      exact (hRest.trans hτ).trans hhAdj
    -- Close the face equality without unfolding `Λ[2,0].ι`.
    refine hl.trans ?_
    symm
    exact hr
  · -- `j = 2`: short edge `0 ⟶ 1`
    have hτ : (N (C := C)).δ 2 τ = CategoryTheory.ComposableArrows.mk₁ f₁.hom := by
      simpa [τ] using (CategoryTheory.nerve.δ₂_mk₂_eq (C := C) (f := f₁.hom) (g := g))
    have hf : CategoryTheory.ComposableArrows.mk₁ f₁.hom = f₁ := by
      simpa using
        (CategoryTheory.ComposableArrows.ext₁ (F := CategoryTheory.ComposableArrows.mk₁ f₁.hom) (G := f₁)
          rfl rfl (by simp))
    have hv : (SSet.horn.face (n := 1) (i := (0 : Fin 3)) (j := (2 : Fin 3)) hj) = fFace := by
      apply Subtype.ext
      simp [fFace, horn_face_val]
    have hl : σ₀.app _ (SSet.horn.face (n := 1) (i := (0 : Fin 3)) (j := (2 : Fin 3)) hj) = f₁ := by
      simp [f₁, hv]
    have hr :
        (Λ[2, (0 : Fin 3)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 1) (i := (0 : Fin 3))
          (j := (2 : Fin 3)) hj) = f₁ := by
      have hRest :
          (Λ[2, (0 : Fin 3)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 1) (i := (0 : Fin 3))
              (j := (2 : Fin 3)) hj) =
            (N (C := C)).δ 2 τ := by
        calc
          (Λ[2, (0 : Fin 3)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 1) (i := (0 : Fin 3))
                (j := (2 : Fin 3)) hj)
              = (SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 1) (i := (0 : Fin 3))
                  (j := (2 : Fin 3)) hj).val := by
                    simp
          _ = (SSet.yonedaEquiv.symm τ).app _ (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3))) := by
                simp [horn_face_val]
          _ = SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm τ) := by
                simpa using
                  (SSet.yonedaEquiv_comp (f := stdSimplex.δ (2 : Fin 3)) (g := SSet.yonedaEquiv.symm τ)).symm
          _ = (N (C := C)).δ 2 τ := by
                have := delta_yonedaEquiv (X := N (C := C)) (σ := SSet.yonedaEquiv.symm τ) (j := (2 : Fin 3))
                simpa using this.symm
      exact (hRest.trans hτ).trans hf
    refine hl.trans ?_
    symm
    exact hr

private lemma hornFilling_dim2_outer2
    (σ₀ : (Λ[2, (2 : Fin 3)] : SSet) ⟶ N (C := C)) :
    ∃ σ : (Δ[2] : SSet) ⟶ N (C := C), σ₀ = Λ[2, (2 : Fin 3)].ι ≫ σ := by
  classical
  let gFace : (Λ[2, (2 : Fin 3)] : SSet) _⦋1⦌ :=
    SSet.horn.face (n := 1) (i := (2 : Fin 3)) (j := (0 : Fin 3)) (by decide)
  let hFace : (Λ[2, (2 : Fin 3)] : SSet) _⦋1⦌ :=
    SSet.horn.face (n := 1) (i := (2 : Fin 3)) (j := (1 : Fin 3)) (by decide)
  let g₁ : (N (C := C)) _⦋1⦌ := σ₀.app _ gFace
  let h₁ : (N (C := C)) _⦋1⦌ := σ₀.app _ hFace

  -- Show the two given faces share the same target vertex (vertex `2` in `Δ[2]`).
  have hVertex :
      (Λ[2, (2 : Fin 3)] : SSet).δ (0 : Fin 2) gFace =
        (Λ[2, (2 : Fin 3)] : SSet).δ (0 : Fin 2) hFace := by
    apply Subtype.ext
    change (Δ[2] : SSet).δ (0 : Fin 2) gFace.val =
      (Δ[2] : SSet).δ (0 : Fin 2) hFace.val
    ext k
    fin_cases k
    simp [gFace, hFace, horn_face_val]
    rfl

  have hδ :
      (N (C := C)).δ (0 : Fin 2) g₁ = (N (C := C)).δ (0 : Fin 2) h₁ := by
    calc
      (N (C := C)).δ (0 : Fin 2) g₁
          = σ₀.app _ ((Λ[2, (2 : Fin 3)] : SSet).δ (0 : Fin 2) gFace) := by
            simpa [g₁] using (delta_app (η := σ₀) (i := (0 : Fin 2)) (x := gFace))
      _ = σ₀.app _ ((Λ[2, (2 : Fin 3)] : SSet).δ (0 : Fin 2) hFace) := by
            simp [hVertex]
      _ = (N (C := C)).δ (0 : Fin 2) h₁ := by
            symm
            simpa [h₁] using (delta_app (η := σ₀) (i := (0 : Fin 2)) (x := hFace))

  have e2 : g₁.right = h₁.right := by
    have := congrArg (fun (x : (N (C := C)) _⦋0⦌) => x.obj ⟨0, by decide⟩) hδ
    simpa [CategoryTheory.nerve.δ_obj, g₁, h₁] using this

  -- Construct the missing edge `0 ⟶ 1` using inverses.
  let hAdj : h₁.left ⟶ g₁.right := h₁.hom ≫ eqToHom e2.symm
  let f : h₁.left ⟶ g₁.left := hAdj ≫ inv g₁.hom
  let τ : (N (C := C)) _⦋2⦌ := CategoryTheory.ComposableArrows.mk₂ f g₁.hom

  refine ⟨SSet.yonedaEquiv.symm τ, ?_⟩
  apply SSet.horn.hom_ext
  intro j hj
  fin_cases j <;> try (cases hj rfl)
  · -- `j = 0`: short edge `1 ⟶ 2`
    have hτ : (N (C := C)).δ 0 τ = CategoryTheory.ComposableArrows.mk₁ g₁.hom := by
      simpa [τ] using (CategoryTheory.nerve.δ₀_mk₂_eq (C := C) (f := f) (g := g₁.hom))
    have hg : CategoryTheory.ComposableArrows.mk₁ g₁.hom = g₁ := by
      simpa using
        (CategoryTheory.ComposableArrows.ext₁ (F := CategoryTheory.ComposableArrows.mk₁ g₁.hom) (G := g₁)
          rfl rfl (by simp))
    have hv : (SSet.horn.face (n := 1) (i := (2 : Fin 3)) (j := (0 : Fin 3)) hj) = gFace := by
      apply Subtype.ext
      simp [gFace, horn_face_val]
    have hl : σ₀.app _ (SSet.horn.face (n := 1) (i := (2 : Fin 3)) (j := (0 : Fin 3)) hj) = g₁ := by
      simp [g₁, hv]
    have hr :
        (Λ[2, (2 : Fin 3)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 1) (i := (2 : Fin 3))
          (j := (0 : Fin 3)) hj) = g₁ := by
      have hRest :
          (Λ[2, (2 : Fin 3)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 1) (i := (2 : Fin 3))
              (j := (0 : Fin 3)) hj) =
            (N (C := C)).δ 0 τ := by
        calc
          (Λ[2, (2 : Fin 3)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 1) (i := (2 : Fin 3))
                (j := (0 : Fin 3)) hj)
              = (SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 1) (i := (2 : Fin 3))
                  (j := (0 : Fin 3)) hj).val := by
                    simp
          _ = (SSet.yonedaEquiv.symm τ).app _ (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3))) := by
                simp [horn_face_val]
          _ = SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm τ) := by
                simpa using
                  (SSet.yonedaEquiv_comp (f := stdSimplex.δ (0 : Fin 3)) (g := SSet.yonedaEquiv.symm τ)).symm
          _ = (N (C := C)).δ 0 τ := by
                have := delta_yonedaEquiv (X := N (C := C)) (σ := SSet.yonedaEquiv.symm τ) (j := (0 : Fin 3))
                simpa using this.symm
      exact (hRest.trans hτ).trans hg
    refine hl.trans ?_
    symm
    exact hr
  · -- `j = 1`: long edge `0 ⟶ 2`
    have hτ : (N (C := C)).δ 1 τ = CategoryTheory.ComposableArrows.mk₁ hAdj := by
      have : (N (C := C)).δ 1 τ = CategoryTheory.ComposableArrows.mk₁ (f ≫ g₁.hom) := by
        simpa [τ] using (CategoryTheory.nerve.δ₁_mk₂_eq (C := C) (f := f) (g := g₁.hom))
      -- simplify `(hAdj ≫ inv g) ≫ g`
      simpa [f, hAdj, Category.assoc, IsIso.inv_hom_id_assoc] using this
    have hhAdj : CategoryTheory.ComposableArrows.mk₁ hAdj = h₁ := by
      refine CategoryTheory.ComposableArrows.ext₁ (left := rfl) (right := e2) ?_
      simp [hAdj]
    have hv : (SSet.horn.face (n := 1) (i := (2 : Fin 3)) (j := (1 : Fin 3)) hj) = hFace := by
      apply Subtype.ext
      simp [hFace, horn_face_val]
    have hl : σ₀.app _ (SSet.horn.face (n := 1) (i := (2 : Fin 3)) (j := (1 : Fin 3)) hj) = h₁ := by
      simp [h₁, hv]
    have hr :
        (Λ[2, (2 : Fin 3)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 1) (i := (2 : Fin 3))
          (j := (1 : Fin 3)) hj) = h₁ := by
      have hRest :
          (Λ[2, (2 : Fin 3)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 1) (i := (2 : Fin 3))
              (j := (1 : Fin 3)) hj) =
            (N (C := C)).δ 1 τ := by
        calc
          (Λ[2, (2 : Fin 3)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 1) (i := (2 : Fin 3))
                (j := (1 : Fin 3)) hj)
              = (SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 1) (i := (2 : Fin 3))
                  (j := (1 : Fin 3)) hj).val := by
                    simp
          _ = (SSet.yonedaEquiv.symm τ).app _ (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3))) := by
                simp [horn_face_val]
          _ = SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm τ) := by
                simpa using
                  (SSet.yonedaEquiv_comp (f := stdSimplex.δ (1 : Fin 3)) (g := SSet.yonedaEquiv.symm τ)).symm
          _ = (N (C := C)).δ 1 τ := by
                have := delta_yonedaEquiv (X := N (C := C)) (σ := SSet.yonedaEquiv.symm τ) (j := (1 : Fin 3))
                simpa using this.symm
      exact (hRest.trans hτ).trans hhAdj
    refine hl.trans ?_
    symm
    exact hr

/-!
### Outer 3-horns

For a groupoid, outer 3-horns fill by a cancellation argument:

* `Λ[3,0]`: cancel the invertible edge `0 ⟶ 1` to solve for the missing face `1,2,3`;
* `Λ[3,3]`: cancel the invertible edge `2 ⟶ 3` to solve for the missing face `0,1,2`.
-/

private lemma hornFilling_dim3_outer0
    (σ₀ : (Λ[3, (0 : Fin 4)] : SSet) ⟶ N (C := C)) :
    ∃ σ : (Δ[3] : SSet) ⟶ N (C := C), σ₀ = Λ[3, (0 : Fin 4)].ι ≫ σ := by
  classical
  -- Faces `j = 1,2,3` of the 3-horn.
  let face₁ : (Λ[3, (0 : Fin 4)] : SSet) _⦋2⦌ :=
    SSet.horn.face (n := 2) (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide)
  let face₂ : (Λ[3, (0 : Fin 4)] : SSet) _⦋2⦌ :=
    SSet.horn.face (n := 2) (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  let face₃ : (Λ[3, (0 : Fin 4)] : SSet) _⦋2⦌ :=
    SSet.horn.face (n := 2) (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  let t₁ : (N (C := C)) _⦋2⦌ := σ₀.app _ face₁
  let t₂ : (N (C := C)) _⦋2⦌ := σ₀.app _ face₂
  let t₃ : (N (C := C)) _⦋2⦌ := σ₀.app _ face₃

  -- Edge compatibilities in the horn (all reduced to `Δ[3]` computations).
  have hEdge01 :
      (Λ[3, (0 : Fin 4)] : SSet).δ (2 : Fin 3) face₃ =
        (Λ[3, (0 : Fin 4)] : SSet).δ (2 : Fin 3) face₂ := by
    apply Subtype.ext
    change (Δ[3] : SSet).δ (2 : Fin 3) face₃.val = (Δ[3] : SSet).δ (2 : Fin 3) face₂.val
    have h3 :
        (Δ[3] : SSet).δ (2 : Fin 3) face₃.val =
          SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) := by
      simpa [face₃, horn_face_val] using
        (delta_yonedaEquiv (X := (Δ[3] : SSet)) (σ := stdSimplex.δ (3 : Fin 4)) (j := (2 : Fin 3)))
    have h2 :
        (Δ[3] : SSet).δ (2 : Fin 3) face₂.val =
          SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4)) := by
      simpa [face₂, horn_face_val] using
        (delta_yonedaEquiv (X := (Δ[3] : SSet)) (σ := stdSimplex.δ (2 : Fin 4)) (j := (2 : Fin 3)))
    refine h3.trans ?_
    rw [h2]
    have hδ :
        stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) =
          stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4) := by
      simpa [SSet.stdSimplex, CosimplicialObject.δ] using
        congrArg (fun f => (SSet.stdSimplex).map f)
          (SimplexCategory.δ_comp_δ_self (n := 1) (i := (2 : Fin 3)))
    exact congrArg (fun f => SSet.yonedaEquiv f) hδ.symm

  have hEdge02 :
      (Λ[3, (0 : Fin 4)] : SSet).δ (1 : Fin 3) face₃ =
        (Λ[3, (0 : Fin 4)] : SSet).δ (2 : Fin 3) face₁ := by
    apply Subtype.ext
    change (Δ[3] : SSet).δ (1 : Fin 3) face₃.val = (Δ[3] : SSet).δ (2 : Fin 3) face₁.val
    have h3 :
        (Δ[3] : SSet).δ (1 : Fin 3) face₃.val =
          SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) := by
      simpa [face₃, horn_face_val] using
        (delta_yonedaEquiv (X := (Δ[3] : SSet)) (σ := stdSimplex.δ (3 : Fin 4)) (j := (1 : Fin 3)))
    have h1 :
        (Δ[3] : SSet).δ (2 : Fin 3) face₁.val =
          SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4)) := by
      simpa [face₁, horn_face_val] using
        (delta_yonedaEquiv (X := (Δ[3] : SSet)) (σ := stdSimplex.δ (1 : Fin 4)) (j := (2 : Fin 3)))
    refine h3.trans ?_
    rw [h1]
    have hδ :
        stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4) =
          stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4) := by
      simpa [SSet.stdSimplex, CosimplicialObject.δ] using
        congrArg (fun f => (SSet.stdSimplex).map f)
          (SimplexCategory.δ_comp_δ (n := 1) (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide))
    exact congrArg (fun f => SSet.yonedaEquiv f) hδ

  have hEdge03 :
      (Λ[3, (0 : Fin 4)] : SSet).δ (1 : Fin 3) face₂ =
        (Λ[3, (0 : Fin 4)] : SSet).δ (1 : Fin 3) face₁ := by
    apply Subtype.ext
    change (Δ[3] : SSet).δ (1 : Fin 3) face₂.val = (Δ[3] : SSet).δ (1 : Fin 3) face₁.val
    have h2 :
        (Δ[3] : SSet).δ (1 : Fin 3) face₂.val =
          SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4)) := by
      simpa [face₂, horn_face_val] using
        (delta_yonedaEquiv (X := (Δ[3] : SSet)) (σ := stdSimplex.δ (2 : Fin 4)) (j := (1 : Fin 3)))
    have h1 :
        (Δ[3] : SSet).δ (1 : Fin 3) face₁.val =
          SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4)) := by
      simpa [face₁, horn_face_val] using
        (delta_yonedaEquiv (X := (Δ[3] : SSet)) (σ := stdSimplex.δ (1 : Fin 4)) (j := (1 : Fin 3)))
    refine h2.trans ?_
    rw [h1]
    have hδ :
        stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4) =
          stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) := by
      simpa [SSet.stdSimplex, CosimplicialObject.δ] using
        congrArg (fun f => (SSet.stdSimplex).map f)
          (SimplexCategory.δ_comp_δ_self (n := 1) (i := (1 : Fin 3)))
    exact congrArg (fun f => SSet.yonedaEquiv f) hδ.symm

  -- Transport the horn edge equalities through `σ₀`.
  have e01_eq : (N (C := C)).δ (2 : Fin 3) t₃ = (N (C := C)).δ (2 : Fin 3) t₂ := by
    calc
      (N (C := C)).δ (2 : Fin 3) t₃ =
          σ₀.app _ ((Λ[3, (0 : Fin 4)] : SSet).δ (2 : Fin 3) face₃) := by
            simpa [t₃] using (delta_app (η := σ₀) (i := (2 : Fin 3)) (x := face₃))
      _ = σ₀.app _ ((Λ[3, (0 : Fin 4)] : SSet).δ (2 : Fin 3) face₂) := by
            simp [hEdge01]
      _ = (N (C := C)).δ (2 : Fin 3) t₂ := by
            symm
            simpa [t₂] using (delta_app (η := σ₀) (i := (2 : Fin 3)) (x := face₂))

  have e02_eq : (N (C := C)).δ (1 : Fin 3) t₃ = (N (C := C)).δ (2 : Fin 3) t₁ := by
    calc
      (N (C := C)).δ (1 : Fin 3) t₃ =
          σ₀.app _ ((Λ[3, (0 : Fin 4)] : SSet).δ (1 : Fin 3) face₃) := by
            simpa [t₃] using (delta_app (η := σ₀) (i := (1 : Fin 3)) (x := face₃))
      _ = σ₀.app _ ((Λ[3, (0 : Fin 4)] : SSet).δ (2 : Fin 3) face₁) := by
            simp [hEdge02]
      _ = (N (C := C)).δ (2 : Fin 3) t₁ := by
            symm
            simpa [t₁] using (delta_app (η := σ₀) (i := (2 : Fin 3)) (x := face₁))

  have e03_eq : (N (C := C)).δ (1 : Fin 3) t₂ = (N (C := C)).δ (1 : Fin 3) t₁ := by
    calc
      (N (C := C)).δ (1 : Fin 3) t₂ =
          σ₀.app _ ((Λ[3, (0 : Fin 4)] : SSet).δ (1 : Fin 3) face₂) := by
            simpa [t₂] using (delta_app (η := σ₀) (i := (1 : Fin 3)) (x := face₂))
      _ = σ₀.app _ ((Λ[3, (0 : Fin 4)] : SSet).δ (1 : Fin 3) face₁) := by
            simp [hEdge03]
      _ = (N (C := C)).δ (1 : Fin 3) t₁ := by
            symm
            simpa [t₁] using (delta_app (η := σ₀) (i := (1 : Fin 3)) (x := face₁))

  -- Name the edge 1-simplices in `N`.
  let e01 : (N (C := C)) _⦋1⦌ := (N (C := C)).δ (2 : Fin 3) t₃     -- `0 ⟶ 1`
  let e12 : (N (C := C)) _⦋1⦌ := (N (C := C)).δ (0 : Fin 3) t₃     -- `1 ⟶ 2`
  let e02 : (N (C := C)) _⦋1⦌ := (N (C := C)).δ (1 : Fin 3) t₃     -- `0 ⟶ 2`
  let e13 : (N (C := C)) _⦋1⦌ := (N (C := C)).δ (0 : Fin 3) t₂     -- `1 ⟶ 3`
  let e03 : (N (C := C)) _⦋1⦌ := (N (C := C)).δ (1 : Fin 3) t₂     -- `0 ⟶ 3`
  let e23 : (N (C := C)) _⦋1⦌ := (N (C := C)).δ (0 : Fin 3) t₁     -- `2 ⟶ 3`
  let e02' : (N (C := C)) _⦋1⦌ := (N (C := C)).δ (2 : Fin 3) t₁    -- `0 ⟶ 2`
  let e03' : (N (C := C)) _⦋1⦌ := (N (C := C)).δ (1 : Fin 3) t₁    -- `0 ⟶ 3`

  have he01 : e01 = (N (C := C)).δ (2 : Fin 3) t₂ := by
    simpa [e01] using e01_eq
  have he02 : e02 = e02' := by
    simpa [e02, e02'] using e02_eq
  have he03 : e03 = e03' := by
    simpa [e03, e03'] using e03_eq

  -- Match the vertex `1` between the `(0,1,2)` and `(0,1,3)` faces.
  have eV1 : e12.left = e13.left := by
    have hR : e01.right = ((N (C := C)).δ (2 : Fin 3) t₂).right :=
      congrArg CategoryTheory.ComposableArrows.right he01
    calc
      e12.left = e01.right := by
        simpa [e12, e01] using (delta0_left_eq_delta2_right (C := C) (t := t₃))
      _ = ((N (C := C)).δ (2 : Fin 3) t₂).right := hR
      _ = e13.left := by
        simpa [e13] using (delta0_left_eq_delta2_right (C := C) (t := t₂)).symm

  -- Match the vertex `3` between the `(0,1,3)` and `(0,2,3)` faces.
  have eV3 : e13.right = e23.right := by
    have hR : e03.right = e03'.right :=
      congrArg CategoryTheory.ComposableArrows.right he03
    calc
      e13.right = e03.right := by
        simpa [e03, e13] using (delta1_right_eq_delta0_right (C := C) (t := t₂)).symm
      _ = e03'.right := hR
      _ = e23.right := by
        simpa [e03', e23] using (delta1_right_eq_delta0_right (C := C) (t := t₁))

  -- Match the vertex `2` between the `(0,1,2)` and `(0,2,3)` faces.
  have eV2 : e12.right = e23.left := by
    have hR : e02.right = e02'.right := congrArg CategoryTheory.ComposableArrows.right he02
    -- In any 2-simplex, `right (δ₁) = right (δ₀)` and `right (δ₂) = left (δ₀)` definitionally.
    simpa [e02, e02', e12, e23] using hR

  -- Cast `2 ⟶ 3` to start at the `2` coming from `e12`.
  let h23 : e12.right ⟶ e23.right := eqToHom eV2 ≫ e23.hom

  -- Cancellation yields the needed edge `1 ⟶ 3` (with explicit casts aligning endpoints).
  have h13 :
      e13.hom =
        eqToHom eV1.symm ≫ (e12.hom ≫ h23) ≫ eqToHom eV3.symm := by
    -- long-edge relations in the three given 2-faces
    have ht₃ : e02.hom = e01.hom ≫ e12.hom := by
      simpa [e01, e12, e02] using triangle_rel (C := C) (t := t₃)
    have ht₂ : e03.hom = ((N (C := C)).δ (2 : Fin 3) t₂).hom ≫ e13.hom := by
      simpa [e03, e13] using triangle_rel (C := C) (t := t₂)
    have ht₁ : e03'.hom = e02'.hom ≫ e23.hom := by
      simpa [e03', e02', e23] using triangle_rel (C := C) (t := t₁)

    -- transport shared edges as morphism equalities with `eqToHom` casts
    have he01_hom :
        ((N (C := C)).δ (2 : Fin 3) t₂).hom =
          eqToHom (congrArg CategoryTheory.ComposableArrows.left he01.symm) ≫
            e01.hom ≫
              eqToHom (congrArg CategoryTheory.ComposableArrows.right he01.symm).symm := by
      simpa using (hom_conj_of_eq (C := C) (h := he01.symm))
    have he02_hom :
        e02'.hom =
          eqToHom (congrArg CategoryTheory.ComposableArrows.left he02.symm) ≫
            e02.hom ≫
              eqToHom (congrArg CategoryTheory.ComposableArrows.right he02.symm).symm := by
      simpa using (hom_conj_of_eq (C := C) (h := he02.symm))
    have he03_hom :
        e03'.hom =
          eqToHom (congrArg CategoryTheory.ComposableArrows.left he03.symm) ≫
            e03.hom ≫
              eqToHom (congrArg CategoryTheory.ComposableArrows.right he03.symm).symm := by
      simpa using (hom_conj_of_eq (C := C) (h := he03.symm))

    -- compare two expressions for the long edge `0 ⟶ 3` in the common codomain `e23.right`
    -- and cancel the invertible short edge `0 ⟶ 1` in face `(0,1,3)`.
    have hLong :
        ((N (C := C)).δ (2 : Fin 3) t₂).hom ≫ e13.hom ≫ eqToHom eV3 =
          ((N (C := C)).δ (2 : Fin 3) t₂).hom ≫
            (eqToHom eV1.symm ≫ (e12.hom ≫ h23)) := by
      -- rewrite the LHS using the triangle relation in face `(0,1,3)`
      have hA : ((N (C := C)).δ (2 : Fin 3) t₂).hom ≫ e13.hom ≫ eqToHom eV3 = e03.hom ≫ eqToHom eV3 := by
        simpa [Category.assoc] using congrArg (fun f => f ≫ eqToHom eV3) ht₂.symm

      -- rewrite the RHS using faces `(0,1,2)` and `(0,2,3)` to express the long edge `0 ⟶ 3`
      have hB :
          ((N (C := C)).δ (2 : Fin 3) t₂).hom ≫
              (eqToHom eV1.symm ≫ (e12.hom ≫ h23)) =
            e03.hom ≫ eqToHom eV3 := by
        -- Expand `h23` and reassociate.
        simp [h23]
        -- First transport the short edge `0 ⟶ 1` from face `(0,1,2)` to face `(0,1,3)`,
        -- then use the long-edge relations in the three 2-faces to identify the long edge `0 ⟶ 3`.
        have hV1 : (congrArg CategoryTheory.ComposableArrows.right he01.symm).symm = eV1 := by
          apply Subsingleton.elim
        have hV2 : (congrArg CategoryTheory.ComposableArrows.right he02.symm).symm = eV2 := by
          apply Subsingleton.elim
        have hV3 : (congrArg CategoryTheory.ComposableArrows.right he03.symm).symm = eV3 := by
          apply Subsingleton.elim

        -- Rewrite the LHS via `he01_hom`, cancel the intermediate vertex cast, then use `(0,1,2)`.
        have hL :
            ((N (C := C)).δ (2 : Fin 3) t₂).hom ≫ eqToHom eV1.symm ≫ e12.hom ≫ eqToHom eV2 ≫ e23.hom =
              eqToHom (congrArg CategoryTheory.ComposableArrows.left he01.symm) ≫
                e02.hom ≫ eqToHom eV2 ≫ e23.hom := by
          -- replace `((N).δ₂ t₂).hom` and cancel the cast at vertex `1`
          -- (this is where `hV1` is used to identify the two proofs of the same equality)
          simp [he01_hom, ht₃, Category.assoc]

        -- Transport the long edge `0 ⟶ 2` from face `(0,1,2)` to face `(0,2,3)` and use `(0,2,3)`.
        have hM :
            eqToHom (congrArg CategoryTheory.ComposableArrows.left he01.symm) ≫ e02.hom ≫ eqToHom eV2 ≫ e23.hom =
              (eqToHom (congrArg CategoryTheory.ComposableArrows.left he01.symm) ≫
                  eqToHom (congrArg CategoryTheory.ComposableArrows.left he02.symm).symm) ≫
                e03'.hom := by
          -- first rewrite `e02.hom ≫ eqToHom eV2` using `he02_hom`
          have hE02 :
              e02.hom ≫ eqToHom eV2 =
                eqToHom (congrArg CategoryTheory.ComposableArrows.left he02.symm).symm ≫ e02'.hom := by
            -- `he02_hom` gives `e02'.hom = eqToHom _ ≫ e02.hom ≫ eqToHom eV2`
            -- so we cancel the left cast.
            have := congrArg (fun f => eqToHom (congrArg CategoryTheory.ComposableArrows.left he02.symm).symm ≫ f)
              (by simpa [hV2, Category.assoc] using he02_hom)
            have h' :
                eqToHom (congrArg CategoryTheory.ComposableArrows.left he02.symm).symm ≫ e02'.hom =
                  e02.hom ≫ eqToHom eV2 := by
              simpa [Category.assoc] using this
            exact h'.symm
          -- now use the triangle relation in face `(0,2,3)`
          calc
            eqToHom (congrArg CategoryTheory.ComposableArrows.left he01.symm) ≫ e02.hom ≫ eqToHom eV2 ≫ e23.hom =
                eqToHom (congrArg CategoryTheory.ComposableArrows.left he01.symm) ≫
                  (eqToHom (congrArg CategoryTheory.ComposableArrows.left he02.symm).symm ≫ e02'.hom) ≫ e23.hom := by
                    -- rewrite the middle segment using `hE02`
                    simpa [Category.assoc] using
                      congrArg
                        (fun f =>
                          eqToHom (congrArg CategoryTheory.ComposableArrows.left he01.symm) ≫ f ≫ e23.hom) hE02
            _ = (eqToHom (congrArg CategoryTheory.ComposableArrows.left he01.symm) ≫
                    eqToHom (congrArg CategoryTheory.ComposableArrows.left he02.symm).symm) ≫
                  (e02'.hom ≫ e23.hom) := by
                    simp [Category.assoc]
            _ = (eqToHom (congrArg CategoryTheory.ComposableArrows.left he01.symm) ≫
                    eqToHom (congrArg CategoryTheory.ComposableArrows.left he02.symm).symm) ≫
                  e03'.hom := by
                    simp [ht₁]

        -- Finally transport the shared long edge `0 ⟶ 3` back from face `(0,2,3)` to face `(0,1,3)`.
        have hCast :
            eqToHom (congrArg CategoryTheory.ComposableArrows.left he01.symm) ≫
                eqToHom (congrArg CategoryTheory.ComposableArrows.left he02.symm).symm =
              eqToHom (congrArg CategoryTheory.ComposableArrows.left he03.symm).symm := by
          -- All these are identity morphisms coming from equality of the same vertex `0`.
          -- Reduce to an equality of the underlying object equalities, then use `eqToHom_trans`.
          let p := congrArg CategoryTheory.ComposableArrows.left he01.symm
          let q := (congrArg CategoryTheory.ComposableArrows.left he02.symm).symm
          let r := (congrArg CategoryTheory.ComposableArrows.left he03.symm).symm
          have hpr : p.trans q = r := by
            apply Subsingleton.elim
          calc
            eqToHom p ≫ eqToHom q = eqToHom (p.trans q) := by
              exact eqToHom_trans p q
            _ = eqToHom r := by
              exact congrArg eqToHom hpr
        -- use `he03_hom` to rewrite `e03'.hom` and cancel the left cast via `hCast`
        have hR :
            (eqToHom (congrArg CategoryTheory.ComposableArrows.left he01.symm) ≫
                eqToHom (congrArg CategoryTheory.ComposableArrows.left he02.symm).symm) ≫
              e03'.hom =
                e03.hom ≫ eqToHom eV3 := by
          -- rewrite `e03'.hom` using `he03_hom`, then simplify `eqToHom` compositions.
          -- `hV3` identifies the right-vertex cast with `eV3`.
          simp [he03_hom, hCast]

        -- Put the pieces together.
        calc
          ((N (C := C)).δ (2 : Fin 3) t₂).hom ≫ eqToHom eV1.symm ≫ e12.hom ≫ eqToHom eV2 ≫ e23.hom
              = (eqToHom (congrArg CategoryTheory.ComposableArrows.left he01.symm) ≫
                    eqToHom (congrArg CategoryTheory.ComposableArrows.left he02.symm).symm) ≫ e03'.hom := by
                  simpa [hL] using hM
          _ = e03.hom ≫ eqToHom eV3 := by
                  simpa using hR
      exact hA.trans hB.symm

    -- cancel on the left (invertibility in a groupoid)
    -- then cancel the endpoint casts to isolate `e13.hom`.
    have hMid :
        e13.hom ≫ eqToHom eV3 = eqToHom eV1.symm ≫ (e12.hom ≫ h23) := by
      calc
        e13.hom ≫ eqToHom eV3 =
            inv ((N (C := C)).δ (2 : Fin 3) t₂).hom ≫
              (((N (C := C)).δ (2 : Fin 3) t₂).hom ≫ e13.hom ≫ eqToHom eV3) := by
                simp
        _ = inv ((N (C := C)).δ (2 : Fin 3) t₂).hom ≫
              (((N (C := C)).δ (2 : Fin 3) t₂).hom ≫ (eqToHom eV1.symm ≫ (e12.hom ≫ h23))) := by
                simp [hLong]
        _ = eqToHom eV1.symm ≫ (e12.hom ≫ h23) := by
              simp
    -- postcompose both sides with the inverse cast to move codomain back to `e13.right`.
    simpa [Category.assoc] using congrArg (fun f => f ≫ eqToHom eV3.symm) hMid

  -- Build the filler 3-simplex.
  let τ : (N (C := C)) _⦋3⦌ :=
    CategoryTheory.ComposableArrows.mk₃ e01.hom e12.hom h23

  refine ⟨SSet.yonedaEquiv.symm τ, ?_⟩
  apply SSet.horn.hom_ext
  intro j hj
  fin_cases j <;> try (cases hj rfl)
  · -- `j = 1`: face `(0,2,3)`
    have hτ : (N (C := C)).δ (1 : Fin 4) τ = CategoryTheory.ComposableArrows.mk₂ (e01.hom ≫ e12.hom) h23 := by
      simpa [τ] using (delta₁_mk₃_eq (C := C) (f := e01.hom) (g := e12.hom) (h := h23))
    -- `t₁` is determined by its short edges; match them using `he02` and `eV2`.
    have ht1 : t₁ = CategoryTheory.ComposableArrows.mk₂ e02'.hom e23.hom := by
      simpa [t₁] using (mk2_of_simplex (C := C) (t := t₁))
    have ht1' : t₁ = CategoryTheory.ComposableArrows.mk₂ (e01.hom ≫ e12.hom) h23 := by
      -- Compare the `mk₂` built from the horn data with the target `mk₂`.
      refine ht1.trans ?_
      have h0' : e02.left = e01.left := by
        simpa [e02, e01] using (delta1_left_eq_delta2_left (C := C) (t := t₃))
      let h0 : e02'.left = e01.left :=
        (congrArg CategoryTheory.ComposableArrows.left he02.symm).trans h0'
      let h1 : e23.left = e12.right := congrArg CategoryTheory.ComposableArrows.right he02.symm
      let h2 : e23.right = e23.right := rfl
      refine CategoryTheory.ComposableArrows.ext₂ h0 h1 h2 ?_ ?_
      · -- first short edge: transport `he02` through `hom`, then use the triangle relation in `(0,1,2)`
        -- `simp` computes `map' 0 1` for `mk₂`.
        simp
        -- rewrite `e02'.hom` using `he02` and then `e02.hom` using the face `(0,1,2)`.
        have ht₃' : e02.hom = e01.hom ≫ e12.hom := by
          simpa [e01, e12, e02] using triangle_rel (C := C) (t := t₃)
        have he02_hom' :
            e02'.hom =
              eqToHom (congrArg CategoryTheory.ComposableArrows.left he02.symm) ≫
                e02.hom ≫
                  eqToHom (congrArg CategoryTheory.ComposableArrows.right he02.symm).symm := by
          simpa using (hom_conj_of_eq (C := C) (h := he02.symm))
        simpa [h0, h1, ht₃', Category.assoc] using he02_hom'
      · -- second short edge: this is just the definition of `h23`
        -- `dsimp` computes `map' 1 2` for `mk₂`.
        dsimp [CategoryTheory.ComposableArrows.mk₂, CategoryTheory.ComposableArrows.Precomp.map]
        -- `simp` cancels the inverse vertex casts.
        simp [h23]
    -- finish by comparing face maps
    have hv : (SSet.horn.face (n := 2) (i := (0 : Fin 4)) (j := (1 : Fin 4)) hj) = face₁ := by
      apply Subtype.ext
      simp [face₁, horn_face_val]
    have hl : σ₀.app _ (SSet.horn.face (n := 2) (i := (0 : Fin 4)) (j := (1 : Fin 4)) hj) = t₁ := by
      simp [t₁, hv]
    have hr :
        (Λ[3, (0 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (0 : Fin 4))
          (j := (1 : Fin 4)) hj) = t₁ := by
      -- evaluate on the horn face and identify with `δ₁ τ`
      have hRest :
          (Λ[3, (0 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (0 : Fin 4))
              (j := (1 : Fin 4)) hj) =
            (N (C := C)).δ (1 : Fin 4) τ := by
        calc
          (Λ[3, (0 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (0 : Fin 4))
                (j := (1 : Fin 4)) hj)
              = (SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (0 : Fin 4))
                  (j := (1 : Fin 4)) hj).val := by
                    simp
          _ = (SSet.yonedaEquiv.symm τ).app _ (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 4))) := by
                simp [horn_face_val]
          _ = SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 4) ≫ SSet.yonedaEquiv.symm τ) := by
                simpa using
                  (SSet.yonedaEquiv_comp (f := stdSimplex.δ (1 : Fin 4)) (g := SSet.yonedaEquiv.symm τ)).symm
          _ = (N (C := C)).δ (1 : Fin 4) τ := by
                have := delta_yonedaEquiv (X := N (C := C)) (σ := SSet.yonedaEquiv.symm τ) (j := (1 : Fin 4))
                simpa using this.symm
      -- rewrite the target face to `t₁`
      simpa [hRest, hτ, ht1'] 
    refine hl.trans ?_
    symm
    exact hr
  · -- `j = 2`: face `(0,1,3)`
    have hτ : (N (C := C)).δ (2 : Fin 4) τ = CategoryTheory.ComposableArrows.mk₂ e01.hom (e12.hom ≫ h23) := by
      simpa [τ] using (delta₂_mk₃_eq (C := C) (f := e01.hom) (g := e12.hom) (h := h23))
    -- show `t₂` is the mk₂ with these short edges, using cancellation (`h13`)
    have ht2 : t₂ = CategoryTheory.ComposableArrows.mk₂ ((N (C := C)).δ (2 : Fin 3) t₂).hom e13.hom := by
      simpa [t₂] using (mk2_of_simplex (C := C) (t := t₂))
    have ht2' : t₂ = CategoryTheory.ComposableArrows.mk₂ e01.hom (e12.hom ≫ h23) := by
      refine ht2.trans ?_
      -- Compare the canonical `mk₂` built from the short edges of `t₂` with the target `mk₂`.
      -- This is just endpoint bookkeeping plus the cancellation identity `h13`.
      have h0 : ((N (C := C)).δ (2 : Fin 3) t₂).left = e01.left :=
        congrArg CategoryTheory.ComposableArrows.left he01.symm
      have h1 : e13.left = e12.left := eV1.symm
      have h2 : e13.right = e23.right := eV3
      refine CategoryTheory.ComposableArrows.ext₂ h0 h1 h2 ?_ ?_
      · -- first short edge: transport `he01` through `hom`
        have h1' : (congrArg CategoryTheory.ComposableArrows.right he01.symm).symm = h1.symm := by
          apply Subsingleton.elim
        -- `simp` computes `map' 0 1` for `mk₂`, leaving the conjugation formula from `hom_conj_of_eq`.
        simpa [h0, h1'] using (hom_conj_of_eq (C := C) (h := he01.symm))
      · -- second short edge: this is exactly `h13` (with matching endpoint casts)
        -- `dsimp` computes `map' 1 2` for `mk₂`.
        dsimp [CategoryTheory.ComposableArrows.mk₂, CategoryTheory.ComposableArrows.Precomp.map]
        simpa [h1, h2] using h13
    have hv : (SSet.horn.face (n := 2) (i := (0 : Fin 4)) (j := (2 : Fin 4)) hj) = face₂ := by
      apply Subtype.ext
      simp [face₂, horn_face_val]
    have hl : σ₀.app _ (SSet.horn.face (n := 2) (i := (0 : Fin 4)) (j := (2 : Fin 4)) hj) = t₂ := by
      simp [t₂, hv]
    have hr :
        (Λ[3, (0 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (0 : Fin 4))
          (j := (2 : Fin 4)) hj) = t₂ := by
      have hRest :
          (Λ[3, (0 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (0 : Fin 4))
              (j := (2 : Fin 4)) hj) =
            (N (C := C)).δ (2 : Fin 4) τ := by
        calc
          (Λ[3, (0 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (0 : Fin 4))
                (j := (2 : Fin 4)) hj)
              = (SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (0 : Fin 4))
                  (j := (2 : Fin 4)) hj).val := by
                    simp
          _ = (SSet.yonedaEquiv.symm τ).app _ (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 4))) := by
                simp [horn_face_val]
          _ = SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 4) ≫ SSet.yonedaEquiv.symm τ) := by
                simpa using
                  (SSet.yonedaEquiv_comp (f := stdSimplex.δ (2 : Fin 4)) (g := SSet.yonedaEquiv.symm τ)).symm
          _ = (N (C := C)).δ (2 : Fin 4) τ := by
                have := delta_yonedaEquiv (X := N (C := C)) (σ := SSet.yonedaEquiv.symm τ) (j := (2 : Fin 4))
                simpa using this.symm
      simpa [hRest, hτ, ht2']
    refine hl.trans ?_
    symm
    exact hr
  · -- `j = 3`: face `(0,1,2)`
    have hτ : (N (C := C)).δ (3 : Fin 4) τ = CategoryTheory.ComposableArrows.mk₂ e01.hom e12.hom := by
      simpa [τ] using (delta₃_mk₃_eq (C := C) (f := e01.hom) (g := e12.hom) (h := h23))
    have ht3 : t₃ = CategoryTheory.ComposableArrows.mk₂ ((N (C := C)).δ (2 : Fin 3) t₃).hom e12.hom := by
      simpa [t₃] using (mk2_of_simplex (C := C) (t := t₃))
    have ht3' : t₃ = CategoryTheory.ComposableArrows.mk₂ e01.hom e12.hom := by
      -- rewrite the first short edge to `e01.hom`
      have : ((N (C := C)).δ (2 : Fin 3) t₃).hom = e01.hom := rfl
      simpa [e01, this] using ht3
    have hv : (SSet.horn.face (n := 2) (i := (0 : Fin 4)) (j := (3 : Fin 4)) hj) = face₃ := by
      apply Subtype.ext
      simp [face₃, horn_face_val]
    have hl : σ₀.app _ (SSet.horn.face (n := 2) (i := (0 : Fin 4)) (j := (3 : Fin 4)) hj) = t₃ := by
      simp [t₃, hv]
    have hr :
        (Λ[3, (0 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (0 : Fin 4))
          (j := (3 : Fin 4)) hj) = t₃ := by
      have hRest :
          (Λ[3, (0 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (0 : Fin 4))
              (j := (3 : Fin 4)) hj) =
            (N (C := C)).δ (3 : Fin 4) τ := by
        calc
          (Λ[3, (0 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (0 : Fin 4))
                (j := (3 : Fin 4)) hj)
              = (SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (0 : Fin 4))
                  (j := (3 : Fin 4)) hj).val := by
                    simp
          _ = (SSet.yonedaEquiv.symm τ).app _ (SSet.yonedaEquiv (stdSimplex.δ (3 : Fin 4))) := by
                simp [horn_face_val]
          _ = SSet.yonedaEquiv (stdSimplex.δ (3 : Fin 4) ≫ SSet.yonedaEquiv.symm τ) := by
                simpa using
                  (SSet.yonedaEquiv_comp (f := stdSimplex.δ (3 : Fin 4)) (g := SSet.yonedaEquiv.symm τ)).symm
          _ = (N (C := C)).δ (3 : Fin 4) τ := by
                have := delta_yonedaEquiv (X := N (C := C)) (σ := SSet.yonedaEquiv.symm τ) (j := (3 : Fin 4))
                simpa using this.symm
      simpa [hRest, hτ, ht3']
    refine hl.trans ?_
    symm
    exact hr

-- NOTE: This proof intentionally uses `simpa` and simp argument lists that trigger known linter noise.
-- We disable those linters locally for this lemma to keep the build clean without rewriting the proof.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
private lemma hornFilling_dim3_outer3
    (σ₀ : (Λ[3, (3 : Fin 4)] : SSet) ⟶ N (C := C)) :
    ∃ σ : (Δ[3] : SSet) ⟶ N (C := C), σ₀ = Λ[3, (3 : Fin 4)].ι ≫ σ := by
  classical
  -- Faces `j = 0,1,2` of the 3-horn.
  let face₀ : (Λ[3, (3 : Fin 4)] : SSet) _⦋2⦌ :=
    SSet.horn.face (n := 2) (i := (3 : Fin 4)) (j := (0 : Fin 4)) (by decide)
  let face₁ : (Λ[3, (3 : Fin 4)] : SSet) _⦋2⦌ :=
    SSet.horn.face (n := 2) (i := (3 : Fin 4)) (j := (1 : Fin 4)) (by decide)
  let face₂ : (Λ[3, (3 : Fin 4)] : SSet) _⦋2⦌ :=
    SSet.horn.face (n := 2) (i := (3 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  let t₀ : (N (C := C)) _⦋2⦌ := σ₀.app _ face₀
  let t₁ : (N (C := C)) _⦋2⦌ := σ₀.app _ face₁
  let t₂ : (N (C := C)) _⦋2⦌ := σ₀.app _ face₂

  -- Edge compatibilities in the horn.
  have hEdge23 :
      (Λ[3, (3 : Fin 4)] : SSet).δ (0 : Fin 3) face₀ =
        (Λ[3, (3 : Fin 4)] : SSet).δ (0 : Fin 3) face₁ := by
    apply Subtype.ext
    change (Δ[3] : SSet).δ (0 : Fin 3) face₀.val = (Δ[3] : SSet).δ (0 : Fin 3) face₁.val
    have h0 :
        (Δ[3] : SSet).δ (0 : Fin 3) face₀.val =
          SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4)) := by
      simpa [face₀, horn_face_val] using
        (delta_yonedaEquiv (X := (Δ[3] : SSet)) (σ := stdSimplex.δ (0 : Fin 4)) (j := (0 : Fin 3)))
    have h1 :
        (Δ[3] : SSet).δ (0 : Fin 3) face₁.val =
          SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4)) := by
      simpa [face₁, horn_face_val] using
        (delta_yonedaEquiv (X := (Δ[3] : SSet)) (σ := stdSimplex.δ (1 : Fin 4)) (j := (0 : Fin 3)))
    refine h0.trans ?_
    rw [h1]
    have hδ :
        stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4) =
          stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4) := by
      simpa [SSet.stdSimplex, CosimplicialObject.δ] using
        congrArg (fun f => (SSet.stdSimplex).map f)
          (SimplexCategory.δ_comp_δ_self (n := 1) (i := (0 : Fin 3)))
    exact congrArg (fun f => SSet.yonedaEquiv f) hδ.symm

  have hEdge03 :
      (Λ[3, (3 : Fin 4)] : SSet).δ (1 : Fin 3) face₁ =
        (Λ[3, (3 : Fin 4)] : SSet).δ (1 : Fin 3) face₂ := by
    apply Subtype.ext
    change (Δ[3] : SSet).δ (1 : Fin 3) face₁.val = (Δ[3] : SSet).δ (1 : Fin 3) face₂.val
    have h1 :
        (Δ[3] : SSet).δ (1 : Fin 3) face₁.val =
          SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4)) := by
      simpa [face₁, horn_face_val] using
        (delta_yonedaEquiv (X := (Δ[3] : SSet)) (σ := stdSimplex.δ (1 : Fin 4)) (j := (1 : Fin 3)))
    have h2 :
        (Δ[3] : SSet).δ (1 : Fin 3) face₂.val =
          SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4)) := by
      simpa [face₂, horn_face_val] using
        (delta_yonedaEquiv (X := (Δ[3] : SSet)) (σ := stdSimplex.δ (2 : Fin 4)) (j := (1 : Fin 3)))
    refine h1.trans ?_
    rw [h2]
    have hδ :
        stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4) =
          stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) := by
      simpa [SSet.stdSimplex, CosimplicialObject.δ] using
        congrArg (fun f => (SSet.stdSimplex).map f)
          (SimplexCategory.δ_comp_δ_self (n := 1) (i := (1 : Fin 3)))
    exact congrArg (fun f => SSet.yonedaEquiv f) hδ

  have hEdge13 :
      (Λ[3, (3 : Fin 4)] : SSet).δ (1 : Fin 3) face₀ =
        (Λ[3, (3 : Fin 4)] : SSet).δ (0 : Fin 3) face₂ := by
    apply Subtype.ext
    change (Δ[3] : SSet).δ (1 : Fin 3) face₀.val = (Δ[3] : SSet).δ (0 : Fin 3) face₂.val
    have h0 :
        (Δ[3] : SSet).δ (1 : Fin 3) face₀.val =
          SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4)) := by
      simpa [face₀, horn_face_val] using
        (delta_yonedaEquiv (X := (Δ[3] : SSet)) (σ := stdSimplex.δ (0 : Fin 4)) (j := (1 : Fin 3)))
    have h2 :
        (Δ[3] : SSet).δ (0 : Fin 3) face₂.val =
          SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4)) := by
      simpa [face₂, horn_face_val] using
        (delta_yonedaEquiv (X := (Δ[3] : SSet)) (σ := stdSimplex.δ (2 : Fin 4)) (j := (0 : Fin 3)))
    refine h0.trans ?_
    rw [h2]
    have hδ :
        stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4) =
          stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) := by
      simpa [SSet.stdSimplex, CosimplicialObject.δ] using
        congrArg (fun f => (SSet.stdSimplex).map f)
          (SimplexCategory.δ_comp_δ (n := 1) (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)).symm
    exact congrArg (fun f => SSet.yonedaEquiv f) hδ

  -- Transport through `σ₀`.
  have e23_eq : (N (C := C)).δ (0 : Fin 3) t₀ = (N (C := C)).δ (0 : Fin 3) t₁ := by
    calc
      (N (C := C)).δ (0 : Fin 3) t₀ =
          σ₀.app _ ((Λ[3, (3 : Fin 4)] : SSet).δ (0 : Fin 3) face₀) := by
            simpa [t₀] using (delta_app (η := σ₀) (i := (0 : Fin 3)) (x := face₀))
      _ = σ₀.app _ ((Λ[3, (3 : Fin 4)] : SSet).δ (0 : Fin 3) face₁) := by
            simp [hEdge23]
      _ = (N (C := C)).δ (0 : Fin 3) t₁ := by
            symm
            simpa [t₁] using (delta_app (η := σ₀) (i := (0 : Fin 3)) (x := face₁))

  have e03_eq : (N (C := C)).δ (1 : Fin 3) t₁ = (N (C := C)).δ (1 : Fin 3) t₂ := by
    calc
      (N (C := C)).δ (1 : Fin 3) t₁ =
          σ₀.app _ ((Λ[3, (3 : Fin 4)] : SSet).δ (1 : Fin 3) face₁) := by
            simpa [t₁] using (delta_app (η := σ₀) (i := (1 : Fin 3)) (x := face₁))
      _ = σ₀.app _ ((Λ[3, (3 : Fin 4)] : SSet).δ (1 : Fin 3) face₂) := by
            simp [hEdge03]
      _ = (N (C := C)).δ (1 : Fin 3) t₂ := by
            symm
            simpa [t₂] using (delta_app (η := σ₀) (i := (1 : Fin 3)) (x := face₂))

  have e13_eq : (N (C := C)).δ (1 : Fin 3) t₀ = (N (C := C)).δ (0 : Fin 3) t₂ := by
    calc
      (N (C := C)).δ (1 : Fin 3) t₀ =
          σ₀.app _ ((Λ[3, (3 : Fin 4)] : SSet).δ (1 : Fin 3) face₀) := by
            simpa [t₀] using (delta_app (η := σ₀) (i := (1 : Fin 3)) (x := face₀))
      _ = σ₀.app _ ((Λ[3, (3 : Fin 4)] : SSet).δ (0 : Fin 3) face₂) := by
            simp [hEdge13]
      _ = (N (C := C)).δ (0 : Fin 3) t₂ := by
            symm
            simpa [t₂] using (delta_app (η := σ₀) (i := (0 : Fin 3)) (x := face₂))

  -- Edges in `N`.
  let e23 : (N (C := C)) _⦋1⦌ := (N (C := C)).δ (0 : Fin 3) t₀        -- `2 ⟶ 3`
  let e13 : (N (C := C)) _⦋1⦌ := (N (C := C)).δ (1 : Fin 3) t₀        -- `1 ⟶ 3`
  let e12 : (N (C := C)) _⦋1⦌ := (N (C := C)).δ (2 : Fin 3) t₀        -- `1 ⟶ 2`
  let e03 : (N (C := C)) _⦋1⦌ := (N (C := C)).δ (1 : Fin 3) t₁        -- `0 ⟶ 3`
  let e02 : (N (C := C)) _⦋1⦌ := (N (C := C)).δ (2 : Fin 3) t₁        -- `0 ⟶ 2`
  let e01 : (N (C := C)) _⦋1⦌ := (N (C := C)).δ (2 : Fin 3) t₂        -- `0 ⟶ 1`
  let e23' : (N (C := C)) _⦋1⦌ := (N (C := C)).δ (0 : Fin 3) t₁       -- `2 ⟶ 3`
  let e03' : (N (C := C)) _⦋1⦌ := (N (C := C)).δ (1 : Fin 3) t₂       -- `0 ⟶ 3`
  let e13' : (N (C := C)) _⦋1⦌ := (N (C := C)).δ (0 : Fin 3) t₂       -- `1 ⟶ 3`

  have he23 : e23 = e23' := by
    simpa [e23, e23'] using e23_eq
  have he03 : e03 = e03' := by
    simpa [e03, e03'] using e03_eq
  have he13 : e13 = e13' := by
    simpa [e13, e13'] using e13_eq

  -- Turn shared-edge equalities into morphism equalities with endpoint transports.
  have he23_hom :
      e23'.hom =
        eqToHom (congrArg CategoryTheory.ComposableArrows.left he23.symm) ≫
          e23.hom ≫
            eqToHom (congrArg CategoryTheory.ComposableArrows.right he23.symm).symm := by
    simpa using (hom_conj_of_eq (C := C) (h := he23.symm))
  have he03_hom :
      e03'.hom =
        eqToHom (congrArg CategoryTheory.ComposableArrows.left he03.symm) ≫
          e03.hom ≫
            eqToHom (congrArg CategoryTheory.ComposableArrows.right he03.symm).symm := by
    simpa using (hom_conj_of_eq (C := C) (h := he03.symm))
  have he13_hom :
      e13'.hom =
        eqToHom (congrArg CategoryTheory.ComposableArrows.left he13.symm) ≫
          e13.hom ≫
            eqToHom (congrArg CategoryTheory.ComposableArrows.right he13.symm).symm := by
    simpa using (hom_conj_of_eq (C := C) (h := he13.symm))

  -- Cast `0 ⟶ 2` using the middle vertex match between `e12.right` and `e23.left`.
  have eV2 : e12.right = e23.left := by
    -- In the face `(1,2,3)`, `right (δ₂) = left (δ₀)` definitionally.
    rfl

  -- Vertex identifications across the horn faces.
  have h0 : e02.left = e01.left := by
    calc
      e02.left = e03.left := by
        simpa [e02, e03] using
          (delta1_left_eq_delta2_left (C := C) (t := t₁)).symm
      _ = e03'.left := by
        simpa using congrArg CategoryTheory.ComposableArrows.left he03
      _ = e01.left := by
        simpa [e01, e03'] using
          (delta1_left_eq_delta2_left (C := C) (t := t₂))

  have h1 : e01.right = e12.left := by
    calc
      e01.right = e13'.left := by
        simpa [e01, e13'] using
          (delta0_left_eq_delta2_right (C := C) (t := t₂)).symm
      _ = e13.left := by
        simpa using (congrArg CategoryTheory.ComposableArrows.left he13).symm
      _ = e12.left := by
        simpa [e12, e13] using
          (delta1_left_eq_delta2_left (C := C) (t := t₀))

  have h2 : e12.right = e02.right := by
    calc
      e12.right = e23.left := by
        simpa [e12, e23] using
          (delta0_left_eq_delta2_right (C := C) (t := t₀)).symm
      _ = e23'.left := by
        simpa using congrArg CategoryTheory.ComposableArrows.left he23
      _ = e02.right := by
        simpa [e02, e23'] using
          (delta0_left_eq_delta2_right (C := C) (t := t₁))

  -- Cancellation on the right yields the missing edge `0 ⟶ 2 = (0 ⟶ 1) ≫ (1 ⟶ 2)`,
  -- with explicit endpoint transports making the composition type-correct.
  let comp012 : e02.left ⟶ e02.right :=
    eqToHom h0 ≫ e01.hom ≫ eqToHom h1 ≫ e12.hom ≫ eqToHom h2

  have h02 : e02.hom = comp012 := by
    -- long-edge relations in the three given 2-faces
    have ht₀ : e13.hom = e12.hom ≫ e23.hom := by
      simpa [e12, e23, e13] using triangle_rel (C := C) (t := t₀)
    have ht₁ : e03.hom = e02.hom ≫ e23'.hom := by
      simpa [e03, e02, e23'] using triangle_rel (C := C) (t := t₁)
    have ht₂ : e03'.hom = e01.hom ≫ e13'.hom := by
      simpa [e03', e01, e13'] using triangle_rel (C := C) (t := t₂)

    -- Identify the relevant vertex equalities (proof-irrelevance).
    have h1_eq : congrArg CategoryTheory.ComposableArrows.left he13.symm = h1 := by
      apply Subsingleton.elim
    have h2_eq : congrArg CategoryTheory.ComposableArrows.left he23.symm = h2.symm := by
      apply Subsingleton.elim

    -- Right endpoint transports coming from the shared-edge equalities.
    let r13 : e13'.right = e13.right := congrArg CategoryTheory.ComposableArrows.right he13.symm
    have r23 : e23.right = e23'.right := by
      simpa using (congrArg CategoryTheory.ComposableArrows.right he23.symm).symm

    -- Transport `e23'.hom` so that it can be compared directly to `e23.hom`.
    have h23_transport : eqToHom h2 ≫ e23'.hom = e23.hom ≫ eqToHom r23 := by
      -- rewrite `e23'.hom` via `he23_hom` and cancel the intermediate `eqToHom`s
      calc
        eqToHom h2 ≫ e23'.hom =
            eqToHom h2 ≫
              (eqToHom (congrArg CategoryTheory.ComposableArrows.left he23.symm) ≫
                e23.hom ≫
                  eqToHom (congrArg CategoryTheory.ComposableArrows.right he23.symm).symm) := by
              simp [he23_hom]
        _ = e23.hom ≫ eqToHom r23 := by
              simp

    -- Transport `e13.hom` so that it can be compared directly to `e13'.hom`.
    have h13_transport : eqToHom h1 ≫ e13.hom = e13'.hom ≫ eqToHom r13 := by
      -- postcompose `he13_hom` with the inverse endpoint cast and simplify
      have hA :
          e13'.hom ≫ eqToHom r13 =
            eqToHom (congrArg CategoryTheory.ComposableArrows.left he13.symm) ≫ e13.hom := by
        calc
          e13'.hom ≫ eqToHom r13 =
              (eqToHom (congrArg CategoryTheory.ComposableArrows.left he13.symm) ≫
                  e13.hom ≫
                    eqToHom (congrArg CategoryTheory.ComposableArrows.right he13.symm).symm) ≫
                eqToHom r13 := by
                  simp [he13_hom, Category.assoc]
          _ = eqToHom (congrArg CategoryTheory.ComposableArrows.left he13.symm) ≫ e13.hom := by
                simp [Category.assoc]
      simpa [h1_eq] using hA.symm

    -- Postcompose with `e23'.hom` to compare with the known long edge `e03.hom`.
    have hCompPost : comp012 ≫ e23'.hom = e03.hom := by
      -- expand `comp012` and rewrite the rightmost segment using `h23_transport`
      dsimp [comp012]
      -- align the codomain of `e13.hom` with `e23.right`
      have v13_23 : e13.right = e23.right := by
        simpa [e13, e23] using (delta1_right_eq_delta0_right (C := C) (t := t₀))
      calc
        (eqToHom h0 ≫ e01.hom ≫ eqToHom h1 ≫ e12.hom ≫ eqToHom h2) ≫ e23'.hom
            =
            eqToHom h0 ≫ e01.hom ≫ eqToHom h1 ≫ e12.hom ≫ (eqToHom h2 ≫ e23'.hom) := by
              simp
        _ = eqToHom h0 ≫ e01.hom ≫ eqToHom h1 ≫ e12.hom ≫ (e23.hom ≫ eqToHom r23) := by
              simp [h23_transport]
        _ = eqToHom h0 ≫ e01.hom ≫ eqToHom h1 ≫ e13.hom ≫ eqToHom r23 := by
              simp [Category.assoc, ht₀]
        _ = eqToHom h0 ≫ e01.hom ≫ (eqToHom h1 ≫ e13.hom) ≫ eqToHom v13_23 ≫ eqToHom r23 := by
              simp [Category.assoc]
        _ = eqToHom h0 ≫ e01.hom ≫ (e13'.hom ≫ eqToHom r13) ≫ eqToHom v13_23 ≫ eqToHom r23 := by
              simp [Category.assoc, h13_transport]
        _ = eqToHom h0 ≫ (e01.hom ≫ e13'.hom) ≫ eqToHom r13 ≫ eqToHom v13_23 ≫ eqToHom r23 := by
              simp
        _ = eqToHom h0 ≫ e03'.hom ≫ eqToHom r13 ≫ eqToHom v13_23 ≫ eqToHom r23 := by
              simp [Category.assoc, ht₂]
        _ = eqToHom h0 ≫ e03'.hom ≫ eqToHom (r13.trans (v13_23.trans r23)) := by
              simp [Category.assoc]
        _ = e03.hom := by
              -- the right endpoint cast `r13.trans r23` matches the one coming from `he03.symm`
              have h0_eq : congrArg CategoryTheory.ComposableArrows.left he03.symm = h0.symm := by
                apply Subsingleton.elim
              have hR_eq :
                  congrArg CategoryTheory.ComposableArrows.right he03.symm = r13.trans (v13_23.trans r23) := by
                apply Subsingleton.elim
              simp [he03_hom, Category.assoc]

    -- Cancel on the right (groupoid morphisms are invertible) using `inv e23'.hom`.
    have hPost : e02.hom ≫ e23'.hom = comp012 ≫ e23'.hom := by
      calc
        e02.hom ≫ e23'.hom = e03.hom := by
          simpa [Category.assoc] using ht₁.symm
        _ = comp012 ≫ e23'.hom := by
          simp [hCompPost]

    calc
      e02.hom = (e02.hom ≫ e23'.hom) ≫ inv e23'.hom := by simp [Category.assoc]
      _ = (comp012 ≫ e23'.hom) ≫ inv e23'.hom := by simp [hPost]
      _ = comp012 := by simp [Category.assoc]

  -- Build the filler 3-simplex.
  let τ : (N (C := C)) _⦋3⦌ :=
    CategoryTheory.ComposableArrows.mk₃ (e01.hom ≫ eqToHom h1) e12.hom e23.hom

  refine ⟨SSet.yonedaEquiv.symm τ, ?_⟩
  apply SSet.horn.hom_ext
  intro j hj
  fin_cases j <;> try (cases hj rfl)
  · -- `j = 0`: face `(1,2,3)`
    have hτ : (N (C := C)).δ (0 : Fin 4) τ = CategoryTheory.ComposableArrows.mk₂ e12.hom e23.hom := by
      rfl
    have ht0 : t₀ = CategoryTheory.ComposableArrows.mk₂ e12.hom e23.hom := by
      -- `t₀` is determined by its short edges
      have := mk2_of_simplex (C := C) (t := t₀)
      simpa [e12, e23, e13] using this
    have hv : (SSet.horn.face (n := 2) (i := (3 : Fin 4)) (j := (0 : Fin 4)) hj) = face₀ := by
      apply Subtype.ext
      simp [face₀, horn_face_val]
    have hl : σ₀.app _ (SSet.horn.face (n := 2) (i := (3 : Fin 4)) (j := (0 : Fin 4)) hj) = t₀ := by
      simp [t₀, hv]
    have hr :
        (Λ[3, (3 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (3 : Fin 4))
          (j := (0 : Fin 4)) hj) = t₀ := by
      have hRest :
          (Λ[3, (3 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (3 : Fin 4))
              (j := (0 : Fin 4)) hj) =
            (N (C := C)).δ (0 : Fin 4) τ := by
        calc
          (Λ[3, (3 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (3 : Fin 4))
                (j := (0 : Fin 4)) hj)
              = (SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (3 : Fin 4))
                  (j := (0 : Fin 4)) hj).val := by
                    simp
          _ = (SSet.yonedaEquiv.symm τ).app _ (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 4))) := by
                simp [horn_face_val]
          _ = SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 4) ≫ SSet.yonedaEquiv.symm τ) := by
                simpa using
                  (SSet.yonedaEquiv_comp (f := stdSimplex.δ (0 : Fin 4)) (g := SSet.yonedaEquiv.symm τ)).symm
          _ = (N (C := C)).δ (0 : Fin 4) τ := by
                have := delta_yonedaEquiv (X := N (C := C)) (σ := SSet.yonedaEquiv.symm τ) (j := (0 : Fin 4))
                simpa using this.symm
      simpa [hRest, hτ, ht0]
    refine hl.trans ?_
    symm
    exact hr
  · -- `j = 1`: face `(0,2,3)`
    have hτ :
        (N (C := C)).δ (1 : Fin 4) τ =
          CategoryTheory.ComposableArrows.mk₂ ((e01.hom ≫ eqToHom h1) ≫ e12.hom) e23.hom := by
      simpa [τ, Category.assoc] using
        (delta₁_mk₃_eq (C := C) (f := (e01.hom ≫ eqToHom h1)) (g := e12.hom) (h := e23.hom))
    have ht1 :
        t₁ = CategoryTheory.ComposableArrows.mk₂ ((e01.hom ≫ eqToHom h1) ≫ e12.hom) e23.hom := by
      have := mk2_of_simplex (C := C) (t := t₁)
      refine this.trans ?_

      -- Compare the canonical `mk₂` for face `(0,2,3)` with the one induced by `τ`.
      let h0' : e02.left = e01.left := h0
      let h1' : e02.right = e12.right := h2.symm
      let h2' : e23'.right = e23.right := (congrArg CategoryTheory.ComposableArrows.right he23).symm

      refine CategoryTheory.ComposableArrows.ext₂ h0' h1' h2' ?_ ?_
      · -- first short edge: use the derived long-edge identity `h02`
        simpa [comp012, Category.assoc, h0', h1'] using h02
      · -- second short edge: transport along `he23`
        have hL : congrArg CategoryTheory.ComposableArrows.left he23.symm = h1' := by
          apply Subsingleton.elim
        have hR : congrArg CategoryTheory.ComposableArrows.right he23.symm = h2' := by
          apply Subsingleton.elim
        simpa [hL, hR] using he23_hom
    have hv : (SSet.horn.face (n := 2) (i := (3 : Fin 4)) (j := (1 : Fin 4)) hj) = face₁ := by
      apply Subtype.ext
      simp [face₁, horn_face_val]
    have hl : σ₀.app _ (SSet.horn.face (n := 2) (i := (3 : Fin 4)) (j := (1 : Fin 4)) hj) = t₁ := by
      simp [t₁, hv]
    have hr :
        (Λ[3, (3 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (3 : Fin 4))
          (j := (1 : Fin 4)) hj) = t₁ := by
      calc
        (Λ[3, (3 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (3 : Fin 4))
              (j := (1 : Fin 4)) hj)
            = (N (C := C)).δ (1 : Fin 4) τ := by
                have hRest :
                    (Λ[3, (3 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2)
                        (i := (3 : Fin 4)) (j := (1 : Fin 4)) hj) =
                      (N (C := C)).δ (1 : Fin 4) τ := by
                  calc
                    (Λ[3, (3 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2)
                          (i := (3 : Fin 4)) (j := (1 : Fin 4)) hj)
                        = (SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (3 : Fin 4))
                            (j := (1 : Fin 4)) hj).val := by
                              simp
                    _ = (SSet.yonedaEquiv.symm τ).app _ (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 4))) := by
                          simp [horn_face_val]
                    _ = SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 4) ≫ SSet.yonedaEquiv.symm τ) := by
                          simpa using
                            (SSet.yonedaEquiv_comp (f := stdSimplex.δ (1 : Fin 4)) (g := SSet.yonedaEquiv.symm τ)).symm
                    _ = (N (C := C)).δ (1 : Fin 4) τ := by
                          have := delta_yonedaEquiv (X := N (C := C)) (σ := SSet.yonedaEquiv.symm τ) (j := (1 : Fin 4))
                          simpa using this.symm
                simpa [hRest] using hRest
        _ = CategoryTheory.ComposableArrows.mk₂ ((e01.hom ≫ eqToHom h1) ≫ e12.hom) e23.hom := hτ
        _ = t₁ := ht1.symm
    refine hl.trans ?_
    symm
    exact hr

  · -- `j = 2`: face `(0,1,3)`
    have hτ :
        (N (C := C)).δ (2 : Fin 4) τ =
          CategoryTheory.ComposableArrows.mk₂ (e01.hom ≫ eqToHom h1) (e12.hom ≫ e23.hom) := by
      simpa [τ, Category.assoc] using
        (delta₂_mk₃_eq (C := C) (f := (e01.hom ≫ eqToHom h1)) (g := e12.hom) (h := e23.hom))
    have ht2 : t₂ = CategoryTheory.ComposableArrows.mk₂ (e01.hom ≫ eqToHom h1) (e12.hom ≫ e23.hom) := by
      have ht := mk2_of_simplex (C := C) (t := t₂)
      refine ht.trans ?_

      -- `t₂` is canonically `mk₂ e01.hom e13'.hom`; transport endpoints to match the target.
      let h0' : e01.left = e01.left := rfl
      -- middle vertex equality is exactly h1
      let h1' : e01.right = e12.left := h1
      -- endpoint alignments for the long edge `1 ⟶ 3`
      have hL0 : e13'.left = e01.right := by
        simpa [e13', e01] using (delta0_left_eq_delta2_right (C := C) (t := t₂))
      have hL1 : e13.left = e12.left := by
        simpa [e13, e12] using (delta1_left_eq_delta2_left (C := C) (t := t₀))
      have hR0 : e13'.right = e13.right := congrArg CategoryTheory.ComposableArrows.right he13.symm
      have hR1 : e13.right = e23.right := by
        simpa [e13, e23] using (delta1_right_eq_delta0_right (C := C) (t := t₀))
      let h2' : e13'.right = e23.right := hR0.trans hR1

      refine CategoryTheory.ComposableArrows.ext₂ h0' h1 h2' ?_ ?_
      · -- first short edge: insert the middle vertex cast
        -- definitional: the `0 ⟶ 1` edge of `t₂` is exactly `e01.hom`
        simp [e01] -- no casts needed
      · -- second short edge: compare `e13'.hom` with `e12.hom ≫ e23.hom`
        -- rewrite the long edge using the face compatibility `he13`
        have hL : congrArg CategoryTheory.ComposableArrows.left he13.symm = h1 := by
          apply Subsingleton.elim
        have hR : congrArg CategoryTheory.ComposableArrows.right he13.symm = hR0 := by
          apply Subsingleton.elim
        have he13_hom' :
            e13'.hom =
              eqToHom h1 ≫ e13.hom ≫ eqToHom hR0.symm := by
          simpa [hL, hR] using (hom_conj_of_eq (C := C) (h := he13.symm))
        -- long edge in face (1,2,3)
        have ht₀ : e13.hom = e12.hom ≫ e23.hom := by
          simpa [e12, e23, e13] using triangle_rel (C := C) (t := t₀)
        -- combine the two rewrites
        have he13_hom'' :
            e13'.hom =
              eqToHom h1 ≫ (e12.hom ≫ e23.hom) ≫ eqToHom hR0.symm := by
          simpa [Category.assoc, ht₀] using he13_hom'
        -- simplify the goal to match `he13_hom''`
        dsimp [CategoryTheory.ComposableArrows.Precomp.map]
        -- `h2'` is definitionally `hR0.trans hR1`, so casts align after `simp`
        simpa [h2', hR1, hR0, Category.assoc, eqToHom_trans] using he13_hom''
    have hv : (SSet.horn.face (n := 2) (i := (3 : Fin 4)) (j := (2 : Fin 4)) hj) = face₂ := by
      apply Subtype.ext
      simp [face₂, horn_face_val]
    have hl : σ₀.app _ (SSet.horn.face (n := 2) (i := (3 : Fin 4)) (j := (2 : Fin 4)) hj) = t₂ := by
      simp [t₂, hv]
    have hr :
        (Λ[3, (3 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (3 : Fin 4))
          (j := (2 : Fin 4)) hj) = t₂ := by
      have hRest :
          (Λ[3, (3 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (3 : Fin 4))
              (j := (2 : Fin 4)) hj) =
            (N (C := C)).δ (2 : Fin 4) τ := by
        calc
          (Λ[3, (3 : Fin 4)].ι ≫ SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (3 : Fin 4))
                (j := (2 : Fin 4)) hj)
              = (SSet.yonedaEquiv.symm τ).app _ (SSet.horn.face (n := 2) (i := (3 : Fin 4))
                  (j := (2 : Fin 4)) hj).val := by
                    simp
          _ = (SSet.yonedaEquiv.symm τ).app _ (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 4))) := by
                simp [horn_face_val]
          _ = SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 4) ≫ SSet.yonedaEquiv.symm τ) := by
                simpa using
                  (SSet.yonedaEquiv_comp (f := stdSimplex.δ (2 : Fin 4)) (g := SSet.yonedaEquiv.symm τ)).symm
          _ = (N (C := C)).δ (2 : Fin 4) τ := by
                have := delta_yonedaEquiv (X := N (C := C)) (σ := SSet.yonedaEquiv.symm τ) (j := (2 : Fin 4))
                simpa using this.symm
      simpa [hRest, hτ, ht2]
    refine hl.trans ?_
    symm
    exact hr

set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true

/-- Every horn in the nerve of a groupoid admits a filler. -/
private lemma nerve_hornFilling
    {n : ℕ} {i : Fin (n + 2)} (σ₀ : (Λ[n + 1, i] : SSet) ⟶ N (C := C)) :
    ∃ σ : (Δ[n + 1] : SSet) ⟶ N (C := C), σ₀ = Λ[n + 1, i].ι ≫ σ := by
  cases n with
  | zero =>
      simpa using hornFilling_dim1 (C := C) i σ₀
  | succ n =>
      cases n with
      | zero =>
          fin_cases i
          · simpa using hornFilling_dim2_outer0 (C := C) σ₀
          · exact SSet.Quasicategory.hornFilling (S := N (C := C))
              (i := (1 : Fin 3)) (by decide) (by decide) σ₀
          · simpa using hornFilling_dim2_outer2 (C := C) σ₀
      | succ n =>
          cases n with
          | zero =>
              fin_cases i
              · simpa using hornFilling_dim3_outer0 (C := C) σ₀
              · exact SSet.Quasicategory.hornFilling (S := N (C := C))
                  (i := (1 : Fin 4)) (by decide) (by decide) σ₀
              · exact SSet.Quasicategory.hornFilling (S := N (C := C))
                  (i := (2 : Fin 4)) (by decide) (by decide) σ₀
              · simpa using hornFilling_dim3_outer3 (C := C) σ₀
          | succ n =>
              simpa using
                hornFilling_ge4_of_isCoskeletal (X := N (C := C))
                  (n := n + 2) i (by omega) σ₀

/-- The nerve of a groupoid is a Kan complex. -/
theorem nerve_kanComplex_of_groupoid :
    SSet.KanComplex (CategoryTheory.nerve C) := by
  change HomotopicalAlgebra.IsFibrant (CategoryTheory.nerve C)
  change HomotopicalAlgebra.Fibration (terminal.from (CategoryTheory.nerve C))
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B g hg
  simp only [SSet.modelCategoryQuillen.J, CategoryTheory.MorphismProperty.iSup_iff,
    CategoryTheory.MorphismProperty.ofHoms_iff] at hg
  obtain ⟨n, i, hg⟩ := hg
  have hHorn :
      HasLiftingProperty (Λ[n + 1, i].ι) (terminal.from (CategoryTheory.nerve C)) := by
    refine ⟨fun {f} {b} sq => ?_⟩
    obtain ⟨σ, hσ⟩ := nerve_hornFilling (C := C) (i := i) f
    exact CommSq.HasLift.mk'
      { l := σ
        fac_left := hσ.symm
        fac_right := by
          simpa using (Subsingleton.elim (σ ≫ terminal.from (CategoryTheory.nerve C)) b) }
  letI : HasLiftingProperty (Λ[n + 1, i].ι) (terminal.from (CategoryTheory.nerve C)) := hHorn
  exact HasLiftingProperty.of_arrow_iso_left
    (i := Λ[n + 1, i].ι) (i' := g) (p := terminal.from (CategoryTheory.nerve C))
    (e := eqToIso hg.symm)

instance instKanComplexNerveGroupoid :
    SSet.KanComplex (CategoryTheory.nerve C) :=
  nerve_kanComplex_of_groupoid (C := C)

end NerveKan

/-- Universe-polymorphic export of the nerve Kan-complex theorem.
    The section-local `nerve_kanComplex_of_groupoid` binds universe variables `u v` from
    the enclosing `section NerveKan`; downstream files that declare only `universe u`
    cannot resolve it directly.  This wrapper lives outside the section so Lean
    can unify universe parameters during elaboration. -/
theorem exported_groupoid_nerve_kanComplex {C : Type u} [CategoryTheory.Groupoid.{v} C] :
    SSet.KanComplex (CategoryTheory.nerve C) := by
  simpa using (nerve_kanComplex_of_groupoid (C := C))

end InfinityGroupoid
end Combinators
end LoF
end HeytingLean
