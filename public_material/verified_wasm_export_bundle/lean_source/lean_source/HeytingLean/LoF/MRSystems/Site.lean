import HeytingLean.LoF.Combinators.Topos.SieveNucleus
import HeytingLean.LoF.MRSystems.Nucleus

import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Closed

/-!
# (M,R) selector site (Phase E.1): a non-discrete Grothendieck topology modeling the selector nucleus

This file defines a tiny **star-shaped** preorder category:

- a hub object `⋆`,
- one leaf object for each selector `Φ : Selector S`,

and equips it with a Grothendieck topology `J` such that on sieves over the hub,
`J.close` behaves like adjoining the **non-closed core** of selectors.

Objectivity boundary:
this is a *site-theoretic* representation of the discrete nucleus from `MRSystems/Nucleus.lean`.
It does not claim a SKY connection.
-/

namespace HeytingLean
namespace LoF
namespace MRSystems

open scoped Classical

open CategoryTheory
open HeytingLean.ClosingTheLoop.MR

universe u v

variable {S : MRSystem.{u, v}} {b : S.B} (RI : RightInverseAt S b)

namespace SelectorSite

/-! ## The star preorder category -/

/-- Objects: `none` is the hub, `some Φ` is a leaf for selector `Φ`. -/
abbrev Obj : Type _ :=
  Option (Selector S)

abbrev hub : Obj (S := S) := none
abbrev leaf (Φ : Selector S) : Obj (S := S) := some Φ

/-- Star-shaped preorder: every object maps to the hub, and leaves only map to themselves/hub. -/
instance : Preorder (Obj (S := S)) where
  le x y := y = none ∨ x = y
  le_refl x := Or.inr rfl
  le_trans x y z hxy hyz := by
    rcases hyz with hz | rfl
    · exact Or.inl hz
    · rcases hxy with hy | rfl
      · exact Or.inl (by simpa using hy)
      · exact Or.inr rfl

/-- The canonical arrow from a leaf into the hub. -/
def leafHom (Φ : Selector S) : leaf (S := S) Φ ⟶ hub (S := S) :=
  CategoryTheory.homOfLE (Or.inl rfl)

/-! ## The Grothendieck topology -/

/-- Covering sieves for the selector site.

Intuition:
- on a non-closed leaf `Φ`, **every** sieve covers (including the empty one), so hub-sieves
  automatically cover the leaf-arrow `Φ ⟶ ⋆`;
- on a closed leaf `Φ`, only `⊤` covers, so hub-sieves cover the leaf-arrow iff they *contain* it;
- on the hub, a sieve covers iff it contains every **closed** leaf-arrow.

The hub coverage condition is chosen so that transitivity holds despite non-closed leaves being
chaotic: it is generally impossible to recover membership of a non-closed leaf-arrow from
pullback-covering alone. -/
def cover : ∀ X : Obj (S := S), Set (Sieve X) :=
  fun X =>
    match X with
    | none =>
        {T : Sieve (hub (S := S)) | ∀ Φ, IsClosed S b RI Φ → T (leafHom (S := S) Φ)}
    | some Φ =>
        if Φ ∈ nonClosedCore (S := S) (b := b) RI then Set.univ else {⊤}

def topology : GrothendieckTopology (Obj (S := S)) := by
  classical
  refine
    { sieves := cover (S := S) (b := b) RI
      top_mem' := ?_
      pullback_stable' := ?_
      transitive' := ?_ }
  · intro X
    cases X with
    | none =>
        intro Φ _hΦ
        trivial
    | some Φ =>
        simp [cover]
  · intro X Y T f hT
    cases X with
    | none =>
        -- Pulling back a hub-covering sieve.
        cases Y with
        | none =>
            -- `hub ⟶ hub` is subsingleton, hence `f = 𝟙`.
            have hf : f = 𝟙 (hub (S := S)) := Subsingleton.elim _ _
            subst hf
            simpa [cover] using hT
        | some Φ =>
            -- Pullback along the leaf-arrow.
            by_cases hNC : Φ ∈ nonClosedCore (S := S) (b := b) RI
            · -- Non-closed leaf: all sieves cover.
              -- `simp` presents this as `IsClosed Φ → ...`; discharge by contradiction using `hNC`.
              -- (Equivalently: `cover (some Φ) = Set.univ` so membership is trivial.)
              have : IsClosed S b RI Φ → T.pullback f = (⊤ : Sieve (leaf (S := S) Φ)) := by
                intro hClosed
                exfalso
                exact (mem_nonClosedCore_iff (S := S) (b := b) (RI := RI) Φ).1 hNC hClosed
              simpa [cover] using this
            · -- Closed leaf: need the pullback to be `⊤`.
              have hClosed : IsClosed S b RI Φ := by
                by_contra h
                exact hNC ((mem_nonClosedCore_iff (S := S) (b := b) (RI := RI) Φ).2 h)
              have hmem : T (leafHom (S := S) Φ) := hT Φ hClosed
              have hf : f = leafHom (S := S) Φ := Subsingleton.elim _ _
              subst hf
              have hpb : T.pullback (leafHom (S := S) Φ) = (⊤ : Sieve (leaf (S := S) Φ)) :=
                Sieve.pullback_eq_top_of_mem T hmem
              simp [cover, hpb]
    | some ΦX =>
        -- Pulling back a leaf-covering sieve: only possible along identities.
        cases Y with
        | none =>
            -- No arrows from the hub to a leaf.
            have hle : (hub (S := S) : Obj (S := S)) ≤ leaf (S := S) ΦX := f.le
            rcases hle with h | h
            · cases h
            · cases h
        | some ΦY =>
            have hle : (leaf (S := S) ΦY : Obj (S := S)) ≤ leaf (S := S) ΦX := f.le
            have hEq : ΦY = ΦX := by
              rcases hle with h | h
              · cases h
              · simpa using Option.some.inj h
            subst hEq
            have hf : f = 𝟙 (leaf (S := S) ΦY) := Subsingleton.elim _ _
            subst hf
            simpa using hT
  · intro X T hT R hR
    cases X with
    | none =>
        -- Transitivity on the hub: it suffices to recover all closed leaf arrows into `R`.
        intro Φ hClosed
        have hTf : T (leafHom (S := S) Φ) := hT Φ hClosed
        have hRpb :
            R.pullback (leafHom (S := S) Φ) ∈ cover (S := S) (b := b) RI (leaf (S := S) Φ) :=
          hR hTf
        have hImp : IsClosed S b RI Φ →
            R.pullback (leafHom (S := S) Φ) = (⊤ : Sieve (leaf (S := S) Φ)) := by
          simpa [cover] using hRpb
        exact (Sieve.mem_iff_pullback_eq_top (S := R) (leafHom (S := S) Φ)).2 (hImp hClosed)
    | some ΦX =>
        by_cases hNC : ΦX ∈ nonClosedCore (S := S) (b := b) RI
        · -- Non-closed leaf: all sieves cover.
          have : IsClosed S b RI ΦX → R = (⊤ : Sieve (leaf (S := S) ΦX)) := by
            intro hClosed
            exfalso
            exact (mem_nonClosedCore_iff (S := S) (b := b) (RI := RI) ΦX).1 hNC hClosed
          simpa [cover] using this
        · -- Closed leaf: covering sieves are exactly `⊤`.
          have hEqT : T = (⊤ : Sieve (leaf (S := S) ΦX)) := by
            have hImp : IsClosed S b RI ΦX → T = (⊤ : Sieve (leaf (S := S) ΦX)) := by
              simpa [cover] using hT
            have hClosed : IsClosed S b RI ΦX := by
              by_contra h
              exact hNC ((mem_nonClosedCore_iff (S := S) (b := b) (RI := RI) ΦX).2 h)
            exact hImp hClosed
          subst hEqT
          have hRid :
              R.pullback (𝟙 (leaf (S := S) ΦX)) ∈
                cover (S := S) (b := b) RI (leaf (S := S) ΦX) :=
            hR (Y := leaf (S := S) ΦX) (f := 𝟙 (leaf (S := S) ΦX)) (by trivial)
          have hImp : IsClosed S b RI ΦX → R.pullback (𝟙 (leaf (S := S) ΦX)) =
              (⊤ : Sieve (leaf (S := S) ΦX)) := by
            simpa [cover] using hRid
          have hTop : R.pullback (𝟙 (leaf (S := S) ΦX)) = (⊤ : Sieve (leaf (S := S) ΦX)) := by
            have hClosed : IsClosed S b RI ΦX := by
              by_contra h
              exact hNC ((mem_nonClosedCore_iff (S := S) (b := b) (RI := RI) ΦX).2 h)
            exact hImp hClosed
          -- `pullback_id` reduces this to `R = ⊤`.
          have : R = (⊤ : Sieve (leaf (S := S) ΦX)) := by
            simpa [Sieve.pullback_id] using hTop
          have hClosed : IsClosed S b RI ΦX := by
            by_contra h
            exact hNC ((mem_nonClosedCore_iff (S := S) (b := b) (RI := RI) ΦX).2 h)
          have hImp' : IsClosed S b RI ΦX → R = (⊤ : Sieve (leaf (S := S) ΦX)) := by
            intro _h
            exact this
          -- Convert the implication-style presentation back into membership in `{⊤}`.
          have : R ∈ cover (S := S) (b := b) RI (leaf (S := S) ΦX) := by
            simpa [cover] using hImp'
          exact this

/-! ## Closure computations on the hub -/

abbrev Hub : Obj (S := S) := hub (S := S)

/-- On a leaf object, membership in the topology is the implication form
`IsClosed Φ → P = ⊤` (so non-closed leaves are “chaotic”). -/
theorem mem_topology_leaf_iff (Φ : Selector S) (P : Sieve (leaf (S := S) Φ)) :
    P ∈ (topology (S := S) (b := b) RI) (leaf (S := S) Φ) ↔
      IsClosed S b RI Φ → P = (⊤ : Sieve (leaf (S := S) Φ)) := by
  -- Unfold `topology` at a leaf: membership depends only on whether `Φ` is closed.
  change P ∈ cover (S := S) (b := b) RI (leaf (S := S) Φ) ↔ _
  dsimp [cover]
  by_cases hNC : Φ ∈ nonClosedCore (S := S) (b := b) RI
  · -- Non-closed leaf: all sieves cover.
    constructor
    · intro _hP hClosed
      exfalso
      exact (mem_nonClosedCore_iff (S := S) (b := b) (RI := RI) Φ).1 hNC hClosed
    · intro _h
      simp [hNC]
  · -- Closed leaf: only `⊤` covers.
    have hClosed : IsClosed S b RI Φ := by
      by_contra h
      exact hNC ((mem_nonClosedCore_iff (S := S) (b := b) (RI := RI) Φ).2 h)
    constructor
    · intro hP
      have hEq : P = (⊤ : Sieve (leaf (S := S) Φ)) := by
        simpa [hNC] using hP
      intro _h
      exact hEq
    · intro hImp
      have hEq : P = (⊤ : Sieve (leaf (S := S) Φ)) := hImp hClosed
      simp [hNC, hEq]

/-- The closure `J.close` on hub sieves adds the non-closed core on leaf arrows. -/
theorem close_leafHom_iff (T : Sieve (Hub (S := S))) (Φ : Selector S) :
    (topology (S := S) (b := b) RI).close T (leafHom (S := S) Φ) ↔
      Φ ∈ nonClosedCore (S := S) (b := b) RI ∨ T (leafHom (S := S) Φ) := by
  classical
  by_cases hClosed : IsClosed S b RI Φ
  · have hnot : ¬ Φ ∈ nonClosedCore (S := S) (b := b) RI := by
      intro hMem
      exact (mem_nonClosedCore_iff (S := S) (b := b) (RI := RI) Φ).1 hMem hClosed
    have hL :
        (topology (S := S) (b := b) RI).close T (leafHom (S := S) Φ) ↔
          T (leafHom (S := S) Φ) := by
      change (topology (S := S) (b := b) RI).Covers T (leafHom (S := S) Φ) ↔ _
      change T.pullback (leafHom (S := S) Φ) ∈ (topology (S := S) (b := b) RI) (leaf (S := S) Φ) ↔ _
      have hCover :
          T.pullback (leafHom (S := S) Φ) ∈ (topology (S := S) (b := b) RI) (leaf (S := S) Φ) ↔
            T.pullback (leafHom (S := S) Φ) = (⊤ : Sieve (leaf (S := S) Φ)) := by
        constructor
        · intro hMem
          have hImp : IsClosed S b RI Φ → T.pullback (leafHom (S := S) Φ) =
                (⊤ : Sieve (leaf (S := S) Φ)) :=
            (mem_topology_leaf_iff (S := S) (b := b) (RI := RI) Φ (P := T.pullback (leafHom (S := S) Φ))).1 hMem
          exact hImp hClosed
        · intro hEq
          have hImp : IsClosed S b RI Φ → T.pullback (leafHom (S := S) Φ) =
                (⊤ : Sieve (leaf (S := S) Φ)) := fun _ => hEq
          exact
            (mem_topology_leaf_iff (S := S) (b := b) (RI := RI) Φ (P := T.pullback (leafHom (S := S) Φ))).2 hImp
      -- Reduce to `T.pullback f = ⊤ ↔ T f`.
      rw [hCover]
      simpa using (Sieve.mem_iff_pullback_eq_top (S := T) (leafHom (S := S) Φ)).symm
    -- With `hnot`, the RHS is just `T (leafHom Φ)`.
    simpa [hnot] using hL
  · have hMem : Φ ∈ nonClosedCore (S := S) (b := b) RI :=
      (mem_nonClosedCore_iff (S := S) (b := b) (RI := RI) Φ).2 hClosed
    have hL :
        (topology (S := S) (b := b) RI).close T (leafHom (S := S) Φ) := by
      change (topology (S := S) (b := b) RI).Covers T (leafHom (S := S) Φ)
      change T.pullback (leafHom (S := S) Φ) ∈ (topology (S := S) (b := b) RI) (leaf (S := S) Φ)
      have hImp : IsClosed S b RI Φ → T.pullback (leafHom (S := S) Φ) =
            (⊤ : Sieve (leaf (S := S) Φ)) := by
        intro hC
        exfalso
        exact (mem_nonClosedCore_iff (S := S) (b := b) (RI := RI) Φ).1 hMem hC
      exact
        (mem_topology_leaf_iff (S := S) (b := b) (RI := RI) Φ (P := T.pullback (leafHom (S := S) Φ))).2 hImp
    exact ⟨fun _ => Or.inl hMem, fun _ => hL⟩

/-! ## From selector predicates to closed sieves (and back) -/

/-- A subset of selectors determines a sieve on the hub:
include the leaf-arrow `Φ ⟶ ⋆` iff `Φ ∈ U`, and include `𝟙 ⋆` iff `U = Set.univ`. -/
def hubSieveOfSet (U : Set (Selector S)) : Sieve (Hub (S := S)) where
  arrows := by
    intro Y _f
    cases Y with
    | none => exact U = Set.univ
    | some Φ => exact Φ ∈ U
  downward_closed := by
    intro Y Z f hf g
    cases Y with
    | none =>
        -- `hf : U = univ`; all arrows into the hub are then included.
        cases Z with
        | none =>
            exact hf
        | some Φ =>
            simp [hf]
    | some Φ =>
        -- Leaf case: the only maps into a leaf are identities.
        cases Z with
        | none =>
            have hle : (hub (S := S) : Obj (S := S)) ≤ leaf (S := S) Φ := g.le
            rcases hle with h | h
            · cases h
            · cases h
        | some Ψ =>
            have hle : (leaf (S := S) Ψ : Obj (S := S)) ≤ leaf (S := S) Φ := g.le
            rcases hle with h | h
            · cases h
            · have : Ψ = Φ := Option.some.inj h
              subst this
              exact hf

@[simp] theorem hubSieveOfSet_leafHom (U : Set (Selector S)) (Φ : Selector S) :
    hubSieveOfSet (S := S) (U := U) (leafHom (S := S) Φ) ↔ Φ ∈ U := by
  rfl

@[simp] theorem hubSieveOfSet_id (U : Set (Selector S)) :
    hubSieveOfSet (S := S) (U := U) (𝟙 (Hub (S := S))) ↔ U = Set.univ := by
  rfl

/-- Extract the subset of selectors represented by a hub sieve. -/
def leafSet (T : Sieve (Hub (S := S))) : Set (Selector S) :=
  {Φ | T (leafHom (S := S) Φ)}

@[simp] theorem leafSet_hubSieveOfSet (U : Set (Selector S)) :
    leafSet (S := S) (T := hubSieveOfSet (S := S) (U := U)) = U := by
  ext Φ
  simp [leafSet]

/-- In any `J`-closed hub sieve, all non-closed selectors must be included. -/
theorem core_subset_leafSet_of_isClosed (T : Sieve (Hub (S := S)))
    (hT : (topology (S := S) (b := b) RI).IsClosed T) :
    nonClosedCore (S := S) (b := b) RI ⊆ leafSet (S := S) (T := T) := by
  intro Φ hΦ
  -- Show `T` covers the leaf arrow (chaotic leaf), hence contains it by closedness.
  have hImp :
      IsClosed S b RI Φ → T.pullback (leafHom (S := S) Φ) = (⊤ : Sieve (leaf (S := S) Φ)) := by
    intro hC
    exfalso
    exact (mem_nonClosedCore_iff (S := S) (b := b) (RI := RI) Φ).1 hΦ hC
  have hCover :
      T.pullback (leafHom (S := S) Φ) ∈ (topology (S := S) (b := b) RI) (leaf (S := S) Φ) :=
    (mem_topology_leaf_iff (S := S) (b := b) (RI := RI) Φ (P := T.pullback (leafHom (S := S) Φ))).2 hImp
  have : T (leafHom (S := S) Φ) :=
    hT (leafHom (S := S) Φ) hCover
  simpa [leafSet] using this

/-- If a set of selectors contains the non-closed core, its hub sieve is `J`-closed. -/
theorem isClosed_hubSieveOfSet_of_core_subset (U : Set (Selector S))
    (hU : nonClosedCore (S := S) (b := b) RI ⊆ U) :
    (topology (S := S) (b := b) RI).IsClosed (hubSieveOfSet (S := S) (U := U)) := by
  intro Y f hf
  cases Y with
  | none =>
      have hf' : f = 𝟙 (Hub (S := S)) := Subsingleton.elim _ _
      subst hf'
      -- If the hub identity is covered, then all closed leaf arrows are present, hence `U = univ`.
      have hCoverHub :
          hubSieveOfSet (S := S) (U := U) ∈ (topology (S := S) (b := b) RI) (Hub (S := S)) :=
        ((topology (S := S) (b := b) RI).covering_iff_covers_id (S := hubSieveOfSet (S := S) (U := U))
              (X := Hub (S := S))).2 hf
      have hAllClosed :
          ∀ Φ, IsClosed S b RI Φ → Φ ∈ U := by
        have hAll :
            ∀ Φ, IsClosed S b RI Φ → hubSieveOfSet (S := S) (U := U) (leafHom (S := S) Φ) := by
          -- Unfold hub coverages.
          change hubSieveOfSet (S := S) (U := U) ∈ cover (S := S) (b := b) RI (Hub (S := S)) at hCoverHub
          simpa [cover] using hCoverHub
        intro Φ hΦ
        have : hubSieveOfSet (S := S) (U := U) (leafHom (S := S) Φ) := hAll Φ hΦ
        simpa using this
      have hUniv : U = Set.univ := by
        ext Φ
        constructor
        · intro _h
          trivial
        · intro _h
          by_cases hΦ : IsClosed S b RI Φ
          · exact hAllClosed Φ hΦ
          · have : Φ ∈ nonClosedCore (S := S) (b := b) RI :=
              (mem_nonClosedCore_iff (S := S) (b := b) (RI := RI) Φ).2 hΦ
            exact hU this
      -- Conclude `hubSieveOfSet U (𝟙 ⋆)` using `hUniv`.
      simp [hubSieveOfSet_id, hUniv]
  | some Φ =>
      have hf' : f = leafHom (S := S) Φ := Subsingleton.elim _ _
      subst hf'
      have hClose :
          (topology (S := S) (b := b) RI).close (hubSieveOfSet (S := S) (U := U)) (leafHom (S := S) Φ) :=
        hf
      have hOr :
          Φ ∈ nonClosedCore (S := S) (b := b) RI ∨ hubSieveOfSet (S := S) (U := U) (leafHom (S := S) Φ) :=
        (close_leafHom_iff (S := S) (b := b) (RI := RI)
              (T := hubSieveOfSet (S := S) (U := U)) (Φ := Φ)).1 hClose
      rcases hOr with hΦ | hΦ
      · exact (hubSieveOfSet_leafHom (S := S) (U := U) Φ).2 (hU hΦ)
      · exact hΦ

abbrev HubClosedSieve : Type _ :=
  {T : Sieve (Hub (S := S)) // (topology (S := S) (b := b) RI).IsClosed T}

/-- Closed selector truth values (`ΩClosed`) are equivalent to `J`-closed hub sieves on the selector site. -/
noncomputable def equivΩClosedHubClosedSieve :
    ΩClosed (S := S) (b := b) RI ≃ HubClosedSieve (S := S) (b := b) RI := by
  classical
  refine
    { toFun := fun U => ?_
      invFun := fun T => ?_
      left_inv := ?_
      right_inv := ?_ }
  · -- `ΩClosed` carries the “core ⊆ U” condition via membership in the sublocale.
    let Uset : Set (Selector S) := (U : Set (Selector S))
    have hCore : nonClosedCore (S := S) (b := b) RI ⊆ Uset :=
      (mem_closedSelectorNucleus_toSublocale_iff (S := S) (b := b) (RI := RI) (U := Uset)).1 U.2
    refine ⟨hubSieveOfSet (S := S) (U := Uset), ?_⟩
    exact isClosed_hubSieveOfSet_of_core_subset (S := S) (b := b) (RI := RI) (U := Uset) hCore
  · -- From a closed hub sieve, extract the leaf subset and package it as `ΩClosed`.
    let Uset : Set (Selector S) := leafSet (S := S) (T := T.1)
    have hCore : nonClosedCore (S := S) (b := b) RI ⊆ Uset :=
      core_subset_leafSet_of_isClosed (S := S) (b := b) (RI := RI) (T := T.1) T.2
    refine ⟨Uset, (mem_closedSelectorNucleus_toSublocale_iff (S := S) (b := b) (RI := RI) (U := Uset)).2 hCore⟩
  · intro U
    -- `leafSet (hubSieveOfSet Uset) = Uset`.
    apply Subtype.ext
    simp [leafSet_hubSieveOfSet]
  · rintro ⟨T, hT⟩
    -- A closed hub sieve is determined by its leaf set, and `ΩClosed` enforces the “no extra top”.
    apply Subtype.ext
    ext Y f
    cases Y with
    | some Φ =>
        have hf : f = leafHom (S := S) Φ := Subsingleton.elim _ _
        subst hf
        simp [leafSet, hubSieveOfSet_leafHom]
    | none =>
        have hf : f = 𝟙 (Hub (S := S)) := Subsingleton.elim _ _
        subst hf
        constructor
        · intro hIdSieve
          have hUniv : leafSet (S := S) (T := T) = Set.univ := by
            simpa [hubSieveOfSet_id, leafSet] using hIdSieve
          -- If all leaves are in `T`, then `T` covers `𝟙`, hence contains it by closedness.
          have hCoverHub : T ∈ (topology (S := S) (b := b) RI) (Hub (S := S)) := by
            -- Hub coverages require all closed leaf arrows.
            change T ∈ cover (S := S) (b := b) RI (Hub (S := S))
            dsimp [cover]
            intro Φ hΦ
            have hAll : ∀ Φ, Φ ∈ leafSet (S := S) (T := T) :=
              (Set.eq_univ_iff_forall).1 hUniv
            have : Φ ∈ leafSet (S := S) (T := T) := hAll Φ
            simpa [leafSet] using this
          have hCovers : (topology (S := S) (b := b) RI).Covers T (𝟙 (Hub (S := S))) :=
            ((topology (S := S) (b := b) RI).covering_iff_covers_id (S := T) (X := Hub (S := S))).1
              hCoverHub
          exact hT _ hCovers
        · intro hId
          -- If `𝟙` is in a sieve, it is top, hence all leaves are present.
          have hTop : T = (⊤ : Sieve (Hub (S := S))) :=
            (Sieve.id_mem_iff_eq_top (S := T) (X := Hub (S := S))).1 hId
          have hUniv : leafSet (S := S) (T := T) = Set.univ := by
            ext Φ
            simp [leafSet, hTop]
          -- Repackage as membership of `hubSieveOfSet` at `𝟙`.
          simpa [hubSieveOfSet_id, leafSet] using hUniv

end SelectorSite

end MRSystems
end LoF
end HeytingLean
