import HeytingLean.Algebra.HomotopyTower.InfinityGroupoidBridge
import HeytingLean.Tests.Plausibility
import Mathlib.CategoryTheory.Groupoid.Discrete

namespace HeytingLean.Tests.Algebra

open CategoryTheory
open HeytingLean.Algebra.HomotopyTower

/-- A concrete constant tower whose unique fixed point is `True`. -/
noncomputable def topTower : NucleusTower (α := Prop) where
  level := fun _ => ⊤
  mono := by
    intro i j hij
    rfl

def topTowerFiniteImage : FiniteImage topTower := by
  simp [FiniteImage, topTower]

/-- The unique fixed point of the constant top tower. -/
def topFixedPoint (n : Nat) : FixedPointCarrier topTower n :=
  ⟨True, by simp [topTower]⟩

theorem topFixedPoint_eq (n : Nat) (x : FixedPointCarrier topTower n) :
    x = topFixedPoint n := by
  apply Subtype.ext
  simpa [topFixedPoint, topTower] using x.2.symm

instance (n : Nat) : Subsingleton (FixedPointCarrier topTower n) := by
  refine ⟨fun x y => ?_⟩
  rw [topFixedPoint_eq n x, topFixedPoint_eq n y]

def topFixedObj (n : Nat) : FixedPointObj topTower n :=
  Discrete.mk (topFixedPoint n)

instance (n : Nat) : Subsingleton (FixedPointObj topTower n) := by
  dsimp [FixedPointObj]
  infer_instance

instance punitEmptyQuiver : Quiver PUnit where
  Hom _ _ := PEmpty

noncomputable def topTransportQuiver :
    StableTransportQuiver topTower topTowerFiniteImage where
  Obj := fun _ => PUnit
  instQuiver := fun _ => punitEmptyQuiver
  drop := fun _ => 𝟭q PUnit

instance : Subsingleton (Quiver.Symmetrify PUnit) := by
  refine ⟨fun x y => ?_⟩
  cases x
  cases y
  rfl

instance : Subsingleton (CategoryTheory.Paths (Quiver.Symmetrify PUnit)) := by
  dsimp [CategoryTheory.Paths]
  infer_instance

instance (n : Nat) : Subsingleton (StageGroupoid topTransportQuiver n) := by
  refine ⟨fun X Y => ?_⟩
  cases X
  cases Y
  congr

instance (n : Nat) : Subsingleton ((stableGroupoidTower topTransportQuiver).Obj n) :=
  show Subsingleton (StageGroupoid topTransportQuiver n) from inferInstance

instance (n : Nat) : Subsingleton ((fixedPointCatTower topTower).Obj n) :=
  show Subsingleton (FixedPointObj topTower n) from inferInstance

theorem topStage_hom_eq (n : Nat) {X Y : StageGroupoid topTransportQuiver n} (f : X ⟶ Y) :
    f = eqToHom (Subsingleton.elim X Y) := by
  have hXY : X = Y := Subsingleton.elim X Y
  cases hXY
  change f = 𝟙 X
  refine Quot.inductionOn f ?_
  intro p
  cases p with
  | nil => rfl
  | cons q e =>
      cases e with
      | inl val => cases val
      | inr val => cases val

instance (n : Nat) (X Y : StageGroupoid topTransportQuiver n) : Subsingleton (X ⟶ Y) := by
  refine ⟨fun f g => ?_⟩
  exact (topStage_hom_eq n f).trans (topStage_hom_eq n g).symm

instance (n : Nat) (X Y : (stableGroupoidTower topTransportQuiver).Obj n) :
    Subsingleton (X ⟶ Y) := by
  refine ⟨fun f g => ?_⟩
  exact (topStage_hom_eq n f).trans (topStage_hom_eq n g).symm

instance (n : Nat) (X Y : (fixedPointCatTower topTower).Obj n) : Subsingleton (X ⟶ Y) := by
  simpa [fixedPointCatTower, FixedPointObj] using
    (CategoryTheory.Discrete.instSubsingletonDiscreteHom X Y)

noncomputable def topComparisonForward (n : Nat) :
    FixedPointObj topTower n ⥤ StageGroupoid topTransportQuiver n where
  obj := fun _ => (Quiver.FreeGroupoid.of PUnit).obj PUnit.unit
  map := by
    intro X Y f
    cases f
    exact 𝟙 _

noncomputable def topComparisonBackward (n : Nat) :
    StageGroupoid topTransportQuiver n ⥤ FixedPointObj topTower n where
  obj := fun _ => topFixedObj n
  map := by
    intro X Y f
    exact 𝟙 _

noncomputable def topComparisonUnitIso (n : Nat) :
    𝟭 (FixedPointObj topTower n) ≅
      (topComparisonForward n ⋙ topComparisonBackward n) :=
  NatIso.ofComponents (fun _ => Discrete.eqToIso (by apply Subsingleton.elim)) (by
    intro X Y f
    apply Subsingleton.elim)

noncomputable def topComparisonCounitIso (n : Nat) :
    (topComparisonBackward n ⋙ topComparisonForward n) ≅
      𝟭 (StageGroupoid topTransportQuiver n) :=
  NatIso.ofComponents (fun X => eqToIso (Subsingleton.elim _ X)) (by
    intro X Y f
    apply Subsingleton.elim)

noncomputable def topComparisonTowerForward :
    TowerFunctor (fixedPointCatTower topTower) (stableGroupoidTower topTransportQuiver) where
  F := topComparisonForward
  comm := by
    intro n
    refine CategoryTheory.Functor.ext
      (F := (topComparisonForward (n + 1)) ⋙ (stableGroupoidTower topTransportQuiver).drop n)
      (G := (fixedPointCatTower topTower).drop n ⋙ topComparisonForward n) ?_ ?_
    · intro X
      cases X
      rfl
    · intro X Y f
      apply Subsingleton.elim

noncomputable def topComparisonTowerBackward :
    TowerFunctor (stableGroupoidTower topTransportQuiver) (fixedPointCatTower topTower) where
  F := topComparisonBackward
  comm := by
    intro n
    refine CategoryTheory.Functor.ext
      (F := (topComparisonBackward (n + 1)) ⋙ (fixedPointCatTower topTower).drop n)
      (G := (stableGroupoidTower topTransportQuiver).drop n ⋙ topComparisonBackward n) ?_ ?_
    · intro X
      apply Subsingleton.elim
    · intro X Y f
      apply Subsingleton.elim

noncomputable def topComparisonTowerUnitIso :
    TowerNatIso (TowerFunctor.id (fixedPointCatTower topTower))
      (TowerFunctor.comp topComparisonTowerBackward topComparisonTowerForward) where
  app := fun n =>
    NatIso.ofComponents (fun _ => Discrete.eqToIso (by apply Subsingleton.elim)) (by
      intro X Y f
      apply Subsingleton.elim)
  hom_comm := by
    intro n
    ext X
    apply Subsingleton.elim
  inv_comm := by
    intro n
    ext X
    apply Subsingleton.elim

noncomputable def topComparisonTowerCounitIso :
    TowerNatIso (TowerFunctor.comp topComparisonTowerForward topComparisonTowerBackward)
      (TowerFunctor.id (stableGroupoidTower topTransportQuiver)) where
  app := fun n =>
    NatIso.ofComponents (fun X => eqToIso (Subsingleton.elim _ X)) (by
      intro X Y f
      apply Subsingleton.elim)
  hom_comm := by
    intro n
    ext X
    apply Subsingleton.elim
  inv_comm := by
    intro n
    ext X
    apply Subsingleton.elim

noncomputable def topComparisonTowerEquivalence :
    TowerEquivalence (fixedPointCatTower topTower) (stableGroupoidTower topTransportQuiver) where
  F := topComparisonTowerForward
  G := topComparisonTowerBackward
  unitIso := topComparisonTowerUnitIso
  counitIso := topComparisonTowerCounitIso
  functor_unitIso_comp := by
    intro n X
    apply Subsingleton.elim

noncomputable def topComparison :
    StableTransportComparison topTower topTowerFiniteImage where
  Q := topTransportQuiver
  towerEquiv := topComparisonTowerEquivalence

example :
    Nonempty
      (StableFixedPointCategory topTower topTowerFiniteImage ≌
        (comparisonInftyGroupoidPresentation topTower topTowerFiniteImage topComparison).Obj) :=
  stabilized_fixed_point_category_has_infty_groupoid_presentation
    topTower topTowerFiniteImage topComparison

namespace TopTransportStructural

inductive Vertex where
  | base
  | tip
deriving DecidableEq

instance : Quiver Vertex where
  Hom X Y :=
    match X, Y with
    | .base, .tip => PUnit
    | _, _ => PEmpty

def edge : Vertex.base ⟶ Vertex.tip := PUnit.unit

noncomputable def quiver : StableTransportQuiver topTower topTowerFiniteImage where
  Obj := fun _ => Vertex
  instQuiver := fun _ => inferInstance
  drop := fun _ => 𝟭q Vertex

noncomputable def baseObj (n : Nat) : StageGroupoid quiver n :=
  (Quiver.FreeGroupoid.of Vertex).obj Vertex.base

noncomputable def tipObj (n : Nat) : StageGroupoid quiver n :=
  (Quiver.FreeGroupoid.of Vertex).obj Vertex.tip

noncomputable def edgeHom (n : Nat) : baseObj n ⟶ tipObj n :=
  (Quiver.FreeGroupoid.of Vertex).map edge

example : Nonempty (baseObj 0 ⟶ tipObj 0) := ⟨edgeHom 0⟩

def collapsePrefunctor (n : Nat) : Vertex ⥤q FixedPointObj topTower n where
  obj := fun _ => topFixedObj n
  map := by
    intro X Y f
    cases X <;> cases Y <;> cases f
    exact 𝟙 _

noncomputable def collapse (n : Nat) : StageGroupoid quiver n ⥤ FixedPointObj topTower n :=
  Quiver.FreeGroupoid.lift (collapsePrefunctor n)

theorem drop_edgeHom (n : Nat) :
    ((stableGroupoidTower quiver).drop n).map (edgeHom (n + 1)) = edgeHom n := by
  change (Quiver.freeGroupoidFunctor (𝟭q Vertex)).map
      ((Quiver.FreeGroupoid.of Vertex).map edge) =
    (Quiver.FreeGroupoid.of Vertex).map edge
  simpa [edgeHom] using
    (Functor.congr_hom (Quiver.freeGroupoidFunctor_id (V := Vertex))
      ((Quiver.FreeGroupoid.of Vertex).map edge))

noncomputable def collapseTower :
    TowerFunctor (stableGroupoidTower quiver) (fixedPointCatTower topTower) where
  F := collapse
  -- NB: Both cases resolve via Subsingleton.elim because the target categories
  -- (FixedPointObj topTower n) are discrete on a subsingleton carrier.  The genuine
  -- structural content in this regression is tested by `drop_edgeHom` above, which
  -- proves that the tower drop functor preserves the non-identity generator edge
  -- through real computation (via `freeGroupoidFunctor_id`), not Subsingleton.elim.
  --
  -- A non-vacuous commutativity test would require a tower whose fixed-point
  -- categories have genuine morphisms — i.e., a frame with non-trivially-grouped
  -- fixed points.  That is an architectural limitation of the `topTower` (constant ⊤
  -- on Prop) and `demoTower` (empty quiver on Set Bool) witnesses, not a gap in the
  -- TowerFunctor infrastructure itself.
  comm := by
    intro n
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro X
      apply Subsingleton.elim
    · intro X Y f
      apply Subsingleton.elim

end TopTransportStructural

noncomputable def addTrueNucleusSetBool : Nucleus (Set Bool) where
  toFun s := insert true s
  map_inf' := by
    intro s t
    ext b
    cases b <;> simp
  idempotent' := by
    intro s b hb
    simp at hb ⊢
    exact hb
  le_apply' := by
    intro s
    exact Set.subset_insert true s

noncomputable def demoTower : NucleusTower (α := Set Bool) where
  level
    | 0 => HeytingLean.Tests.idNucleusSetBool
    | _ + 1 => addTrueNucleusSetBool
  mono := by
    intro i j hij
    cases i with
    | zero =>
        cases j with
        | zero => rfl
        | succ j =>
            intro s
            exact Set.subset_insert true s
    | succ i =>
        cases j with
        | zero => cases hij
        | succ j => rfl

def demoTowerFiniteImage : FiniteImage demoTower := by
  classical
  refine Set.Finite.subset (Set.toFinite {HeytingLean.Tests.idNucleusSetBool, addTrueNucleusSetBool}) ?_
  intro J hJ
  rcases hJ with ⟨n, rfl⟩
  cases n <;> simp [demoTower]

theorem demoTower_not_stabilized_at_zero : ¬ TowerStabilizes demoTower 0 := by
  intro h
  have h01 := h 1 (by simp)
  have hEq : addTrueNucleusSetBool = HeytingLean.Tests.idNucleusSetBool := by
    simpa [demoTower] using h01
  have hVal := congrArg (fun J : Nucleus (Set Bool) => J (∅ : Set Bool)) hEq
  have hempty' : ({true} : Set Bool) = HeytingLean.Tests.idNucleusSetBool (∅ : Set Bool) := by
    simpa [addTrueNucleusSetBool] using hVal
  have hempty : ({true} : Set Bool) = (∅ : Set Bool) := by
    simp [HeytingLean.Tests.idNucleusSetBool] at hempty' ⊢
  have htrue : (true : Bool) ∈ ({true} : Set Bool) := by simp
  have hmem : (true : Bool) ∈ (∅ : Set Bool) := by
    simp [hempty] at htrue ⊢
  simp at hmem

namespace DemoTransport

def emptyQuiver (β : Type*) : Quiver β where
  Hom _ _ := PEmpty

instance fixedPointQuiver (n : Nat) : Quiver (FixedPointCarrier demoTower n) :=
  emptyQuiver (FixedPointCarrier demoTower n)

instance fixedPointEmptyHom (n : Nat) (X Y : FixedPointCarrier demoTower n) : IsEmpty (X ⟶ Y) := by
  change IsEmpty PEmpty
  infer_instance

noncomputable def quiver : StableTransportQuiver demoTower demoTowerFiniteImage where
  Obj := FixedPointCarrier demoTower
  instQuiver := fixedPointQuiver
  drop := fun n =>
    { obj := dropFixedPoint demoTower n
      map := by
        intro X Y f
        exact (IsEmpty.false f).elim }

theorem obj_eq_of_hom (n : Nat) {X Y : StageGroupoid quiver n} (f : X ⟶ Y) : X = Y := by
  cases X
  cases Y
  apply Quotient.ext
  exact Quot.inductionOn f (fun p => by
    cases p with
    | nil => rfl
    | cons q e =>
        cases e with
        | inl val => cases val
        | inr val => cases val)

theorem hom_eq (n : Nat) {X Y : StageGroupoid quiver n} (f : X ⟶ Y) :
    f = eqToHom (obj_eq_of_hom n f) := by
  have hXY : X = Y := obj_eq_of_hom n f
  cases hXY
  change f = 𝟙 X
  refine Quot.inductionOn f ?_
  intro p
  cases p with
  | nil => rfl
  | cons q e =>
      cases e with
      | inl val => cases val
      | inr val => cases val

instance stageHomSubsingleton (n : Nat) (X Y : StageGroupoid quiver n) : Subsingleton (X ⟶ Y) := by
  refine ⟨fun f g => ?_⟩
  rw [hom_eq n f, hom_eq n g]

instance stageTowerHomSubsingleton (n : Nat) (X Y : (stableGroupoidTower quiver).Obj n) :
    Subsingleton (X ⟶ Y) := by
  exact stageHomSubsingleton n X Y

instance fixedPointTowerHomSubsingleton (n : Nat) (X Y : (fixedPointCatTower demoTower).Obj n) :
    Subsingleton (X ⟶ Y) := by
  simpa [fixedPointCatTower, FixedPointObj] using
    (CategoryTheory.Discrete.instSubsingletonDiscreteHom X Y)

noncomputable def forward (n : Nat) : FixedPointObj demoTower n ⥤ StageGroupoid quiver n where
  obj := fun X => (Quiver.FreeGroupoid.of (FixedPointCarrier demoTower n)).obj X.as
  map := by
    intro X Y f
    cases X with
    | mk x =>
        cases Y with
        | mk y =>
            have hxy : x = y := f.down.down
            exact eqToHom (by
              simpa using congrArg
                (fun z => (Quiver.FreeGroupoid.of (FixedPointCarrier demoTower n)).obj z) hxy)

noncomputable def backward (n : Nat) : StageGroupoid quiver n ⥤ FixedPointObj demoTower n where
  obj := fun X => Discrete.mk X.as
  map := by
    intro X Y f
    exact Discrete.eqToHom (by
      simpa using congrArg (fun Z : StageGroupoid quiver n => Z.as) (obj_eq_of_hom n f))

theorem forward_backward_eq_id (n : Nat) :
    forward n ⋙ backward n = 𝟭 (FixedPointObj demoTower n) := by
  refine CategoryTheory.Functor.ext
    (F := forward n ⋙ backward n)
    (G := 𝟭 (FixedPointObj demoTower n)) ?_ ?_
  · intro X
    cases X
    rfl
  · intro X Y f
    apply Subsingleton.elim

theorem backward_forward_eq_id (n : Nat) :
    backward n ⋙ forward n = 𝟭 (StageGroupoid quiver n) := by
  refine CategoryTheory.Functor.ext
    (F := backward n ⋙ forward n)
    (G := 𝟭 (StageGroupoid quiver n)) ?_ ?_
  · intro X
    apply Quotient.ext
    rfl
  · intro X Y f
    simpa [backward, forward, Category.comp_id] using (hom_eq n f).symm

noncomputable def stageUnitIso (n : Nat) :
    𝟭 (FixedPointObj demoTower n) ≅ forward n ⋙ backward n :=
  NatIso.ofComponents (fun X => Discrete.eqToIso (by cases X; rfl)) (by
    intro X Y f
    apply Subsingleton.elim)

noncomputable def stageCounitIso (n : Nat) :
    backward n ⋙ forward n ≅ 𝟭 (StageGroupoid quiver n) :=
  NatIso.ofComponents (fun X => eqToIso (by apply Quotient.ext; rfl)) (by
    intro X Y f
    apply Subsingleton.elim)

noncomputable def equivalence (n : Nat) : FixedPointObj demoTower n ≌ StageGroupoid quiver n where
  functor := forward n
  inverse := backward n
  unitIso := stageUnitIso n
  counitIso := stageCounitIso n
  functor_unitIso_comp := by
    intro X
    apply Subsingleton.elim

noncomputable def towerForward :
    TowerFunctor (fixedPointCatTower demoTower) (stableGroupoidTower quiver) where
  F := forward
  comm := by
    intro n
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro X
      rfl
    · intro X Y f
      apply Subsingleton.elim

noncomputable def towerBackward :
    TowerFunctor (stableGroupoidTower quiver) (fixedPointCatTower demoTower) where
  F := backward
  comm := by
    intro n
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro X
      cases X
      rfl
    · intro X Y f
      apply Subsingleton.elim

noncomputable def towerUnitIso :
    TowerNatIso (TowerFunctor.id (fixedPointCatTower demoTower))
      (TowerFunctor.comp towerBackward towerForward) where
  app := by
    intro n
    exact NatIso.ofComponents (fun X => Discrete.eqToIso (by cases X; rfl)) (by
      intro X Y f
      apply Subsingleton.elim)
  hom_comm := by
    intro n
    ext X
    apply Subsingleton.elim
  inv_comm := by
    intro n
    ext X
    apply Subsingleton.elim

noncomputable def towerCounitIso :
    TowerNatIso (TowerFunctor.comp towerForward towerBackward)
      (TowerFunctor.id (stableGroupoidTower quiver)) where
  app := by
    intro n
    exact NatIso.ofComponents (fun X => eqToIso (by apply Quotient.ext; rfl)) (by
      intro X Y f
      apply Subsingleton.elim)
  hom_comm := by
    intro n
    ext X
    apply Subsingleton.elim
  inv_comm := by
    intro n
    ext X
    apply Subsingleton.elim

noncomputable def towerEquivalence :
    TowerEquivalence (fixedPointCatTower demoTower) (stableGroupoidTower quiver) where
  F := towerForward
  G := towerBackward
  unitIso := towerUnitIso
  counitIso := towerCounitIso
  functor_unitIso_comp := by
    intro n X
    apply Subsingleton.elim

noncomputable def comparison :
    StableTransportComparison demoTower demoTowerFiniteImage where
  Q := quiver
  towerEquiv := towerEquivalence

end DemoTransport

example : stabilizationIndex demoTower demoTowerFiniteImage ≠ 0 := by
  intro h0
  exact demoTower_not_stabilized_at_zero <| by
    simpa [h0] using stabilizationIndex_spec demoTower demoTowerFiniteImage

example :
    Nonempty
      (StableFixedPointCategory demoTower demoTowerFiniteImage ≌
        (comparisonInftyGroupoidPresentation demoTower demoTowerFiniteImage
          DemoTransport.comparison).Obj) :=
  stabilized_fixed_point_category_has_infty_groupoid_presentation
    demoTower demoTowerFiniteImage DemoTransport.comparison

/-! ### Non-vacuous TowerFunctor commutativity regression

This section closes the persistent audit residual from Rounds 1–5: every prior
TowerFunctor commutativity proof resolved via `Subsingleton.elim` because one
side of the comparison was always a Discrete (subsingleton) category.

Here we build a TowerFunctor between two `stableGroupoidTower`s — both with
genuine non-identity morphisms — where the `comm` proof uses
`freeGroupoidFunctor_comp` and prefunctor algebra, not `Subsingleton.elim`.

**Design**: A symmetric 2-vertex quiver `SV` with a swap automorphism `σ` of
order 2.  Two `StableTransportQuiver`s for `topTower`:
- `Q_twist` with `drop n = σ` (the swap)
- `Q_triv`  with `drop n = 𝟭q SV` (identity)

The TowerFunctor `F(n) = freeGroupoidFunctor (swapPower n)` interleaves the
twist: it "untwists" the σ-drop at each level.  The commutativity proof chains
through `freeGroupoidFunctor_comp`, `swapPower` recursion, and
`Prefunctor.comp_id` — all genuine morphism-level computations. -/

namespace GroupoidTowerFunctorRegression

open CategoryTheory

/-- Symmetric 2-vertex quiver with edges in both directions. -/
inductive SV where
  | p
  | q

instance svQuiver : Quiver SV where
  Hom X Y :=
    match X, Y with
    | .p, .q => PUnit
    | .q, .p => PUnit
    | _, _ => PEmpty

/-- The swap automorphism: p ↔ q, edges swapped accordingly. -/
def svSwap : SV ⥤q SV where
  obj
    | .p => .q
    | .q => .p
  map {X Y} f :=
    match X, Y, f with
    | .p, .q, _ => PUnit.unit
    | .q, .p, _ => PUnit.unit

/-- σⁿ: identity when n is even, swap when n is odd. -/
def swapPower : Nat → (SV ⥤q SV)
  | 0 => Prefunctor.id SV
  | n + 1 => svSwap ⋙q swapPower n

/-- Edge from p to q in SV. -/
def svEdge_pq : (SV.p : SV) ⟶ SV.q := PUnit.unit

/-- Edge from q to p in SV. -/
def svEdge_qp : (SV.q : SV) ⟶ SV.p := PUnit.unit

/-- Transport quiver with twisted (swap) drop. -/
noncomputable def Q_twist : StableTransportQuiver topTower topTowerFiniteImage where
  Obj := fun _ => SV
  instQuiver := fun _ => svQuiver
  drop := fun _ => svSwap

/-- Transport quiver with trivial (identity) drop. -/
noncomputable def Q_triv : StableTransportQuiver topTower topTowerFiniteImage where
  Obj := fun _ => SV
  instQuiver := fun _ => svQuiver
  drop := fun _ => Prefunctor.id SV

/-- The interleaving TowerFunctor: F(n) = freeGroupoidFunctor(σⁿ).

    The comm proof uses `freeGroupoidFunctor_comp` and prefunctor algebra —
    NO `Subsingleton.elim` anywhere.  Both source and target towers have
    genuine non-identity morphisms (p→q and q→p edges in the free groupoid). -/
noncomputable def twistedUntwist :
    TowerFunctor (stableGroupoidTower Q_twist) (stableGroupoidTower Q_triv) where
  F := fun n => Quiver.freeGroupoidFunctor (swapPower n)
  comm := by
    intro n
    -- Goal: F(n+1) ⋙ triv.drop n = twist.drop n ⋙ F(n)
    -- i.e. freeGroupoidFunctor (σ ⋙q σⁿ) ⋙ freeGroupoidFunctor (𝟭q SV)
    --    = freeGroupoidFunctor σ ⋙ freeGroupoidFunctor (σⁿ)
    show Quiver.freeGroupoidFunctor (swapPower (n + 1)) ⋙
        Quiver.freeGroupoidFunctor (Prefunctor.id SV) =
      Quiver.freeGroupoidFunctor svSwap ⋙ Quiver.freeGroupoidFunctor (swapPower n)
    -- Combine both sides into single freeGroupoidFunctor via comp lemma,
    -- simplify id, then close by definitional unfolding of swapPower.
    rw [← Quiver.freeGroupoidFunctor_comp, ← Quiver.freeGroupoidFunctor_comp,
      Prefunctor.comp_id]
    -- swapPower (n+1) = svSwap ⋙q swapPower n by definition
    rfl

/-- The edge p→q is a genuine non-identity morphism in the stage groupoid. -/
example : Nonempty
    ((Quiver.FreeGroupoid.of SV).obj SV.p ⟶ (Quiver.FreeGroupoid.of SV).obj SV.q) :=
  ⟨(Quiver.FreeGroupoid.of SV).map svEdge_pq⟩

set_option maxHeartbeats 1600000 in
/-- The twisted drop maps the p→q edge to q→p (swap).
    This witnesses non-trivial morphism transport through the tower. -/
theorem twist_drop_swaps_edge (n : Nat) :
    ((stableGroupoidTower Q_twist).drop n).map
      ((Quiver.FreeGroupoid.of SV).map svEdge_pq) =
    (Quiver.FreeGroupoid.of SV).map svEdge_qp := by
  -- Both sides reduce to the same Quot representative via kernel computation.
  -- The tower drop unfolds through stableGroupoidTower → freeGroupoidFunctor → lift,
  -- which on the single-step generator path computes by Quot reduction.
  rfl

set_option maxHeartbeats 1600000 in
/-- The trivial drop preserves the p→q edge (identity). -/
theorem triv_drop_preserves_edge (n : Nat) :
    ((stableGroupoidTower Q_triv).drop n).map
      ((Quiver.FreeGroupoid.of SV).map svEdge_pq) =
    (Quiver.FreeGroupoid.of SV).map svEdge_pq := by
  rfl

/-- F(1) maps the p→q edge to q→p (swap once). -/
theorem F1_swaps_edge :
    (twistedUntwist.F 1).map ((Quiver.FreeGroupoid.of SV).map svEdge_pq) =
    (Quiver.FreeGroupoid.of SV).map svEdge_qp :=
  twist_drop_swaps_edge 0

end GroupoidTowerFunctorRegression

end HeytingLean.Tests.Algebra
