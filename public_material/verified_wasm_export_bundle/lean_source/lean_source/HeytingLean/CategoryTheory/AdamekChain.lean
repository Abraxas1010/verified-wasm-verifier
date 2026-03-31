import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open scoped Classical

open CategoryTheory
open CategoryTheory.Limits

namespace HeytingLean.CategoryTheory.AdamekChain

universe v u

variable {C : Type u} [Category.{v} C]

/-- The objects of the ω-Adámek chain: `0 ↦ ⊥`, `n+1 ↦ F (A n)`. -/
noncomputable def obj (F : C ⥤ C) [HasInitial C] : ℕ → C
  | 0 => ⊥_ C
  | n + 1 => F.obj (obj F n)

/-- The successor maps of the ω-Adámek chain. -/
noncomputable def step (F : C ⥤ C) [HasInitial C] :
    ∀ n : ℕ, obj (C := C) F n ⟶ obj (C := C) F (n + 1)
  | 0 => initial.to (F.obj (⊥_ C))
  | n + 1 => F.map (step F n)

@[simp] lemma step_succ (F : C ⥤ C) [HasInitial C] (n : ℕ) :
    step (C := C) F (n+1) = F.map (step (C := C) F n) := rfl

/-- The ω-Adámek chain as a diagram `ℕ ⥤ C`. -/
noncomputable def chain (F : C ⥤ C) [HasInitial C] : ℕ ⥤ C :=
  Functor.ofSequence (X := obj (C := C) F) (step (C := C) F)

@[simp] lemma chain_map_succ (F : C ⥤ C) [HasInitial C] (n : ℕ) :
    (chain (C := C) F).map (homOfLE (Nat.le_add_right n 1)) = step (C := C) F n := by
  simp [chain]

/-- The cocone on the shifted diagram `(chain F ⋙ F)` with vertex `colimit (chain F)`
whose legs are the colimit inclusions at `n+1`. -/
noncomputable def shiftCocone (F : C ⥤ C) [HasInitial C]
    [HasColimit (chain (C := C) F)] : Cocone (chain (C := C) F ⋙ F) where
  pt := colimit (chain (C := C) F)
  ι :=
    NatTrans.ofSequence
      (app := fun n => (colimit.ι (chain (C := C) F) (n + 1)))
      (naturality := by
        intro n
        simpa [chain_map_succ, step_succ, Category.assoc] using
          (colimit.w (chain (C := C) F) (homOfLE (Nat.le_add_right (n + 1) 1))))

/-- The Adámek colimit object `colimit (chain F)` equipped with its induced `F`-algebra structure. -/
noncomputable def colimitAlgebra (F : C ⥤ C) [HasInitial C]
    [HasColimit (chain (C := C) F)] [PreservesColimit (chain (C := C) F) F] :
    Endofunctor.Algebra F where
  a := colimit (chain (C := C) F)
  str := (preservesColimitIso F (chain (C := C) F)).hom ≫
    colimit.desc _ (shiftCocone (C := C) F)

@[reassoc]
lemma colimitAlgebra_str_ι (F : C ⥤ C) [HasInitial C]
    [HasColimit (chain (C := C) F)] [PreservesColimit (chain (C := C) F) F] (n : ℕ) :
    F.map (colimit.ι (chain (C := C) F) n) ≫ (colimitAlgebra (C := C) F).str =
      colimit.ι (chain (C := C) F) (n + 1) := by
  simp [colimitAlgebra, shiftCocone]

/-- Recursive maps from the Adámek chain into an algebra. -/
noncomputable def toAlg (F : C ⥤ C) [HasInitial C]
    (A : Endofunctor.Algebra F) : ∀ n : ℕ, obj (C := C) F n ⟶ A.a
  | 0 => initial.to A.a
  | n + 1 => F.map (toAlg F A n) ≫ A.str

@[simp] lemma toAlg_zero (F : C ⥤ C) [HasInitial C] (A : Endofunctor.Algebra F) :
    toAlg (C := C) F A 0 = initial.to A.a := rfl

@[simp] lemma toAlg_succ (F : C ⥤ C) [HasInitial C] (A : Endofunctor.Algebra F) (n : ℕ) :
    toAlg (C := C) F A (n+1) = F.map (toAlg (C := C) F A n) ≫ A.str := rfl

lemma step_comp_toAlg_succ (F : C ⥤ C) [HasInitial C] (A : Endofunctor.Algebra F) (n : ℕ) :
    step (C := C) F n ≫ toAlg (C := C) F A (n+1) = toAlg (C := C) F A n := by
  induction n with
  | zero =>
      apply (initialIsInitial (C := C)).hom_ext
  | succ n ih =>
      have ih' :
          step (C := C) F n ≫ (F.map (toAlg (C := C) F A n) ≫ A.str) = toAlg (C := C) F A n := by
        simpa [toAlg_succ, Category.assoc] using ih
      have ihF :
          F.map (step (C := C) F n) ≫ F.map (F.map (toAlg (C := C) F A n)) ≫ F.map A.str =
            F.map (toAlg (C := C) F A n) := by
        simpa [Functor.map_comp, Category.assoc] using congrArg (fun f => F.map f) ih'
      simpa [step_succ, toAlg_succ, Functor.map_comp, Category.assoc] using
        congrArg (fun g => g ≫ A.str) ihF

/-- The cocone from the Adámek chain to any `F`-algebra. -/
noncomputable def coconeToAlgebra (F : C ⥤ C) [HasInitial C]
    (A : Endofunctor.Algebra F) : Cocone (chain (C := C) F) where
  pt := A.a
  ι :=
    NatTrans.ofSequence
      (app := fun n => toAlg (C := C) F A n)
      (naturality := by
        intro n
        simpa [chain_map_succ] using (step_comp_toAlg_succ (C := C) F A n))

/-- The canonical morphism from the Adámek colimit algebra to any algebra `A`. -/
noncomputable def toAlgebraHom (F : C ⥤ C) [HasInitial C]
    [HasColimit (chain (C := C) F)] [PreservesColimit (chain (C := C) F) F]
    (A : Endofunctor.Algebra F) : colimitAlgebra (C := C) F ⟶ A where
  f := colimit.desc _ (coconeToAlgebra (C := C) F A)
  h := by
    let D := chain (C := C) F
    refine (isColimitOfPreserves F (colimit.isColimit D)).hom_ext (fun n => ?_)
    let f : colimit D ⟶ A.a := colimit.desc D (coconeToAlgebra (C := C) F A)
    have hf (k : ℕ) : colimit.ι D k ≫ f = toAlg (C := C) F A k := by
      simp [f, coconeToAlgebra]
    have left : F.map (colimit.ι D n) ≫ F.map f ≫ A.str = toAlg (C := C) F A (n + 1) := by
      calc
        F.map (colimit.ι D n) ≫ F.map f ≫ A.str
            = F.map (colimit.ι D n ≫ f) ≫ A.str := by
                simp [Functor.map_comp, Category.assoc]
        _ = F.map (toAlg (C := C) F A n) ≫ A.str := by
                simp [hf]
        _ = toAlg (C := C) F A (n + 1) := by
                simp [toAlg_succ]
    have right : F.map (colimit.ι D n) ≫ (colimitAlgebra (C := C) F).str ≫ f =
        toAlg (C := C) F A (n + 1) := by
      calc
        F.map (colimit.ι D n) ≫ (colimitAlgebra (C := C) F).str ≫ f
            = colimit.ι D (n + 1) ≫ f := by
                simpa [Category.assoc] using
                  congrArg (fun t => t ≫ f) (colimitAlgebra_str_ι (C := C) F n)
        _ = toAlg (C := C) F A (n + 1) := by
                simp [hf]
    simpa [f] using left.trans right.symm

/-- The Adámek colimit algebra is initial (ω-case Adámek fixed point theorem). -/
noncomputable def isInitial_colimitAlgebra (F : C ⥤ C) [HasInitial C]
    [HasColimit (chain (C := C) F)] [PreservesColimit (chain (C := C) F) F] :
    IsInitial (colimitAlgebra (C := C) F) := by
  classical
  refine IsInitial.ofUniqueHom (h := fun A => toAlgebraHom (C := C) F A) ?_
  intro A g
  ext
  refine colimit.hom_ext (fun n => ?_)
  have hrec : ∀ n : ℕ, colimit.ι (chain (C := C) F) n ≫ g.f = toAlg (C := C) F A n := by
    intro n
    induction n with
    | zero =>
        apply (initialIsInitial (C := C)).hom_ext
    | succ n ih =>
        have hι : colimit.ι (chain (C := C) F) (n + 1) ≫ g.f =
            (F.map (colimit.ι (chain (C := C) F) n) ≫ (colimitAlgebra (C := C) F).str) ≫ g.f := by
          simpa [Category.assoc] using
            (congrArg (fun t => t ≫ g.f) (colimitAlgebra_str_ι (C := C) F n)).symm
        calc
          colimit.ι (chain (C := C) F) (n + 1) ≫ g.f
              = (F.map (colimit.ι (chain (C := C) F) n) ≫ (colimitAlgebra (C := C) F).str) ≫ g.f := hι
          _ = F.map (colimit.ι (chain (C := C) F) n) ≫ ((colimitAlgebra (C := C) F).str ≫ g.f) := by
                simp [Category.assoc]
          _ = F.map (colimit.ι (chain (C := C) F) n) ≫ (F.map g.f ≫ A.str) := by
                exact
                  congrArg (fun t => F.map (colimit.ι (chain (C := C) F) n) ≫ t) g.h.symm
          _ = F.map (colimit.ι (chain (C := C) F) n ≫ g.f) ≫ A.str := by
                simp [Functor.map_comp, Category.assoc]
          _ = F.map (toAlg (C := C) F A n) ≫ A.str := by
                simp [ih]
          _ = toAlg (C := C) F A (n + 1) := by
                simp [toAlg_succ]
  have hcan :
      colimit.ι (chain (C := C) F) n ≫ (toAlgebraHom (C := C) F A).f = toAlg (C := C) F A n := by
    simp [toAlgebraHom, coconeToAlgebra]
  exact (hrec n).trans hcan.symm

end HeytingLean.CategoryTheory.AdamekChain

