import HeytingLean.CDL.StrongMonad

/-!
# CDL: lax algebras induce comonoids (cartesian Para case)

CDL’s key structural claim (Appendix G, Theorem G.10) is that a *lax algebra* for the lifted
2-monad `Para(T)` forces the parameter object `P` to carry a **comonoid** structure, whose
comultiplication `Δ_P` is exactly the “weight tying” map.

In this repo’s Lean-realistic scope (starting in `Type`):

- we represent the comonoid laws directly as equations in `Type` (cartesian monoidal),
- we package the “lax algebra data” as explicit maps `ε : P → 1` and `Δ : P → P × P`,
  together with the comonoid axioms.

This is sufficient to formalize the *mechanism* of weight tying:
reusing a parametric cell twice produces parameters `P × P`, and precomposing with `Δ_P` ties them.
-/

namespace HeytingLean
namespace CDL

universe u

open HeytingLean.CDL.Para

/-! ## Comonoids in `(Type, Prod, PUnit)` -/

structure ComonoidStruct (P : Type u) : Type (u + 1) where
  counit : P → PUnit.{u + 1}
  comult : P → P × P
  counit_left : ∀ p, (counit (comult p).1, (comult p).2) = (PUnit.unit, p)
  counit_right : ∀ p, ((comult p).1, counit (comult p).2) = (p, PUnit.unit)
  coassoc :
    ∀ p,
      ((comult (comult p).1).1, ((comult (comult p).1).2, (comult p).2)) =
        ((comult p).1, comult (comult p).2)

namespace ComonoidStruct

variable {P : Type u} (C : ComonoidStruct P)

theorem comult_fst (p : P) : (C.comult p).1 = p := by
  have h := congrArg Prod.fst (C.counit_right p)
  simpa using h

theorem comult_snd (p : P) : (C.comult p).2 = p := by
  have h := congrArg Prod.snd (C.counit_left p)
  simpa using h

theorem comult_eq_diag : C.comult = fun p => (p, p) := by
  funext p
  apply Prod.ext
  · simpa using C.comult_fst p
  · simpa using C.comult_snd p

end ComonoidStruct

/-! ## “Lax algebra data” (minimal, CDL-shaped) -/

/-- Minimal lax-algebra interface used for CDL weight tying: a parametric algebra map plus the
induced comonoid structure on parameters. -/
structure LaxParaAlg (T : Type u → Type u) [StrongMonad T] (A : Type u) : Type (u + 1) where
  P : Type u
  a : P × T A → A
  eps : P → PUnit.{u + 1}
  delta : P → P × P
  counit_left : ∀ p, (eps (delta p).1, (delta p).2) = (PUnit.unit, p)
  counit_right : ∀ p, ((delta p).1, eps (delta p).2) = (p, PUnit.unit)
  coassoc :
    ∀ p,
      ((delta (delta p).1).1, ((delta (delta p).1).2, (delta p).2)) =
        ((delta p).1, delta (delta p).2)

namespace LaxParaAlg

variable {T : Type u → Type u} [StrongMonad T]
variable {A : Type u}

def toComonoid (alg : LaxParaAlg (T := T) (A := A)) : ComonoidStruct alg.P :=
  { counit := alg.eps
    comult := alg.delta
    counit_left := alg.counit_left
    counit_right := alg.counit_right
    coassoc := alg.coassoc }

end LaxParaAlg

/-! ## Weight tying as reparameterization -/

namespace WeightTying

variable {X : Type u}

/-- Tie `m.P × m.P` parameters back down to a single `m.P` using `Δ : m.P → m.P × m.P`. -/
def tie2 (m : ParaHom X X) (Δ : m.P → m.P × m.P) : ParaHom X X :=
  ParaHom.reparam (ParaHom.comp m m) Δ

def tie2_correct (m : ParaHom X X) (Δ : m.P → m.P × m.P) :
    Para2Hom (ParaHom.comp m m) (ParaHom.reparam (ParaHom.comp m m) Δ) :=
  Para2Hom.reparam (m := ParaHom.comp m m) Δ

def tie2_sigma (m : ParaHom X X) (Δ : m.P → m.P × m.P) :
    Σ m' : ParaHom X X, Para2Hom (ParaHom.comp m m) m' :=
  ⟨ParaHom.reparam (ParaHom.comp m m) Δ, Para2Hom.reparam (m := ParaHom.comp m m) Δ⟩

theorem tie2_exists (m : ParaHom X X) (Δ : m.P → m.P × m.P) :
    ∃ m' : ParaHom X X, Nonempty (Para2Hom (ParaHom.comp m m) m') := by
  refine ⟨ParaHom.reparam (ParaHom.comp m m) Δ, ?_⟩
  exact ⟨Para2Hom.reparam (m := ParaHom.comp m m) Δ⟩

end WeightTying

end CDL
end HeytingLean
