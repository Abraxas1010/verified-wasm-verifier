import HeytingLean.CDL.LaxAlgebraComonoid

/-!
# CDL: deriving the parameter comonoid from a 2-cell presentation

`HeytingLean.CDL.LaxParaAlg` packages the CDL Theorem G.10 conclusion directly:
`eps : P → 1` and `delta : P → P × P` with comonoid laws.

To make the dependency chain closer to the paper, this file introduces a more categorical
*presentation* of the same data:

- a parametric algebra 1-cell `a : T A ⟶ A` in `Para(Type)`,
- a “unit 2-cell” `ι : 𝟙 A ⟶ (η_A ≫ a)` whose underlying reparameterization deletes parameters,
- a “multiplication 2-cell” `μ : (T a ≫ a) ⟶ (μ_A ≫ a)` whose underlying reparameterization copies
  parameters.

In the cartesian `Type` specialization, extracting the reparameterization maps from `ι` and `μ`
recovers `eps` and `delta`. The *coherence* laws needed to make these into a comonoid are
collected as fields (they correspond to the usual lax-algebra axioms for a 2-monad).

No proof gaps: this file is an organizational refactor that makes explicit where the comonoid laws
enter.
-/

namespace HeytingLean
namespace CDL

universe u

open HeytingLean.CDL.Para

/-! ## A 2-cell presentation of the induced parameter comonoid -/

structure ParaTLaxAlg (T : Type u → Type u) [StrongMonad T] [LawfulMonad T] (A : Type u) :
    Type (u + 1) where
  /-- The algebra 1-cell `T A ⟶ A` with parameter object `P`. -/
  a : ParaHom (T A) A
  /-- Unit 2-cell: `𝟙 A ⟶ η_A ≫ a` (its reparameterization deletes `P`). -/
  unit₂ : Para2Hom (ParaHom.id A) (ParaHom.comp a (Para.unit (T := T) A))
  /-- Multiplication 2-cell: `T a ≫ a ⟶ μ_A ≫ a` (its reparameterization copies `P`). -/
  mult₂ : Para2Hom (ParaHom.comp a (Para.map (T := T) a)) (ParaHom.comp a (Para.mult (T := T) A))

namespace ParaTLaxAlg

variable {T : Type u → Type u} [StrongMonad T] [LawfulMonad T]
variable {A : Type u}

/-- Parameter type of the lax algebra. -/
abbrev P (alg : ParaTLaxAlg (T := T) (A := A)) : Type u := alg.a.P

/-- Extract the counit map `ε : P → 1` from the unit 2-cell. -/
def eps (alg : ParaTLaxAlg (T := T) (A := A)) : alg.P → PUnit.{u + 1} :=
  fun p => alg.unit₂.r (p, PUnit.unit)

/-- Extract the comultiplication `Δ : P → P × P` from the multiplication 2-cell. -/
def delta (alg : ParaTLaxAlg (T := T) (A := A)) : alg.P → alg.P × alg.P :=
  fun p => alg.mult₂.r (p, PUnit.unit)

/-!
## Coherence laws (cartesian specialization)

In a general actegory/2-monad development these would be stated as pasting equalities of 2-cells.
For the current `Type` specialization, it is maximally transparent (and easiest to audit) to
record them as equations on the extracted maps.
-/

structure Coherence (alg : ParaTLaxAlg (T := T) (A := A)) : Type (u + 1) where
  counit_left : ∀ p, (eps alg (delta alg p).1, (delta alg p).2) = (PUnit.unit, p)
  counit_right : ∀ p, ((delta alg p).1, eps alg (delta alg p).2) = (p, PUnit.unit)
  coassoc :
    ∀ p,
      ((delta alg (delta alg p).1).1, ((delta alg (delta alg p).1).2, (delta alg p).2)) =
        ((delta alg p).1, delta alg (delta alg p).2)

/-- From a coherent `ParaTLaxAlg`, we obtain the induced comonoid structure on parameters. -/
def toComonoid (alg : ParaTLaxAlg (T := T) (A := A)) (h : Coherence alg) : ComonoidStruct alg.P :=
  { counit := eps alg
    comult := delta alg
    counit_left := h.counit_left
    counit_right := h.counit_right
    coassoc := h.coassoc }

end ParaTLaxAlg

end CDL
end HeytingLean
