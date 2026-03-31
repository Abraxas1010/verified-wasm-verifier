import HeytingLean.CDL.Para.Type

/-!
# CDL: Mealy machines as parametric coalgebras in `Para(Type)`

CDL viewpoint:
- A (deterministic) Mealy machine is a coalgebra for the endofunctor `F(X) = I → X × O`.
- In `Para(Type)`, a *parametric* Mealy machine is a 1-cell `S ⟶ F(S)` whose parameters `P`
  represent shared weights.

This file provides:
- `ParaMealy I O S` with parameters `P` and transition `P × I × S → S × O`,
- `fix` to obtain an ordinary Mealy transition by choosing parameters,
- sequential composition `seq`, which stacks parameters by products.

Bridges to the existing ClosingTheLoop Mealy definition live in
`HeytingLean.CDL.Coalgebra.MealyBridge`.
-/

namespace HeytingLean
namespace CDL
namespace Coalgebra

universe u

open HeytingLean.CDL.Para

/-! ## Endofunctor for Mealy coalgebras -/

/-- Endofunctor for Mealy machines: `F(X) = I → X × O`. -/
def MealyF (I O : Type u) (X : Type u) : Type u :=
  I → X × O

/-! ## Parametric Mealy machines -/

/-- A Mealy machine in `Para(Type)`:
parameters `P` and a transition function `P × I × S → S × O`. -/
structure ParaMealy (I O S : Type u) where
  P : Type u
  transition : P × I × S → S × O

namespace ParaMealy

variable {I O S : Type u}

/-- Reparameterize a parametric Mealy machine along `r : P' → P`. -/
def reparam (m : ParaMealy I O S) {P' : Type u} (r : P' → m.P) : ParaMealy I O S :=
  { P := P'
    transition := fun
      | (p', i, s) => m.transition (r p', i, s) }

/-- Fix parameters to obtain an ordinary (non-parametric) Mealy transition. -/
def fix (m : ParaMealy I O S) (p : m.P) : I × S → S × O :=
  fun (i, s) => m.transition (p, i, s)

/-- View a parametric Mealy machine as a `ParaHom` coalgebra `S ⟶ (I → S × O)`. -/
def toParaHom (m : ParaMealy I O S) : ParaHom S (MealyF I O S) :=
  ⟨m.P, fun | (p, s) => fun i => m.transition (p, i, s)⟩

/-- Build a parametric Mealy machine from a `ParaHom` coalgebra `S ⟶ (I → S × O)`. -/
def ofParaHom (m : ParaHom S (MealyF I O S)) : ParaMealy I O S :=
  { P := m.P
    transition := fun
      | (p, i, s) =>
          let step := m.f (p, s)
          step i }

@[simp] theorem ofParaHom_P (m : ParaHom S (MealyF I O S)) :
    (ofParaHom (I := I) (O := O) (S := S) m).P = m.P := rfl

@[simp] theorem toParaHom_P (m : ParaMealy I O S) :
    (toParaHom (I := I) (O := O) (S := S) m).P = m.P := rfl

@[simp] theorem of_toParaHom (m : ParaMealy I O S) :
    ofParaHom (I := I) (O := O) (S := S) (toParaHom m) = m := by
  cases m with
  | mk P tr =>
    rfl

@[simp] theorem to_ofParaHom (m : ParaHom S (MealyF I O S)) :
    toParaHom (I := I) (O := O) (S := S) (ofParaHom (I := I) (O := O) (S := S) m) = m := by
  cases m with
  | mk P f =>
    rfl

@[simp] theorem toParaHom_reparam (m : ParaMealy I O S) {P' : Type u} (r : P' → m.P) :
    toParaHom (I := I) (O := O) (S := S) (reparam (I := I) (O := O) (S := S) m r) =
      ParaHom.reparam (toParaHom (I := I) (O := O) (S := S) m) r := rfl

/-! ## Sequential composition -/

variable {I₁ I₂ I₃ : Type u} {S₁ S₂ S₃ : Type u}

/-- Sequential composition: run `m1`, feed its output alphabet into `m2`.

Parameters stack by product and the composite state is a product. -/
def seq (m1 : ParaMealy I₁ I₂ S₁) (m2 : ParaMealy I₂ I₃ S₂) :
    ParaMealy I₁ I₃ (S₁ × S₂) :=
  { P := m1.P × m2.P
    transition := fun
      | ((p1, p2), i, (s1, s2)) =>
          let (s1', o1) := m1.transition (p1, i, s1)
          let (s2', o2) := m2.transition (p2, o1, s2)
          ((s1', s2'), o2) }

@[simp] theorem seq_P (m1 : ParaMealy I₁ I₂ S₁) (m2 : ParaMealy I₂ I₃ S₂) :
    (seq m1 m2).P = (m1.P × m2.P) := rfl

/-! ## Weight tying for 2-step unrolling (endo-alphabet case) -/

/-- A 2-step unroll of a Mealy machine with **tied** parameters, obtained by diagonal reparameterization.

This version is for the common “endo-alphabet” case `I → I` (so that we can feed the output back in). -/
def unroll2_tied (m : ParaMealy I₁ I₁ S₁) : ParaMealy I₁ I₁ (S₁ × S₁) :=
  reparam (I := I₁) (O := I₁) (S := S₁ × S₁) (seq m m) (fun p => (p, p))

/-- A `Para2Hom` witness (at the `ParaHom` coalgebra level) that 2-step unrolling ties by the diagonal. -/
def unroll2_ties (m : ParaMealy I₁ I₁ S₁) :
    Para2Hom (toParaHom (I := I₁) (O := I₁) (S := S₁ × S₁) (seq m m))
      (toParaHom (I := I₁) (O := I₁) (S := S₁ × S₁) (unroll2_tied (I₁ := I₁) (S₁ := S₁) m)) :=
  Para2Hom.reparam (m := toParaHom (I := I₁) (O := I₁) (S := S₁ × S₁) (seq m m)) (fun p => (p, p))

end ParaMealy

end Coalgebra
end CDL
end HeytingLean
