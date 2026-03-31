import HeytingLean.Noneism.Syntax

namespace HeytingLean
namespace Noneism
namespace LP

/-- Truth values as "is true" and "is false" flags. -/
structure TV where
  T : Bool
  F : Bool
  deriving DecidableEq, Repr

namespace TV
def designated (v : TV) : Prop := v.T
def not (a : TV) : TV := ⟨a.F, a.T⟩
def and (a b : TV) : TV := ⟨a.T && b.T, a.F || b.F⟩
def or  (a b : TV) : TV := ⟨a.T || b.T, a.F && b.F⟩
def imp (a b : TV) : TV := or (not a) b
end TV

/-- Propositional LP evaluation over predicate symbols `σ`. -/
structure Env (σ : Type) where
  val : σ → TV

open Noneism Formula

def eval {σ} (E : Env σ) : Formula σ → TV
  | .top        => ⟨true, false⟩
  | .bot        => ⟨false, true⟩
  | .pred p _   => E.val p
  | .eExists _  => ⟨false, false⟩   -- outside propositional fragment
  | .not φ      => TV.not (eval E φ)
  | .and φ ψ    => TV.and (eval E φ) (eval E ψ)
  | .or  φ ψ    => TV.or  (eval E φ) (eval E ψ)
  | .imp φ ψ    => TV.imp (eval E φ) (eval E ψ)
  | .sigma _ _  => ⟨false, false⟩
  | .pi    _ _  => ⟨false, false⟩

/-- Designated satisfaction in LP for a given environment. -/
def Holds {σ} (E : Env σ) (φ : Formula σ) : Prop :=
  TV.designated (eval E φ)

/-- Entailment: Γ entails φ if every environment that designates all of Γ also designates φ. -/
def Entails {σ} (Γ : List (Formula σ)) (φ : Formula σ) : Prop :=
  ∀ E : Env σ, (∀ ψ ∈ Γ, Holds E ψ) → Holds E φ

/-- A simple countervaluation: A is both-true, B is false-only. -/
inductive Atom where | A | B deriving DecidableEq, Repr, Inhabited

def counterEnv : Env Atom :=
  { val := fun
      | .A => ⟨true, true⟩
      | .B => ⟨false, true⟩ }

def A : Formula Atom := .pred .A []
def B : Formula Atom := .pred .B []

/-- In the counter environment, `A ∧ ¬A` is designated (both true). -/
theorem contradiction_designated :
    TV.designated (eval counterEnv (.and A (.not A))) := by
  simp [eval, A, TV.designated, TV.and, TV.not, counterEnv]

/-- In the counter environment, `B` is not designated. -/
theorem b_not_designated :
    ¬ TV.designated (eval counterEnv B) := by
  simp [eval, B, TV.designated, counterEnv]

end LP
end Noneism
end HeytingLean
