import Mathlib.Data.Set.Basic

namespace HeytingLean
namespace InqBQ

/-- Signature for inquisitive first-order logic with separate rigid and non-rigid function symbols. -/
structure Signature where
  PredSym : Type
  RigidFun : Type
  NonRigidFun : Type
  predArity : PredSym → ℕ
  rigidArity : RigidFun → ℕ
  nonrigidArity : NonRigidFun → ℕ

/-- Terms in an InqBQ signature. Variables are indexed by naturals. -/
inductive Term (sig : Signature) : Type where
  | var : ℕ → Term sig
  | rigidApp (f : sig.RigidFun) (args : Fin (sig.rigidArity f) → Term sig) : Term sig
  | nonrigidApp (f : sig.NonRigidFun) (args : Fin (sig.nonrigidArity f) → Term sig) : Term sig

/-- Primitive InqBQ formulas. -/
inductive Formula (sig : Signature) : Type where
  | pred (P : sig.PredSym) (args : Fin (sig.predArity P) → Term sig) : Formula sig
  | eq : Term sig → Term sig → Formula sig
  | bot : Formula sig
  | conj : Formula sig → Formula sig → Formula sig
  | inqDisj : Formula sig → Formula sig → Formula sig
  | imp : Formula sig → Formula sig → Formula sig
  | forall_ : ℕ → Formula sig → Formula sig
  | inqExists : ℕ → Formula sig → Formula sig

namespace Formula

variable {sig : Signature}

/-- InqBQ negation is implication into bottom. -/
def neg (φ : Formula sig) : Formula sig :=
  .imp φ .bot

/-- Top is the negation of bottom. -/
def top : Formula sig :=
  neg .bot

/-- Classical disjunction defined from negation and conjunction. -/
def classicalOr (φ ψ : Formula sig) : Formula sig :=
  neg (.conj (neg φ) (neg ψ))

/-- Classical existential defined from universal quantification and negation. -/
def classicalExists (x : ℕ) (φ : Formula sig) : Formula sig :=
  neg (.forall_ x (neg φ))

/-- Question operator. -/
def question (φ : Formula sig) : Formula sig :=
  .inqDisj φ (neg φ)

/-- Mention-some identification. Uses variable `0` by default. -/
def identify (t : Term sig) : Formula sig :=
  .inqExists 0 (.eq (.var 0) t)

/-- Mention-all identification. Uses variable `0` by default. -/
def mentionAllIdentify (t : Term sig) : Formula sig :=
  .forall_ 0 (question (.eq (.var 0) t))

/-- Binary dependence atom. -/
def dependence (t u : Term sig) : Formula sig :=
  .imp (identify t) (identify u)

/-- Syntactic predicate for the classical fragment. -/
def isClassical : Formula sig → Prop
  | .pred _ _ => True
  | .eq _ _ => True
  | .bot => True
  | .conj φ ψ => isClassical φ ∧ isClassical ψ
  | .inqDisj _ _ => False
  | .imp φ ψ => isClassical φ ∧ isClassical ψ
  | .forall_ _ φ => isClassical φ
  | .inqExists _ _ => False

end Formula

end InqBQ
end HeytingLean
