import HeytingLean.LeanCore.Syntax
import HeytingLean.LeanCore.Primitives

namespace HeytingLean
namespace LeanCore

open Classical

mutual
  inductive Value : Ty → Type where
    | vlam {α β} (body : Term β) (env : Env) : Value (Ty.arrow α β)
    | vpair {α β} (v₁ : Value α) (v₂ : Value β) : Value (Ty.prod α β)
    | vinl  {α β} (v : Value α) : Value (Ty.sum α β)
    | vinr  {α β} (v : Value β) : Value (Ty.sum α β)
    | vnat  : Nat → Value (Ty.base .nat)
    | vbool : Bool → Value (Ty.base .bool)
    | vsucc : Value (Ty.arrow (Ty.base .nat) (Ty.base .nat))
  inductive Env : Type where
    | nil : Env
    | cons : {τ : Ty} → Value τ → Env → Env
end

namespace Env

/-- Empty runtime environment. -/
def empty : Env := Env.nil

/-- Extend an environment with a freshly bound value. -/
def extend {τ : Ty} (v : Value τ) (ρ : Env) : Env := Env.cons v ρ

/-- Lookup a value stored at the given de Bruijn index. -/
@[simp] def lookup : Env → Nat → Option (Sigma fun τ => Value τ)
  | Env.nil, _ => none
  | Env.cons (τ:=τ) v _, 0 => some ⟨τ, v⟩
  | Env.cons _ tail, Nat.succ idx => lookup tail idx

end Env

structure PrimSem where
  sig   : PrimSig
  value : Value sig.ty

abbrev PrimSemEnv := List PrimSem

namespace PrimSemEnv

/-- Find the semantic value for a primitive name. -/
def lookup (env : PrimSemEnv) (name : String) : Option (Sigma fun τ => Value τ) := do
  let sem ← env.find? (fun entry => entry.sig.name = name)
  pure ⟨sem.sig.ty, sem.value⟩

/-- Default primitive semantics aligned with `PrimEnv.default`. -/
def default : PrimSemEnv :=
  { sig := { name := "zero", ty := Ty.base .nat }, value := Value.vnat 0 } ::
  { sig := { name := "succ", ty := Ty.arrow (Ty.base .nat) (Ty.base .nat) }
  , value := Value.vsucc } ::
  { sig := { name := "true", ty := Ty.base .bool }, value := Value.vbool true } ::
  { sig := { name := "false", ty := Ty.base .bool }, value := Value.vbool false } ::
  []

end PrimSemEnv

private def evalFuel (fuel : Nat) (prims : PrimSemEnv) (ρ : Env) {τ} (t : Term τ) : Option (Value τ) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match t with
      | Term.var idx => do
          let ⟨ty, v⟩ ← Env.lookup ρ idx
          if h : ty = τ then
            match h with
            | rfl => pure v
          else
            none
      | Term.lam body =>
          pure (Value.vlam body ρ)
      | Term.app f x => do
          let vf ← evalFuel fuel prims ρ f
          let vx ← evalFuel fuel prims ρ x
          match vf with
          | Value.vlam body closEnv =>
              evalFuel fuel prims (Env.extend vx closEnv) body
          | Value.vsucc =>
              match vx with
              | Value.vnat n => pure (Value.vnat (n + 1))
      | Term.pair t₁ t₂ => do
          let v₁ ← evalFuel fuel prims ρ t₁
          let v₂ ← evalFuel fuel prims ρ t₂
          pure (Value.vpair v₁ v₂)
      | Term.fst t => do
          match ← evalFuel fuel prims ρ t with
          | Value.vpair v₁ _ => pure v₁
      | Term.snd t => do
          match ← evalFuel fuel prims ρ t with
          | Value.vpair _ v₂ => pure v₂
      | Term.inl t => do
          let v ← evalFuel fuel prims ρ t
          pure (Value.vinl v)
      | Term.inr t => do
          let v ← evalFuel fuel prims ρ t
          pure (Value.vinr v)
      | Term.matchSum scrut k₁ k₂ => do
          match ← evalFuel fuel prims ρ scrut with
          | Value.vinl _ => evalFuel fuel prims ρ k₁
          | Value.vinr _ => evalFuel fuel prims ρ k₂
      | Term.const name => do
          let ⟨ty, val⟩ ← PrimSemEnv.lookup prims name
          if h : ty = τ then
            match h with
            | rfl => pure val
          else
            none

def eval (prims : PrimSemEnv) (ρ : Env) {τ} (t : Term τ) : Option (Value τ) :=
  evalFuel 10000 prims ρ t

/-- Evaluate a closed term under the empty environment and a primitive set. -/
def evalClosed (prims : PrimSemEnv := PrimSemEnv.default) {τ} (t : Term τ) : Option (Value τ) :=
  eval prims Env.empty t

end LeanCore
end HeytingLean
