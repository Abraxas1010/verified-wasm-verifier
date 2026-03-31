import Mathlib.CategoryTheory.Category.Basic

/-!
# Util.VirtualChain

A reusable “virtualization” pattern: represent a composite as a **chain of steps** rather than
an actual composed arrow.

This is useful when:
- you want to reason about an effective `a ⟶ c` without constructing a single “pasted” morphism;
- you want explicit provenance/audit trails of intermediate steps;
- composition/coherence is expensive or not yet formalized.

The key is that `VirtualChain Step` itself forms a category:
- identities are empty chains;
- composition is append;
- associativity/identity laws are by induction.
-/

namespace HeytingLean
namespace Util

open CategoryTheory

universe u v

/-- A formal composite of `Step`s from `a` to `b`. Always lives in `Type` (never `Prop`). -/
inductive VirtualChain {α : Type u} (Step : α → α → Sort v) : α → α → Type (max u v)
  | nil (a : α) : VirtualChain Step a a
  | cons {a b c : α} : Step a b → VirtualChain Step b c → VirtualChain Step a c

namespace VirtualChain

variable {α : Type u} {Step : α → α → Sort v}

def length {a b : α} : VirtualChain Step a b → Nat
  | nil _ => 0
  | cons _ rest => rest.length.succ

def append {a b c : α} : VirtualChain Step a b → VirtualChain Step b c → VirtualChain Step a c
  | nil _, q => q
  | cons h p, q => cons h (append p q)

@[simp] theorem append_nil_left {a b : α} (p : VirtualChain Step a b) :
    append (VirtualChain.nil a) p = p := by
  rfl

@[simp] theorem append_nil_right {a b : α} (p : VirtualChain Step a b) :
    append p (VirtualChain.nil b) = p := by
  induction p with
  | nil a =>
      rfl
  | cons h rest ih =>
      simp [append, ih]

@[simp] theorem append_assoc {a b c d : α}
    (p : VirtualChain Step a b) (q : VirtualChain Step b c) (r : VirtualChain Step c d) :
    append (append p q) r = append p (append q r) := by
  induction p with
  | nil a =>
      rfl
  | cons h rest ih =>
      simp [append, ih]

instance category (α : Type u) (Step : α → α → Sort v) : Category α where
  Hom a b := VirtualChain Step a b
  id a := VirtualChain.nil a
  comp p q := VirtualChain.append p q
  id_comp := by intro a b p; simp
  comp_id := by intro a b p; simp
  assoc := by intro a b c d p q r; simp [VirtualChain.append_assoc]

end VirtualChain

end Util
end HeytingLean
