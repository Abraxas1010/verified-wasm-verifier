import HeytingLean.Chem.PeriodicTable.CIAAW2024
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Sort

/-!
# SLICES: Labeled quotient graphs (Phase 1)

This file defines a minimal combinatorial model of a periodic crystal as a finite **labeled
quotient graph**:

- nodes represent atoms in the unit cell (labeled by `Element`)
- edges represent bonds/adjacencies, labeled by a translation vector in `Z^3`

This is the core data model used by the SLICES string codec and canonicalization layers.
-/

namespace HeytingLean.Chem.Materials.SLICES

open HeytingLean.Chem.PeriodicTable

/-! ## Translation vectors -/

structure TranslationVec where
  x : Int
  y : Int
  z : Int
deriving Repr, DecidableEq

namespace TranslationVec

@[simp] theorem ext {a b : TranslationVec} (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  cases a
  cases b
  cases hx
  cases hy
  cases hz
  rfl

def cmp (a b : TranslationVec) : Ordering :=
  match compare a.x b.x with
  | .lt => .lt
  | .gt => .gt
  | .eq =>
    match compare a.y b.y with
    | .lt => .lt
    | .gt => .gt
    | .eq => compare a.z b.z

def leBool (a b : TranslationVec) : Bool :=
  match cmp a b with
  | .gt => false
  | _ => true

end TranslationVec

/-! ## Edges and graphs -/

structure Edge (n : Nat) where
  u : Fin n
  v : Fin n
  t : TranslationVec
deriving Repr, DecidableEq

namespace Edge

def cmp {n : Nat} (a b : Edge n) : Ordering :=
  match compare a.u.val b.u.val with
  | .lt => .lt
  | .gt => .gt
  | .eq =>
    match compare a.v.val b.v.val with
    | .lt => .lt
    | .gt => .gt
    | .eq => TranslationVec.cmp a.t b.t

def leBool {n : Nat} (a b : Edge n) : Bool :=
  match cmp a b with
  | .gt => false
  | _ => true

def map {n : Nat} (π : Equiv.Perm (Fin n)) (e : Edge n) : Edge n :=
  { u := π e.u
    v := π e.v
    t := e.t }

theorem map_injective {n : Nat} (π : Equiv.Perm (Fin n)) : Function.Injective (map π) := by
  intro a b h
  cases a with
  | mk au av t0 =>
    cases b with
    | mk bu bv bt =>
      have hu' : π au = π bu := congrArg Edge.u h
      have hv' : π av = π bv := congrArg Edge.v h
      have ht : t0 = bt := congrArg Edge.t h
      have hu : au = bu := π.injective hu'
      have hv : av = bv := π.injective hv'
      cases hu
      cases hv
      cases ht
      rfl

end Edge

structure LabeledQuotientGraph (n : Nat) where
  labels : Fin n → Element
  edges : Finset (Edge n)

namespace LabeledQuotientGraph

@[ext] theorem ext {n : Nat} {g h : LabeledQuotientGraph n}
    (hl : ∀ i, g.labels i = h.labels i) (he : g.edges = h.edges) : g = h := by
  cases g with
  | mk gl ge =>
    cases h with
    | mk hlab heds =>
      cases he
      have hlabels : gl = hlab := by
        funext i
        exact hl i
      cases hlabels
      rfl

def permute {n : Nat} (g : LabeledQuotientGraph n) (π : Equiv.Perm (Fin n)) : LabeledQuotientGraph n :=
  { labels := fun i => g.labels (π.symm i)
    edges :=
      g.edges.map
        ⟨fun e => Edge.map π e, Edge.map_injective π⟩ }

@[simp] theorem perm_symm_mul_apply {n : Nat} (σ π : Equiv.Perm (Fin n)) (i : Fin n) :
    (σ * π).symm i = π.symm (σ.symm i) := by
  rfl

@[simp] theorem permute_labels {n : Nat} (g : LabeledQuotientGraph n) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (g.permute π).labels i = g.labels (π.symm i) :=
  rfl

@[simp] theorem permute_edges {n : Nat} (g : LabeledQuotientGraph n) (π : Equiv.Perm (Fin n)) :
    (g.permute π).edges = g.edges.map ⟨fun e => Edge.map π e, Edge.map_injective π⟩ :=
  rfl

@[simp] theorem permute_one {n : Nat} (g : LabeledQuotientGraph n) :
    g.permute (Equiv.refl (Fin n)) = g := by
  apply LabeledQuotientGraph.ext (g := g.permute (Equiv.refl (Fin n))) (h := g)
  · intro i
    simp [LabeledQuotientGraph.permute]
  · classical
    -- `Finset.map` with an identity embedding.
    ext e
    constructor
    · intro he
      rcases Finset.mem_map.1 he with ⟨e0, he0, rfl⟩
      simpa [Edge.map] using he0
    · intro he
      exact Finset.mem_map.2 ⟨e, he, by simp [Edge.map]⟩

@[simp] theorem permute_mul {n : Nat} (g : LabeledQuotientGraph n) (π σ : Equiv.Perm (Fin n)) :
    (g.permute π).permute σ = g.permute (σ * π) := by
  classical
  apply LabeledQuotientGraph.ext (g := (g.permute π).permute σ) (h := g.permute (σ * π))
  · intro i
    -- `symm` of a composition of permutations reverses the order.
    simp [LabeledQuotientGraph.permute]
  · -- Use `Finset.map_map` to compose the embeddings on edges.
    let embπ : Edge n ↪ Edge n := ⟨fun e => Edge.map π e, Edge.map_injective π⟩
    let embσ : Edge n ↪ Edge n := ⟨fun e => Edge.map σ e, Edge.map_injective σ⟩
    let emb : Edge n ↪ Edge n := ⟨fun e => Edge.map (σ * π) e, Edge.map_injective (σ * π)⟩
    have htrans : embπ.trans embσ = emb := by
      ext e
      simp [embπ, embσ, emb, Edge.map]
    simpa [LabeledQuotientGraph.permute, embπ, embσ, emb, htrans] using
      (Finset.map_map embπ embσ g.edges)

end LabeledQuotientGraph

end HeytingLean.Chem.Materials.SLICES
