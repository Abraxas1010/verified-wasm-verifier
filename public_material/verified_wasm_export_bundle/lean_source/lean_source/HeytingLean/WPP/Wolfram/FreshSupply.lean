import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Vector.Mem

namespace HeytingLean
namespace WPP
namespace Wolfram

/-!
# Fresh vertex supply (polymorphic)

Wolfram-model / SetReplace rewriting typically introduces **fresh** vertices when a rule's RHS
mentions vertices not bound by the match. We model the required capability as a typeclass:
given a finite set of already-used vertices, produce one not in that set.

We keep this polymorphic in the vertex type `V`. When `V` is infinite, we provide a
noncomputable default instance via classical choice.
-/

universe u

/-- A supply of fresh vertices for `V`: given a finite set of used vertices, produce a new one. -/
class FreshSupply (V : Type u) [DecidableEq V] : Type u where
  fresh : Finset V → V
  fresh_not_mem : ∀ s : Finset V, fresh s ∉ s

namespace FreshSupply

variable {V : Type u} [DecidableEq V] [FreshSupply V]

@[simp] lemma fresh_not_mem' (s : Finset V) : FreshSupply.fresh s ∉ s :=
  FreshSupply.fresh_not_mem (V := V) s

/-- Allocate `n` fresh vertices, extending the forbidden set as we go. -/
noncomputable def allocList : Nat → Finset V → List V
  | 0, _forbidden => []
  | n + 1, forbidden =>
      let v := FreshSupply.fresh forbidden
      v :: allocList n (insert v forbidden)

@[simp] lemma allocList_length (n : Nat) (forbidden : Finset V) :
    (allocList (V := V) n forbidden).length = n := by
  induction n generalizing forbidden with
  | zero => simp [allocList]
  | succ n ih =>
      simp [allocList, ih]

lemma allocList_mem_not_mem_forbidden {n : Nat} {forbidden : Finset V} {v : V} :
    v ∈ allocList (V := V) n forbidden → v ∉ forbidden := by
  classical
  induction n generalizing forbidden with
  | zero =>
      intro hv
      simp [allocList] at hv
  | succ n ih =>
      intro hv
      simp [allocList] at hv
      rcases hv with hv | hv
      · subst hv
        exact FreshSupply.fresh_not_mem (V := V) forbidden
      · have hnot : v ∉ insert (FreshSupply.fresh forbidden) forbidden :=
          ih (forbidden := insert (FreshSupply.fresh forbidden) forbidden) hv
        exact fun hmem => hnot (by simpa [Finset.mem_insert] using Or.inr hmem)

lemma allocList_nodup (n : Nat) (forbidden : Finset V) :
    (allocList (V := V) n forbidden).Nodup := by
  classical
  induction n generalizing forbidden with
  | zero =>
      simp [allocList]
  | succ n ih =>
      simp [allocList]
      refine ⟨?_, ih (forbidden := insert (FreshSupply.fresh forbidden) forbidden)⟩
      intro hmem
      have htail :
          FreshSupply.fresh forbidden ∉ insert (FreshSupply.fresh forbidden) forbidden :=
        allocList_mem_not_mem_forbidden (V := V) (n := n)
          (forbidden := insert (FreshSupply.fresh forbidden) forbidden)
          (v := FreshSupply.fresh forbidden) hmem
      exact htail (by simp)

/-- Allocate `n` fresh vertices as a length-`n` vector. -/
noncomputable def allocVec (n : Nat) (forbidden : Finset V) : List.Vector V n :=
  ⟨allocList (V := V) n forbidden, allocList_length (V := V) n forbidden⟩

/-- The corresponding fresh assignment function `Fin n → V`. -/
noncomputable def alloc (n : Nat) (forbidden : Finset V) : Fin n → V :=
  (allocVec (V := V) n forbidden).get

lemma alloc_injective (n : Nat) (forbidden : Finset V) :
    Function.Injective (alloc (V := V) n forbidden) := by
  classical
  have hnodup : (allocVec (V := V) n forbidden).toList.Nodup := by
    simpa [allocVec] using allocList_nodup (V := V) n forbidden
  exact (List.Vector.nodup_iff_injective_get).1 hnodup

lemma alloc_not_mem (n : Nat) (forbidden : Finset V) (i : Fin n) :
    alloc (V := V) n forbidden i ∉ forbidden := by
  have hi : alloc (V := V) n forbidden i ∈ allocList (V := V) n forbidden := by
    -- `Vector.get_mem` gives membership in the underlying list.
    simpa [alloc, allocVec] using (List.Vector.get_mem i (allocVec (V := V) n forbidden))
  exact allocList_mem_not_mem_forbidden (V := V) (n := n) (forbidden := forbidden) (v := alloc (V := V) n forbidden i) hi

end FreshSupply

/-- Any infinite type admits a (noncomputable) fresh-supply instance. -/
noncomputable instance instFreshSupply_ofInfinite (V : Type u) [DecidableEq V] [Infinite V] :
    FreshSupply V where
  fresh s := Classical.choose (Finset.exists_notMem s)
  fresh_not_mem s := Classical.choose_spec (Finset.exists_notMem s)

end Wolfram
end WPP
end HeytingLean
