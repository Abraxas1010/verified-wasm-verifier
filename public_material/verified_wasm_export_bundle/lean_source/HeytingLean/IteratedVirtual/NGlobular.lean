import Mathlib.CategoryTheory.Category.Basic

/-!
# IteratedVirtual.NGlobular

A **truncated** globular-set interface up to dimension `n` (using `Nat` indices with explicit
`k < n` guards for the structure maps).

This avoids the “ω-category needs (n+1)-cells to even talk about n-cells” pitfall while keeping
the API very small.
-/

namespace HeytingLean
namespace IteratedVirtual

universe u

/-- A globular set truncated to dimensions `0..n` (only the structure maps up to `< n` are required). -/
structure NGlobularSet (n : Nat) where
  Cell : Nat → Type u
  src : ∀ k : Nat, k < n → Cell (k + 1) → Cell k
  tgt : ∀ k : Nat, k < n → Cell (k + 1) → Cell k
  src_src_eq_src_tgt :
      ∀ k : Nat, ∀ hk0 : k < n, ∀ hk1 : k + 1 < n, ∀ x : Cell (k + 2),
        src k hk0 (src (k + 1) hk1 x) = src k hk0 (tgt (k + 1) hk1 x)
  tgt_src_eq_tgt_tgt :
      ∀ k : Nat, ∀ hk0 : k < n, ∀ hk1 : k + 1 < n, ∀ x : Cell (k + 2),
        tgt k hk0 (src (k + 1) hk1 x) = tgt k hk0 (tgt (k + 1) hk1 x)

namespace NGlobularSet

/-- Restrict a truncated globular set further down to dimension `k ≤ n`. -/
def restrict {n : Nat} (X : NGlobularSet n) (k : Nat) (hk : k ≤ n) : NGlobularSet k where
  Cell := fun m => if m ≤ k then X.Cell m else PUnit
  src := by
    intro i hi x
    have hi0 : i ≤ k := Nat.le_of_lt hi
    have hi1 : i + 1 ≤ k := Nat.succ_le_of_lt hi
    have x' : X.Cell (i + 1) := by simpa [if_pos hi1] using x
    have y : X.Cell i := X.src i (Nat.lt_of_lt_of_le hi hk) x'
    exact (by simpa [if_pos hi0] using y)
  tgt := by
    intro i hi x
    have hi0 : i ≤ k := Nat.le_of_lt hi
    have hi1 : i + 1 ≤ k := Nat.succ_le_of_lt hi
    have x' : X.Cell (i + 1) := by simpa [if_pos hi1] using x
    have y : X.Cell i := X.tgt i (Nat.lt_of_lt_of_le hi hk) x'
    exact (by simpa [if_pos hi0] using y)
  src_src_eq_src_tgt := by
    intro i hi0 hi1 x
    have hi0' : i ≤ k := Nat.le_of_lt hi0
    have hi2 : i + 2 ≤ k := by
      have : i + 1 < k := hi1
      exact Nat.succ_le_of_lt this
    let x' : X.Cell (i + 2) := cast (by simp [if_pos hi2]) x
    have hx :
        X.src i (Nat.lt_of_lt_of_le hi0 hk) (X.src (i + 1) (Nat.lt_of_lt_of_le hi1 hk) x') =
          X.src i (Nat.lt_of_lt_of_le hi0 hk) (X.tgt (i + 1) (Nat.lt_of_lt_of_le hi1 hk) x') :=
      X.src_src_eq_src_tgt i (Nat.lt_of_lt_of_le hi0 hk) (Nat.lt_of_lt_of_le hi1 hk) x'
    -- Coerce the equality back into the restricted cell types (both sides live in `X.Cell i`).
    simpa [if_pos hi0', x'] using hx
  tgt_src_eq_tgt_tgt := by
    intro i hi0 hi1 x
    have hi0' : i ≤ k := Nat.le_of_lt hi0
    have hi2 : i + 2 ≤ k := by
      have : i + 1 < k := hi1
      exact Nat.succ_le_of_lt this
    let x' : X.Cell (i + 2) := cast (by simp [if_pos hi2]) x
    have hx :
        X.tgt i (Nat.lt_of_lt_of_le hi0 hk) (X.src (i + 1) (Nat.lt_of_lt_of_le hi1 hk) x') =
          X.tgt i (Nat.lt_of_lt_of_le hi0 hk) (X.tgt (i + 1) (Nat.lt_of_lt_of_le hi1 hk) x') :=
      X.tgt_src_eq_tgt_tgt i (Nat.lt_of_lt_of_le hi0 hk) (Nat.lt_of_lt_of_le hi1 hk) x'
    simpa [if_pos hi0', x'] using hx

/-- Morphisms of truncated globular sets. -/
structure Hom {n : Nat} (X Y : NGlobularSet n) where
  map : ∀ k : Nat, X.Cell k → Y.Cell k
  map_src :
      ∀ k : Nat, ∀ hk : k < n, ∀ x : X.Cell (k + 1),
        map k (X.src k hk x) = Y.src k hk (map (k + 1) x)
  map_tgt :
      ∀ k : Nat, ∀ hk : k < n, ∀ x : X.Cell (k + 1),
        map k (X.tgt k hk x) = Y.tgt k hk (map (k + 1) x)

attribute [simp] Hom.map_src Hom.map_tgt

@[ext] theorem Hom.ext {n : Nat} {X Y : NGlobularSet n} {f g : Hom X Y}
    (h : ∀ k : Nat, ∀ x : X.Cell k, f.map k x = g.map k x) : f = g := by
  cases f with
  | mk fmap fsrc ftgt =>
    cases g with
    | mk gmap gsrc gtgt =>
      have hm : fmap = gmap := by
        funext k x
        exact h k x
      subst hm
      have hsrc : fsrc = gsrc := by
        funext k hk x
        exact Subsingleton.elim (fsrc k hk x) (gsrc k hk x)
      have htgt : ftgt = gtgt := by
        funext k hk x
        exact Subsingleton.elim (ftgt k hk x) (gtgt k hk x)
      subst hsrc
      subst htgt
      rfl

def Hom.id {n : Nat} (X : NGlobularSet n) : Hom X X :=
  { map := fun _ x => x
    map_src := by intro k hk x; rfl
    map_tgt := by intro k hk x; rfl }

def Hom.comp {n : Nat} {X Y Z : NGlobularSet n} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  { map := fun k => g.map k ∘ f.map k
    map_src := by
      intro k hk x
      calc
        g.map k (f.map k (X.src k hk x)) = g.map k (Y.src k hk (f.map (k + 1) x)) := by
          exact congrArg (g.map k) (f.map_src k hk x)
        _ = Z.src k hk (g.map (k + 1) (f.map (k + 1) x)) := by
          exact g.map_src k hk (f.map (k + 1) x)
    map_tgt := by
      intro k hk x
      calc
        g.map k (f.map k (X.tgt k hk x)) = g.map k (Y.tgt k hk (f.map (k + 1) x)) := by
          exact congrArg (g.map k) (f.map_tgt k hk x)
        _ = Z.tgt k hk (g.map (k + 1) (f.map (k + 1) x)) := by
          exact g.map_tgt k hk (f.map (k + 1) x) }

instance {n : Nat} : CategoryTheory.Category (NGlobularSet n) where
  Hom X Y := Hom X Y
  id X := Hom.id X
  comp f g := Hom.comp f g
  id_comp := by
    intro X Y f
    ext k x
    rfl
  comp_id := by
    intro X Y f
    ext k x
    rfl
  assoc := by
    intro W X Y Z f g h
    ext k x
    rfl

end NGlobularSet

end IteratedVirtual
end HeytingLean
