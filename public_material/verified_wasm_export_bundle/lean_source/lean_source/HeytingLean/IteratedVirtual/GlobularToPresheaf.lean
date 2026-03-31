import HeytingLean.IteratedVirtual.Globular
import HeytingLean.IteratedVirtual.GlobularIndex
import HeytingLean.IteratedVirtual.GlobularPresheaf

/-!
# IteratedVirtual.GlobularToPresheaf

Bridge: the minimal structured `GlobularSet` record induces a presheaf globular set
`GlobularSetPsh := GlobularIndexᵒᵖ ⥤ Type`.

This is the “other direction” complementing `IteratedVirtual/GlobularFromPresheaf.lean`.

Why this matters (Phase 8):
- We already use the presheaf presentation (`GlobularSetPsh`, `GlobePsh`, `kCellPsh`) as the
  canonical “walking globe” semantics.
- Large parts of IteratedVirtual still consume the small record `GlobularSet`.
  This file gives a strict-only conversion so we can migrate incrementally.
-/

namespace HeytingLean
namespace IteratedVirtual

open CategoryTheory

namespace GlobularSet

universe u

variable {X : GlobularSet.{u}}

/-- Iterated `src` from level `n` down to `m` (canonical choice: always `src` at each step). -/
def downSrc (X : GlobularSet.{u}) : ∀ (m n : Nat), m ≤ n → X.Cell n → X.Cell m
  | m, 0, hm => by
      intro x
      have : m = 0 := Nat.eq_zero_of_le_zero hm
      subst this
      exact x
  | m, n + 1, hm => by
      intro x
      by_cases hmn : m = n + 1
      · subst hmn
        exact x
      · have hm' : m ≤ n := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hm hmn)
        exact downSrc X m n hm' (X.src x)

/-- Iterated `tgt` from level `n` down to `m` (canonical choice: always `tgt` at each step). -/
def downTgt (X : GlobularSet.{u}) : ∀ (m n : Nat), m ≤ n → X.Cell n → X.Cell m
  | m, 0, hm => by
      intro x
      have : m = 0 := Nat.eq_zero_of_le_zero hm
      subst this
      exact x
  | m, n + 1, hm => by
      intro x
      by_cases hmn : m = n + 1
      · subst hmn
        exact x
      · have hm' : m ≤ n := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hm hmn)
        exact downTgt X m n hm' (X.tgt x)

@[simp] theorem downSrc_self (X : GlobularSet.{u}) (n : Nat) (x : X.Cell n) :
    downSrc X n n (Nat.le_refl n) x = x := by
  cases n with
  | zero => rfl
  | succ n =>
      simp [downSrc]

@[simp] theorem downTgt_self (X : GlobularSet.{u}) (n : Nat) (x : X.Cell n) :
    downTgt X n n (Nat.le_refl n) x = x := by
  cases n with
  | zero => rfl
  | succ n =>
      simp [downTgt]

/-!
## Key “independence” lemma

When you push a cell down below a level `m < n`, the `m`-boundary is independent of whether you
take `src` or `tgt` at level `n`.
-/

theorem downSrc_src_eq_downSrc_tgt (X : GlobularSet.{u}) {m n : Nat} (hmn : m < n)
    (x : X.Cell (n + 1)) :
    downSrc X m n (Nat.le_of_lt hmn) (X.src x) = downSrc X m n (Nat.le_of_lt hmn) (X.tgt x) := by
  -- Unfold one `downSrc` step (since `m ≠ n`) and use the globular relation at level `n-1`.
  cases n with
  | zero =>
      cases Nat.not_lt_zero m hmn
  | succ n =>
      have hmne : m ≠ n.succ := Nat.ne_of_lt hmn
      have hm' : m ≤ n := Nat.le_of_lt_succ hmn
      -- Both sides reduce to `downSrc X m n hm' (src (src x))` / `downSrc ... (src (tgt x))`.
      simp [downSrc, hmne, X.src_src_eq_src_tgt (n := n) x]

theorem downTgt_src_eq_downTgt_tgt (X : GlobularSet.{u}) {m n : Nat} (hmn : m < n)
    (x : X.Cell (n + 1)) :
    downTgt X m n (Nat.le_of_lt hmn) (X.src x) = downTgt X m n (Nat.le_of_lt hmn) (X.tgt x) := by
  cases n with
  | zero =>
      cases Nat.not_lt_zero m hmn
  | succ n =>
      have hmne : m ≠ n.succ := Nat.ne_of_lt hmn
      have hm' : m ≤ n := Nat.le_of_lt_succ hmn
      simp [downTgt, hmne, X.tgt_src_eq_tgt_tgt (n := n) x]

/-!
## Composition lemmas for `downSrc`/`downTgt`

These are exactly what we need to prove functoriality for the presheaf conversion, because
`GlobularIndex` has **left-biased** composition encoding the globular relations.
-/

theorem downSrc_comp_downSrc (X : GlobularSet.{u}) {m n p : Nat}
    (hmn : m ≤ n) (hnp : n ≤ p) (x : X.Cell p) :
    downSrc X m n hmn (downSrc X n p hnp x) = downSrc X m p (Nat.le_trans hmn hnp) x := by
  revert x
  induction p with
  | zero =>
      intro x
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hnp
      subst hn0
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst hm0
      simp [downSrc]
  | succ p ih =>
      intro x
      by_cases hp : n = p.succ
      · subst hp
        have hhnp : hnp = Nat.le_refl p.succ := Subsingleton.elim _ _
        cases hhnp
        simp [downSrc_self]
      · have hnp' : n ≤ p := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hnp hp)
        have hmp' : m ≤ p := Nat.le_trans hmn hnp'
        have hmne : m ≠ p.succ := Nat.ne_of_lt (Nat.lt_of_le_of_lt hmp' (Nat.lt_succ_self p))
        -- Peel one step from the top and apply IH to `X.src x`.
        simp [downSrc, hp, hmne, ih (hnp := hnp') (x := X.src x)]

theorem downTgt_comp_downTgt (X : GlobularSet.{u}) {m n p : Nat}
    (hmn : m ≤ n) (hnp : n ≤ p) (x : X.Cell p) :
    downTgt X m n hmn (downTgt X n p hnp x) = downTgt X m p (Nat.le_trans hmn hnp) x := by
  revert x
  induction p with
  | zero =>
      intro x
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hnp
      subst hn0
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst hm0
      simp [downTgt]
  | succ p ih =>
      intro x
      by_cases hp : n = p.succ
      · subst hp
        have hhnp : hnp = Nat.le_refl p.succ := Subsingleton.elim _ _
        cases hhnp
        simp [downTgt_self]
      · have hnp' : n ≤ p := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hnp hp)
        have hmp' : m ≤ p := Nat.le_trans hmn hnp'
        have hmne : m ≠ p.succ := Nat.ne_of_lt (Nat.lt_of_le_of_lt hmp' (Nat.lt_succ_self p))
        simp [downTgt, hp, hmne, ih (hnp := hnp') (x := X.tgt x)]

theorem downSrc_comp_downTgt (X : GlobularSet.{u}) {m n p : Nat}
    (hmn : m < n) (hnp : n ≤ p) (x : X.Cell p) :
    downSrc X m n (Nat.le_of_lt hmn) (downTgt X n p hnp x) =
      downSrc X m p (Nat.le_trans (Nat.le_of_lt hmn) hnp) x := by
  -- Induct on `p` by peeling one step at the top; use the independence lemma at the join point.
  revert x
  induction p with
  | zero =>
      intro x
      cases Nat.not_lt_zero _ (Nat.lt_of_lt_of_le hmn hnp)
  | succ p ih =>
      intro x
      by_cases hp : n = p.succ
      · subst hp
        -- Here `downTgt X n n` is the identity, so the statement is definitional.
        have hhnp : hnp = Nat.le_refl p.succ := Subsingleton.elim _ _
        cases hhnp
        simp [downTgt_self]
      · have hnp' : n ≤ p := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hnp hp)
        -- Apply IH to the peeled `tgt` and then swap `tgt` to `src` at the final step.
        -- Use IH: downSrc m n (downTgt n p (tgt x)) = downSrc m p (tgt x)
        have ih' :
            downSrc X m n (Nat.le_of_lt hmn) (downTgt X n p hnp' (X.tgt x)) =
              downSrc X m p (Nat.le_trans (Nat.le_of_lt hmn) hnp') (X.tgt x) := by
          simpa using (ih (hnp := hnp') (x := X.tgt x))
        -- Now compare `downSrc m (p+1) x` with `downSrc m p (tgt x)` via independence at level `p`.
        have hm_p : m < p := Nat.lt_of_lt_of_le hmn hnp'
        have hs : downSrc X m p (Nat.le_of_lt hm_p) (X.tgt x) =
            downSrc X m p (Nat.le_of_lt hm_p) (X.src x) :=
          (downSrc_src_eq_downSrc_tgt (X := X) (m := m) (n := p) hm_p x).symm
        -- Finish by unfolding the outermost `downSrc` step.
        have hmne : m ≠ p.succ := Nat.ne_of_lt (Nat.lt_of_lt_of_le hm_p (Nat.le_succ p))
        simp [downSrc, downTgt, hp, hmne, ih', hs]

theorem downTgt_comp_downSrc (X : GlobularSet.{u}) {m n p : Nat}
    (hmn : m < n) (hnp : n ≤ p) (x : X.Cell p) :
    downTgt X m n (Nat.le_of_lt hmn) (downSrc X n p hnp x) =
      downTgt X m p (Nat.le_trans (Nat.le_of_lt hmn) hnp) x := by
  revert x
  induction p with
  | zero =>
      intro x
      cases Nat.not_lt_zero _ (Nat.lt_of_lt_of_le hmn hnp)
  | succ p ih =>
      intro x
      by_cases hp : n = p.succ
      · subst hp
        have hhnp : hnp = Nat.le_refl p.succ := Subsingleton.elim _ _
        cases hhnp
        simp [downSrc_self]
      · have hnp' : n ≤ p := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hnp hp)
        have ih' :
            downTgt X m n (Nat.le_of_lt hmn) (downSrc X n p hnp' (X.src x)) =
              downTgt X m p (Nat.le_trans (Nat.le_of_lt hmn) hnp') (X.src x) := by
          simpa using (ih (hnp := hnp') (x := X.src x))
        have hm_p : m < p := Nat.lt_of_lt_of_le hmn hnp'
        have hs : downTgt X m p (Nat.le_of_lt hm_p) (X.src x) =
            downTgt X m p (Nat.le_of_lt hm_p) (X.tgt x) :=
          downTgt_src_eq_downTgt_tgt (X := X) (m := m) (n := p) hm_p x
        have hmne : m ≠ p.succ := Nat.ne_of_lt (Nat.lt_of_lt_of_le hm_p (Nat.le_succ p))
        simp [downSrc, downTgt, hp, hmne, ih', hs]

end GlobularSet

/-!
## The presheaf conversion
-/

namespace GlobularSet

/-- The action on morphisms used by `GlobularSet.toPresheaf`. -/
def toPresheafMap (X : GlobularSet.{u}) {a b : GlobularIndex.Objᵒᵖ} (f : a ⟶ b) :
    X.Cell a.unop.n → X.Cell b.unop.n :=
  match f.unop with
  | ⟨none, valid⟩ =>
      fun x => by
        have hn : b.unop.n = a.unop.n := congrArg GlobularIndex.Obj.n valid
        simpa [hn] using x
  | ⟨some choice, valid⟩ =>
      let hle : b.unop.n ≤ a.unop.n := Nat.le_of_lt valid
      match choice with
      | false => GlobularSet.downSrc X b.unop.n a.unop.n hle
      | true => GlobularSet.downTgt X b.unop.n a.unop.n hle

/-- Convert a structured `GlobularSet` into a presheaf on the globular indexing category. -/
def toPresheaf (X : GlobularSet.{u}) : GlobularSetPsh :=
  { obj := fun o => X.Cell o.unop.n
    map := fun {a b} f => toPresheafMap (X := X) (a := a) (b := b) f
    map_id := by
      intro a
      funext x
      simp [toPresheafMap, CategoryStruct.id, GlobularIndex.Hom.id]
    map_comp := by
      intro a b c f g
      cases a with
      | op a0 =>
        cases b with
        | op b0 =>
          cases c with
          | op c0 =>
            -- Work by cases on `f.unop.kind` and `g.unop.kind`.
            cases hf : f.unop with
            | mk fk fv =>
              cases hg : g.unop with
              | mk gk gv =>
                cases fk with
                | none =>
                    -- `f` is identity, so `toPresheafMap (f ≫ g) = toPresheafMap g`.
                    cases fv
                    cases gk with
                    | none =>
                        cases gv
                        funext x
                        simp [toPresheafMap, hf, hg, CategoryStruct.comp, GlobularIndex.Hom.comp]
                    | some gb =>
                        funext x
                        simp [toPresheafMap, hf, hg, CategoryStruct.comp, GlobularIndex.Hom.comp]
                | some fb =>
                    cases gk with
                    | none =>
                        cases gv
                        funext x
                        simp [toPresheafMap, hf, hg, CategoryStruct.comp, GlobularIndex.Hom.comp]
                    | some gb =>
                        funext x
                        have hlt_cb : c0.n < b0.n := gv
                        have hlt_ba : b0.n < a0.n := fv
                        have hle_cb : c0.n ≤ b0.n := Nat.le_of_lt hlt_cb
                        have hle_ba : b0.n ≤ a0.n := Nat.le_of_lt hlt_ba
                        have hle_ca : c0.n ≤ a0.n := Nat.le_trans hle_cb hle_ba
                        cases gb <;> cases fb
                        · -- gb = src, fb = src
                          have :=
                            (GlobularSet.downSrc_comp_downSrc (X := X)
                              (m := c0.n) (n := b0.n) (p := a0.n)
                              (hmn := hle_cb) (hnp := hle_ba) (x := x))
                          -- `downSrc c b (downSrc b a x) = downSrc c a x`
                          simpa [toPresheafMap, hf, hg, GlobularIndex.Hom.comp, hle_cb, hle_ba, hle_ca] using this.symm
                        · -- gb = src, fb = tgt
                          have :=
                            (GlobularSet.downSrc_comp_downTgt (X := X)
                              (m := c0.n) (n := b0.n) (p := a0.n)
                              (hmn := hlt_cb) (hnp := hle_ba) (x := x))
                          simpa [toPresheafMap, hf, hg, GlobularIndex.Hom.comp, hle_cb, hle_ba, hle_ca] using this.symm
                        · -- gb = tgt, fb = src
                          have :=
                            (GlobularSet.downTgt_comp_downSrc (X := X)
                              (m := c0.n) (n := b0.n) (p := a0.n)
                              (hmn := hlt_cb) (hnp := hle_ba) (x := x))
                          simpa [toPresheafMap, hf, hg, GlobularIndex.Hom.comp, hle_cb, hle_ba, hle_ca] using this.symm
                        · -- gb = tgt, fb = tgt
                          have :=
                            (GlobularSet.downTgt_comp_downTgt (X := X)
                              (m := c0.n) (n := b0.n) (p := a0.n)
                              (hmn := hle_cb) (hnp := hle_ba) (x := x))
                          simpa [toPresheafMap, hf, hg, GlobularIndex.Hom.comp, hle_cb, hle_ba, hle_ca] using this.symm
  }

end GlobularSet

end IteratedVirtual
end HeytingLean
