import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Opposites
import HeytingLean.IteratedVirtual.GlobeCategoryPresented
import HeytingLean.IteratedVirtual.GlobularPresheaf

/-!
# IteratedVirtual.GlobeCatEquivalence

Phase‑8 (research-scale): relate the **presented** globe category `GlobeCategoryPresented.GlobeCat`
to the strict surrogate `GlobularIndex`.

We provide:
- a canonical normal form in the presented category (`canonMor`) and a normalization lemma
  (`normalize_path`),
- an explicit functor `fromGlobularIndex : GlobularIndex ⥤ GlobeCat`,
- an equivalence `GlobeCat ≌ GlobularIndex.Obj`,
- a rebasing equivalence on presheaf globular sets.
-/

namespace HeytingLean
namespace IteratedVirtual

open CategoryTheory

namespace GlobeCategoryPresented

namespace PathsCat

/-- Boolean tag of a generator: `false` for `σ`, `true` for `τ`. -/
def genBool : ∀ {a b : Obj}, (a ⟶ b) → Bool
  | _, _, Gen.sigma _ => false
  | _, _, Gen.tau _ => true

/-- First-edge tag of a path (defaults to `false` on `nil`, but our uses are on nonempty paths). -/
def firstBool : ∀ {a b : Obj}, Quiver.Path a b → Bool
  | _, _, Quiver.Path.nil => false
  | _, _, Quiver.Path.cons Quiver.Path.nil e => genBool e
  | _, _, Quiver.Path.cons (Quiver.Path.cons p e₁) _ => firstBool (Quiver.Path.cons p e₁)

@[simp] theorem firstBool_toPath {a b : Obj} (e : a ⟶ b) :
    firstBool (Quiver.Hom.toPath e) = genBool e := by
  cases e <;> simp [Quiver.Hom.toPath, firstBool, genBool]

end PathsCat

namespace GlobeCat

open PathsCat

/-- Canonical “normal form” morphism `n ⟶ n+(k+1)` in `GlobeCat`:
choose `σₙ` or `τₙ` at the first step, then use only `σ` afterwards. -/
def canonMor (n : Nat) (b : Bool) : ∀ k : Nat, obj n ⟶ obj (n + k.succ)
  | 0 =>
      if b then tau n else sigma n
  | k + 1 =>
      canonMor n b k ≫ sigma (n + k + 1)

@[simp] theorem canonMor_zero_false (n : Nat) : canonMor n false 0 = sigma n := by
  simp [canonMor]

@[simp] theorem canonMor_zero_true (n : Nat) : canonMor n true 0 = tau n := by
  simp [canonMor]

@[simp] theorem canonMor_succ (n : Nat) (b : Bool) (k : Nat) :
    canonMor n b (k + 1) = canonMor n b k ≫ sigma (n + k + 1) := by
  rfl

theorem canonMor_comp_tau_eq (n : Nat) (b : Bool) :
    ∀ k : Nat, canonMor n b k ≫ tau (n + k + 1) = canonMor n b (k + 1)
  | 0 => by
      cases b <;> simp [canonMor, GlobeCat.sigma_sigma_eq_sigma_tau, GlobeCat.tau_sigma_eq_tau_tau]
  | k + 1 => by
      have hn : n + (k + 1) + 1 = n + k + 2 := by
        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      cases hn
      calc
        canonMor n b (k + 1) ≫ tau (n + k + 2)
            = (canonMor n b k ≫ sigma (n + k + 1)) ≫ tau (n + k + 2) := by
                simp [canonMor, Category.assoc]
        _ = canonMor n b k ≫ (sigma (n + k + 1) ≫ tau (n + k + 2)) := by
              simp [Category.assoc]
        _ = canonMor n b k ≫ (sigma (n + k + 1) ≫ sigma (n + k + 2)) := by
              simpa [Category.assoc] using
                congrArg (fun x => canonMor n b k ≫ x) (GlobeCat.sigma_sigma_eq_sigma_tau (n + k + 1)).symm
        _ = canonMor n b (k + 2) := by
              -- Unfold `canonMor`; the remaining mismatch is the index of the final `σ`.
              simp [canonMor, Category.assoc]
              have hnσ : n + (k + 1) + 1 = n + k + 2 := by
                simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              cases hnσ
              rfl

private theorem tgt_nat_eq_add_length {a b : GlobeCategoryPresented.Obj} (p : Quiver.Path a b) :
    b.n = a.n + p.length := by
  induction p with
  | nil =>
      simp [Quiver.Path.length]
  | cons p e ih =>
      -- `e` advances dimension by exactly one.
      cases e with
      | sigma n0 =>
          -- goal is `n0+1 = a.n + (p.length+1)`, using IH `n0 = a.n + p.length`
          calc
            n0 + 1 = (a.n + p.length) + 1 := by simpa [ih]
            _ = a.n + (p.length + 1) := by simp [Nat.add_assoc]
            _ = a.n + (1 + p.length) := by
                  simp [Nat.add_comm]
            _ = a.n + (Quiver.Path.cons p (Gen.sigma n0)).length := by
                  simp [Quiver.Path.length_cons, Nat.add_comm]
      | tau n0 =>
          calc
            n0 + 1 = (a.n + p.length) + 1 := by simpa [ih]
            _ = a.n + (p.length + 1) := by simp [Nat.add_assoc]
            _ = a.n + (1 + p.length) := by
                  simp [Nat.add_comm]
            _ = a.n + (Quiver.Path.cons p (Gen.tau n0)).length := by
                  simp [Quiver.Path.length_cons, Nat.add_comm]

/-- Every path in the free path category normalizes to the canonical `canonMor` in the quotient. -/
theorem normalize_path {n k : Nat} (p : Quiver.Path (ofNat n) (ofNat (n + k.succ))) :
    quotientFunctor.map p = canonMor n (firstBool p) k := by
  induction k with
  | zero =>
      -- The target is `n+1`, so the path has length `1` and is a single generator.
      cases p with
      | cons p' e =>
          have hlen1 : (Quiver.Path.cons p' e).length = 1 := by
            have hdim := (tgt_nat_eq_add_length (p := Quiver.Path.cons p' e))
            -- `n+1 = n + length`
            have : n + 1 = n + (Quiver.Path.cons p' e).length := by
              simpa [ofNat] using hdim.symm
            have : 1 = (Quiver.Path.cons p' e).length := Nat.add_left_cancel this
            exact this.symm
          have hlen0 : p'.length = 0 := by
            have h : p'.length + 1 = 1 := by
              simpa [Quiver.Path.length_cons] using hlen1
            have : p'.length + 1 = 0 + 1 := by
              simpa using h
            exact Nat.add_right_cancel this
          cases p' with
          | nil =>
              cases e <;>
                simp [canonMor, firstBool, genBool, quotientFunctor, GlobeCat.sigma, GlobeCat.tau,
                  PathsCat.sigma, PathsCat.tau, Quiver.Hom.toPath]
          | cons p'' e'' =>
              -- contradiction: a nonempty prefix has positive length
              simp [Quiver.Path.length_cons] at hlen0
  | succ k ih =>
      -- Decompose into a prefix to `n+k+1` and a final generator at dimension `n+k+1`.
      cases p with
      | cons p' e =>
          rename_i b
          -- Compute the length of the whole path from endpoints, then deduce the prefix length.
          have hlen_total : (Quiver.Path.cons p' e).length = (k + 1).succ := by
            have hdim := (tgt_nat_eq_add_length (p := Quiver.Path.cons p' e))
            have : n + (k + 1).succ = n + (Quiver.Path.cons p' e).length := by
              simpa [ofNat] using hdim
            have : (k + 1).succ = (Quiver.Path.cons p' e).length := Nat.add_left_cancel this
            exact this.symm
          have hlen_prefix : p'.length = k.succ := by
            have : p'.length + 1 = k.succ + 1 := by
              simpa [Nat.succ_eq_add_one, Quiver.Path.length_cons, Nat.add_assoc] using hlen_total
            exact Nat.add_right_cancel this
          -- Identify the intermediate object as `ofNat (n + k.succ)`.
          have hbNat : b.n = n + k.succ := by
            have hdim := (tgt_nat_eq_add_length (p := p'))
            simpa [ofNat, hlen_prefix] using hdim
          have hbObj : b = ofNat (n + k.succ) := by
            cases b with
            | mk bn =>
                have : bn = n + k.succ := by simpa using hbNat
                cases this
                rfl
          cases hbObj
          -- Now the prefix is correctly typed for the IH.
          have hp' : quotientFunctor.map p' = canonMor n (firstBool p') k := by
            simpa using ih (p := p')
          -- `firstBool` ignores the appended edge because the prefix is nonempty.
          have hfirst : firstBool (p'.cons e) = firstBool p' := by
            cases p' with
            | cons p0 e0 =>
                simp [PathsCat.firstBool]
          -- Use `map_comp` without `simp` collapsing the goal.
          have hmap :
              quotientFunctor.map (p'.cons e) =
                quotientFunctor.map p' ≫ quotientFunctor.map (Quiver.Hom.toPath e) := by
            have hpath : p'.comp (Quiver.Hom.toPath e) = p'.cons e :=
              Quiver.Path.comp_toPath_eq_cons (p := p') (e := e)
            have hmap_path :
                quotientFunctor.map (p'.comp (Quiver.Hom.toPath e)) = quotientFunctor.map (p'.cons e) :=
              congrArg (fun q => quotientFunctor.map q) hpath
            have h0 := quotientFunctor.map_comp p' (Quiver.Hom.toPath e)
            calc
              quotientFunctor.map (p'.cons e) = quotientFunctor.map (p'.comp (Quiver.Hom.toPath e)) := by
                exact hmap_path.symm
              _ = quotientFunctor.map p' ≫ quotientFunctor.map (Quiver.Hom.toPath e) := by
                exact h0
          cases e with
          | sigma m =>
              -- The last edge is `σ`, matching the recursive step of `canonMor`.
              have hn : n + (k + 1) = n + k + 1 := by
                simp [Nat.add_assoc]
              simp [hmap, hp', hfirst, canonMor, GlobeCat.sigma, PathsCat.sigma]
              cases hn
              rfl
          | tau m =>
              have ht :
                  canonMor n (firstBool p') k ≫ tau (n + k + 1) = canonMor n (firstBool p') (k + 1) := by
                simpa using (canonMor_comp_tau_eq (n := n) (b := firstBool p') k)
              have hn : n + (k + 1) = n + k + 1 := by
                simp [Nat.add_assoc]
              -- Reduce to the canonical replacement of a final `τ` by `σ` in `canonMor`.
              have ht' :
                  canonMor n (firstBool p') k ≫ quotientFunctor.map (Quiver.Hom.toPath (Gen.tau (n + k + 1))) =
                    canonMor n (firstBool p') (k + 1) := by
                -- `tau` is defined as mapping the length-1 `τ` path.
                simpa [GlobeCat.tau, PathsCat.tau] using ht
              -- Now finish by unfolding `canonMor`.
              have hcanon : canonMor n (firstBool p') (k + 1) = canonMor n (firstBool p') k ≫ sigma (n + k + 1) := by
                rfl
              -- Rewrite indices using `hn` and conclude.
              simpa [hn, hmap, hp', hfirst, ht', hcanon, GlobeCat.sigma, PathsCat.sigma, Category.assoc]

  /-- A transport-friendly variant of `normalize_path`, avoiding casts on the input path. -/
    theorem normalize_path_eqToHom {n k m : Nat} (hm : m = n + k.succ) (p : Quiver.Path (ofNat n) (ofNat m)) :
        quotientFunctor.map p ≫
            eqToHom (C := GlobeCategoryPresented.GlobeCat) (congrArg GlobeCategoryPresented.GlobeCat.obj hm) =
          canonMor n (firstBool p) k := by
      cases hm
      -- now `m` is definitionally `n + k.succ` and the `eqToHom` is the identity
      simpa using (normalize_path (n := n) (k := k) (p := p))

    /-- Canonical path representative of `canonMor` in the free path category. -/
    private def canonPath (n : Nat) (b : Bool) : ∀ k : Nat, Quiver.Path (ofNat n) (ofNat (n + k.succ))
      | 0 => if b then PathsCat.tau n else PathsCat.sigma n
      | k + 1 => (canonPath n b k).cons (Gen.sigma (n + k + 1))

    private theorem quotientFunctor_map_canonPath (n : Nat) (b : Bool) :
        ∀ k : Nat, quotientFunctor.map (canonPath n b k) = canonMor n b k := by
      intro k
      induction k with
      | zero =>
          cases b <;>
            simp [canonPath, canonMor, GlobeCat.sigma, GlobeCat.tau, PathsCat.sigma, PathsCat.tau, quotientFunctor]
      | succ k ih =>
          -- Express `cons` as composition with a length-1 path, so functoriality applies.
          have hpath :
              (canonPath n b k).comp (Quiver.Hom.toPath (Gen.sigma (n + k + 1))) =
                (canonPath n b k).cons (Gen.sigma (n + k + 1)) :=
            Quiver.Path.comp_toPath_eq_cons (p := canonPath n b k) (e := Gen.sigma (n + k + 1))
          have hmap_path :
              quotientFunctor.map ((canonPath n b k).comp (Quiver.Hom.toPath (Gen.sigma (n + k + 1)))) =
                quotientFunctor.map ((canonPath n b k).cons (Gen.sigma (n + k + 1))) :=
            congrArg (fun q => quotientFunctor.map q) hpath
          have h0 := quotientFunctor.map_comp (canonPath n b k) (Quiver.Hom.toPath (Gen.sigma (n + k + 1)))
          -- Now unfold one step of `canonMor`.
          calc
            quotientFunctor.map (canonPath n b (k + 1)) =
                quotientFunctor.map ((canonPath n b k).cons (Gen.sigma (n + k + 1))) := by
                  rfl
            _ = quotientFunctor.map ((canonPath n b k).comp (Quiver.Hom.toPath (Gen.sigma (n + k + 1)))) := by
                  exact hmap_path.symm
            _ = quotientFunctor.map (canonPath n b k) ≫
                  quotientFunctor.map (Quiver.Hom.toPath (Gen.sigma (n + k + 1))) := by
                  exact h0
            _ = canonMor n b k ≫ sigma (n + k + 1) := by
                  simp [GlobeCat.sigma, PathsCat.sigma, quotientFunctor, ih]
            _ = canonMor n b (k + 1) := by
                  rfl

      private theorem firstBool_canonPath (n : Nat) (b : Bool) :
          ∀ k : Nat, firstBool (canonPath n b k) = b := by
        intro k
        induction k with
        | zero =>
            cases b <;>
              simp [canonPath, PathsCat.sigma, PathsCat.tau, PathsCat.firstBool_toPath, PathsCat.genBool]
        | succ k ih =>
            -- `canonPath` is never `nil` (endpoints differ), so `firstBool` ignores the appended edge.
            -- First unfold the recursive step.
            simp [canonPath]
            cases h : canonPath n b k with
            | cons p e =>
                have ih' : firstBool (p.cons e) = b := by
                  simpa [h] using ih
                simpa [h, PathsCat.firstBool] using ih'

      private theorem firstBool_comp_canonPath (n : Nat) (b₁ b₂ : Bool) (k₁ k₂ : Nat) :
          firstBool ((canonPath n b₁ k₁).comp (canonPath (n + k₁.succ) b₂ k₂)) = b₁ := by
        -- Right-composition appends edges and cannot change the first generator.
        induction k₂ with
        | zero =>
            have h₁ : firstBool (canonPath n b₁ k₁) = b₁ := firstBool_canonPath n b₁ k₁
            cases h : canonPath n b₁ k₁ with
            | cons p e =>
                have h₁' : firstBool (p.cons e) = b₁ := by
                  simpa [h] using h₁
                cases b₂ <;>
                  -- `canonPath _ _ 0` is a length-1 generator; appending it cannot change the first edge.
                  simpa [h, canonPath, PathsCat.sigma, PathsCat.tau, PathsCat.firstBool,
                    Quiver.Path.comp_toPath_eq_cons] using h₁'
        | succ k₂ ih =>
            -- Append a final `σ` to the right, then use the IH.
            have ih' :
                firstBool ((canonPath n b₁ k₁).comp (canonPath (n + (k₁ + 1)) b₂ k₂)) = b₁ := by
              simpa [Nat.succ_eq_add_one] using ih
            -- Unfold the recursive step and reduce to the IH (the final edge cannot change `firstBool`).
            simp [canonPath, Quiver.Path.comp_cons, Nat.succ_eq_add_one]
            cases hprefix :
                (canonPath n b₁ k₁).comp (canonPath (n + (k₁ + 1)) b₂ k₂) with
            | cons p e =>
                simpa [PathsCat.firstBool, hprefix] using ih'

    /-- Composition of canonical normal forms is left-biased (the second boolean choice is irrelevant). -/
    theorem canonMor_comp_canonMor (n : Nat) (b₁ b₂ : Bool) (k₁ k₂ : Nat) :
        canonMor n b₁ k₁ ≫ canonMor (n + k₁.succ) b₂ k₂ =
          canonMor n b₁ (k₁ + k₂.succ) ≫
            eqToHom (C := GlobeCategoryPresented.GlobeCat)
              (congrArg GlobeCategoryPresented.GlobeCat.obj (by
                simp [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm])) := by
      classical
      let p₁ : Quiver.Path (ofNat n) (ofNat (n + k₁.succ)) := canonPath n b₁ k₁
      let p₂ : Quiver.Path (ofNat (n + k₁.succ)) (ofNat ((n + k₁.succ) + k₂.succ)) := canonPath (n + k₁.succ) b₂ k₂
      let p : Quiver.Path (ofNat n) (ofNat ((n + k₁.succ) + k₂.succ)) := p₁.comp p₂
      have hpMap :
          quotientFunctor.map p = canonMor n b₁ k₁ ≫ canonMor (n + k₁.succ) b₂ k₂ := by
        dsimp [p]
        have hpComp :
            quotientFunctor.map (p₁.comp p₂) = quotientFunctor.map p₁ ≫ quotientFunctor.map p₂ :=
          quotientFunctor.map_comp p₁ p₂
        -- Replace each canonical path by its `canonMor`.
        simpa [p₁, p₂, quotientFunctor_map_canonPath, Category.assoc] using hpComp
      have hm : ((n + k₁.succ) + k₂.succ) = n + (k₁ + k₂.succ).succ := by
        simp [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm]
      have hnorm :=
        normalize_path_eqToHom (n := n) (k := k₁ + k₂.succ) (m := (n + k₁.succ) + k₂.succ) hm p
      -- Solve for `quotientFunctor.map p` by composing with the inverse transport.
      have hnorm' :
          quotientFunctor.map p =
            canonMor n (firstBool p) (k₁ + k₂.succ) ≫
              eqToHom (C := GlobeCategoryPresented.GlobeCat) (congrArg GlobeCategoryPresented.GlobeCat.obj hm.symm) := by
        have :=
          congrArg
            (fun q =>
              q ≫
                eqToHom (C := GlobeCategoryPresented.GlobeCat) (congrArg GlobeCategoryPresented.GlobeCat.obj hm.symm))
            hnorm
        -- Cancel `eqToHom hm` against `eqToHom hm.symm`.
        simpa [Category.assoc] using this
      have hfb : firstBool p = b₁ := by
        -- `p` is `canonPath` followed by `canonPath`, so the first edge is determined by `b₁`.
        simpa [p, p₁, p₂] using firstBool_comp_canonPath n b₁ b₂ k₁ k₂
      -- Combine the normalization with the path representative of the composite.
      calc
        canonMor n b₁ k₁ ≫ canonMor (n + k₁.succ) b₂ k₂ = quotientFunctor.map p := by
          simpa using hpMap.symm
        _ = canonMor n (firstBool p) (k₁ + k₂.succ) ≫
              eqToHom (C := GlobeCategoryPresented.GlobeCat) (congrArg GlobeCategoryPresented.GlobeCat.obj hm.symm) := by
              exact hnorm'
        _ = canonMor n b₁ (k₁ + k₂.succ) ≫
              eqToHom (C := GlobeCategoryPresented.GlobeCat) (congrArg GlobeCategoryPresented.GlobeCat.obj hm.symm) := by
              simp [hfb]
        _ = canonMor n b₁ (k₁ + k₂.succ) ≫
              eqToHom (C := GlobeCategoryPresented.GlobeCat)
                (congrArg GlobeCategoryPresented.GlobeCat.obj (by
                  simpa using hm.symm)) := by
              rfl

  end GlobeCat

end GlobeCategoryPresented

namespace GlobeCatEquivalence

open GlobeCategoryPresented

abbrev GlobeCat := GlobeCategoryPresented.GlobeCat

abbrev toGlobularIndex : GlobeCat ⥤ GlobularIndex.Obj :=
  GlobeCategoryPresented.ToGlobularIndex.functor

namespace FromGlobularIndex

/-- Deterministic “gap” (number of interior steps) between dimensions. -/
def gap (a b : Nat) : Nat :=
  b - (a + 1)

theorem gap_spec {a b : Nat} (hab : a < b) : b = a + (gap a b).succ := by
  have hle : a + 1 ≤ b := Nat.succ_le_of_lt hab
  have hb : (a + 1) + (b - (a + 1)) = b := Nat.add_sub_of_le hle
  -- Re-associate `(a+1) + k` as `a + k.succ`.
  calc
    b = (a + 1) + (b - (a + 1)) := by simpa using hb.symm
    _ = a + (b - (a + 1)).succ := by
          simp [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm]
    _ = a + (gap a b).succ := by rfl

end FromGlobularIndex

open GlobeCategoryPresented.PathsCat

theorem pathsFunctor_kind {a b : GlobeCategoryPresented.Obj} (p : Quiver.Path a b) :
    (GlobeCategoryPresented.ToGlobularIndex.pathsFunctor.map p).kind =
      match p with
      | Quiver.Path.nil => none
      | _ => some (firstBool p) := by
  induction p with
  | nil =>
      -- `pathsFunctor.map nil` is an identity in `GlobularIndex`.
      simp [GlobeCategoryPresented.ToGlobularIndex.pathsFunctor, GlobeCategoryPresented.ToGlobularIndex.genPrefunctor,
        CategoryStruct.id, GlobularIndex.Hom.id]
  | cons p e ih =>
      cases p with
      | nil =>
          -- One-edge path: the kind is determined by the generator.
          cases e <;>
            simp [GlobeCategoryPresented.ToGlobularIndex.pathsFunctor, GlobeCategoryPresented.ToGlobularIndex.genPrefunctor,
              firstBool, genBool, CategoryStruct.id, CategoryStruct.comp, GlobularIndex.Hom.id, GlobularIndex.Hom.comp,
              GlobularIndex.Hom.src, GlobularIndex.Hom.tgt]
      | cons p' e' =>
          -- Nonempty prefix: the composite kind is left-biased.
          have hk :
              (GlobeCategoryPresented.ToGlobularIndex.pathsFunctor.map (Quiver.Path.cons p' e')).kind =
                some (firstBool (Quiver.Path.cons p' e')) := by
            simpa using ih
          -- Expand the functor on a cons.
          have hcons :
              GlobeCategoryPresented.ToGlobularIndex.pathsFunctor.map ((Quiver.Path.cons p' e').cons e) =
                GlobeCategoryPresented.ToGlobularIndex.pathsFunctor.map (Quiver.Path.cons p' e') ≫
                  GlobeCategoryPresented.ToGlobularIndex.genPrefunctor.map e := by
            simp [GlobeCategoryPresented.ToGlobularIndex.pathsFunctor]
          -- Now compute `kind` using left-biased composition.
          cases hpre : GlobeCategoryPresented.ToGlobularIndex.pathsFunctor.map (Quiver.Path.cons p' e') with
          | mk preKind preValid =>
              -- Rewrite the kind equality using the explicit `mk` form.
              simp [hpre] at hk
              cases preKind with
              | none =>
                  -- Impossible: `hk` says the kind is `some _`.
                  cases hk
              | some fb =>
                  have hfb : fb = firstBool (Quiver.Path.cons p' e') :=
                    Option.some.inj hk
                  -- `firstBool` ignores the appended edge when the prefix is nonempty.
                  have hfirst :
                      firstBool ((Quiver.Path.cons p' e').cons e) = firstBool (Quiver.Path.cons p' e') := by
                    simp [firstBool]
                  have :
                      (GlobeCategoryPresented.ToGlobularIndex.pathsFunctor.map ((Quiver.Path.cons p' e').cons e)).kind =
                        some fb := by
                    -- Rewrite using `hcons`, then apply `comp_kind_some`.
                    have :
                        (({ kind := some fb, valid := preValid } : GlobularIndex.Hom _ _) ≫
                            GlobeCategoryPresented.ToGlobularIndex.genPrefunctor.map e).kind =
                          some fb := by
                      simpa [GlobularIndex.Hom.comp] using
                        (GlobularIndex.Hom.comp_kind_some fb preValid
                          (GlobeCategoryPresented.ToGlobularIndex.genPrefunctor.map e))
                    simpa [hcons, hpre] using this
                  simpa [hfirst, hfb] using this

/-- Action on morphisms for `fromGlobularIndex` (defined separately so `map_comp` can unfold it). -/
noncomputable def fromGlobularIndexMap {a b : GlobularIndex.Obj} (f : GlobularIndex.Hom a b) :
    GlobeCategoryPresented.GlobeCat.obj a.n ⟶ GlobeCategoryPresented.GlobeCat.obj b.n := by
  cases f with
  | mk kind valid =>
    cases kind with
    | none =>
        cases valid
        exact 𝟙 (GlobeCategoryPresented.GlobeCat.obj a.n)
    | some fb =>
        have hab : a.n < b.n := valid
        let k : Nat := FromGlobularIndex.gap a.n b.n
        have hk : b.n = a.n + k.succ := FromGlobularIndex.gap_spec (a := a.n) (b := b.n) hab
        -- Postcompose with an `eqToHom` to land in `b`.
        have hbQ :
            GlobeCategoryPresented.GlobeCat.obj (a.n + k.succ) = GlobeCategoryPresented.GlobeCat.obj b.n :=
          congrArg GlobeCategoryPresented.GlobeCat.obj hk.symm
        exact GlobeCategoryPresented.GlobeCat.canonMor a.n fb k ≫
          eqToHom (C := GlobeCategoryPresented.GlobeCat) hbQ

/-- Quasi-inverse `GlobularIndex.Obj ⥤ GlobeCat` picking the canonical normal form. -/
noncomputable def fromGlobularIndex : GlobularIndex.Obj ⥤ GlobeCat where
  obj o := GlobeCategoryPresented.GlobeCat.obj o.n
  map := fun {a b} f => fromGlobularIndexMap (a := a) (b := b) f
  map_id := by
    intro a
    rfl
  map_comp := by
    intro a b c f g
    -- Expose source composition as `GlobularIndex.Hom.comp` while keeping target `≫` abstract.
    change
        fromGlobularIndexMap (a := a) (b := c)
            (GlobularIndex.Hom.comp (a := a) (b := b) (c := c) f g) =
          fromGlobularIndexMap (a := a) (b := b) f ≫ fromGlobularIndexMap (a := b) (b := c) g
    cases f with
    | mk fk fv =>
      cases g with
      | mk gk gv =>
        cases fk with
        | none =>
            cases fv
            cases gk with
            | none =>
                cases gv
                -- Both morphisms are identities.
                have hcomp :
                    GlobularIndex.Hom.comp (a := a) (b := a) (c := a)
                        ({ kind := none, valid := rfl } : GlobularIndex.Hom a a)
                        ({ kind := none, valid := rfl } : GlobularIndex.Hom a a) =
                      ({ kind := none, valid := rfl } : GlobularIndex.Hom a a) := by
                  simp [GlobularIndex.Hom.comp]
                rw [hcomp]
                simp [fromGlobularIndexMap]
            | some gb =>
                have hcomp :
                    GlobularIndex.Hom.comp (a := a) (b := a) (c := c)
                        ({ kind := none, valid := rfl } : GlobularIndex.Hom a a)
                        ({ kind := some gb, valid := gv } : GlobularIndex.Hom a c) =
                      ({ kind := some gb, valid := gv } : GlobularIndex.Hom a c) := by
                  simp [GlobularIndex.Hom.comp]
                rw [hcomp]
                simp [fromGlobularIndexMap]
        | some fb =>
            cases gk with
            | none =>
                cases gv
                -- `g` is an identity, so `f ≫ g = f`.
                simp [fromGlobularIndexMap, GlobularIndex.Hom.comp]
            | some gb =>
                have hab : a.n < b.n := fv
                have hbc : b.n < c.n := gv
                have hk₁ :
                    b.n = a.n + (FromGlobularIndex.gap a.n b.n).succ :=
                  FromGlobularIndex.gap_spec (a := a.n) (b := b.n) hab
                have hk₂ :
                    c.n = b.n + (FromGlobularIndex.gap b.n c.n).succ :=
                  FromGlobularIndex.gap_spec (a := b.n) (b := c.n) hbc
                have hac : a.n < c.n := Nat.lt_trans hab hbc
                have hk₃ :
                    c.n = a.n + (FromGlobularIndex.gap a.n c.n).succ :=
                  FromGlobularIndex.gap_spec (a := a.n) (b := c.n) hac
                have hklen :
                    FromGlobularIndex.gap a.n c.n =
                      FromGlobularIndex.gap a.n b.n + (FromGlobularIndex.gap b.n c.n).succ := by
                  have hc :
                      c.n =
                        a.n +
                          (FromGlobularIndex.gap a.n b.n + (FromGlobularIndex.gap b.n c.n).succ).succ := by
                    calc
                      c.n = b.n + (FromGlobularIndex.gap b.n c.n).succ := hk₂
                      _ =
                          (a.n + (FromGlobularIndex.gap a.n b.n).succ) +
                            (FromGlobularIndex.gap b.n c.n).succ := by
                            -- Freeze the second gap so rewriting `b.n` doesn't rewrite inside it.
                            let x : Nat := FromGlobularIndex.gap b.n c.n
                            have hx : b.n + x.succ = (a.n + (FromGlobularIndex.gap a.n b.n).succ) + x.succ := by
                              exact congrArg (fun t => t + x.succ) hk₁
                            simpa [x] using hx
                      _ =
                          a.n +
                            ((FromGlobularIndex.gap a.n b.n).succ +
                              (FromGlobularIndex.gap b.n c.n).succ) := by
                            simp [Nat.add_assoc]
                      _ =
                          a.n +
                            (FromGlobularIndex.gap a.n b.n +
                              (FromGlobularIndex.gap b.n c.n).succ).succ := by
                            exact congrArg (fun t => a.n + t)
                              (Nat.succ_add (FromGlobularIndex.gap a.n b.n)
                                (FromGlobularIndex.gap b.n c.n).succ)
                  have hcancel :
                      (FromGlobularIndex.gap a.n b.n + (FromGlobularIndex.gap b.n c.n).succ).succ =
                        (FromGlobularIndex.gap a.n c.n).succ := by
                    have :
                        a.n +
                            (FromGlobularIndex.gap a.n b.n +
                                (FromGlobularIndex.gap b.n c.n).succ).succ =
                          a.n + (FromGlobularIndex.gap a.n c.n).succ := by
                      calc
                        a.n +
                              (FromGlobularIndex.gap a.n b.n +
                                  (FromGlobularIndex.gap b.n c.n).succ).succ =
                            c.n := by
                            exact hc.symm
                        _ = a.n + (FromGlobularIndex.gap a.n c.n).succ := hk₃
                    exact Nat.add_left_cancel this
                  exact (Nat.succ_inj.mp hcancel).symm
                have hb₁ :
                    GlobeCategoryPresented.GlobeCat.obj
                          (a.n + (FromGlobularIndex.gap a.n b.n).succ) =
                      GlobeCategoryPresented.GlobeCat.obj b.n :=
                  congrArg GlobeCategoryPresented.GlobeCat.obj hk₁.symm
                have hb₂ :
                    GlobeCategoryPresented.GlobeCat.obj
                          (b.n + (FromGlobularIndex.gap b.n c.n).succ) =
                      GlobeCategoryPresented.GlobeCat.obj c.n :=
                  congrArg GlobeCategoryPresented.GlobeCat.obj hk₂.symm
                have hb₃ :
                    GlobeCategoryPresented.GlobeCat.obj
                          (a.n + (FromGlobularIndex.gap a.n c.n).succ) =
                      GlobeCategoryPresented.GlobeCat.obj c.n :=
                  congrArg GlobeCategoryPresented.GlobeCat.obj hk₃.symm
                have hb₁g :
                    GlobeCategoryPresented.GlobeCat.obj
                          ((a.n + (FromGlobularIndex.gap a.n b.n).succ) +
                            (FromGlobularIndex.gap b.n c.n).succ) =
                      GlobeCategoryPresented.GlobeCat.obj
                          (b.n + (FromGlobularIndex.gap b.n c.n).succ) :=
                  congrArg
                      (fun t =>
                        GlobeCategoryPresented.GlobeCat.obj (t + (FromGlobularIndex.gap b.n c.n).succ))
                      hk₁.symm
                have hcanonNat :
                    a.n +
                          (FromGlobularIndex.gap a.n b.n +
                              (FromGlobularIndex.gap b.n c.n).succ).succ =
                      (a.n + (FromGlobularIndex.gap a.n b.n).succ) +
                          (FromGlobularIndex.gap b.n c.n).succ := by
                  calc
                    a.n +
                          (FromGlobularIndex.gap a.n b.n +
                              (FromGlobularIndex.gap b.n c.n).succ).succ =
                        (a.n +
                              (FromGlobularIndex.gap a.n b.n +
                                (FromGlobularIndex.gap b.n c.n).succ)).succ := by
                        exact Nat.add_succ a.n
                          (FromGlobularIndex.gap a.n b.n + (FromGlobularIndex.gap b.n c.n).succ)
                    _ =
                        ((a.n + FromGlobularIndex.gap a.n b.n) +
                              (FromGlobularIndex.gap b.n c.n).succ).succ := by
                        exact congrArg Nat.succ
                          (Nat.add_assoc a.n (FromGlobularIndex.gap a.n b.n)
                            (FromGlobularIndex.gap b.n c.n).succ).symm
                    _ =
                        (a.n + FromGlobularIndex.gap a.n b.n).succ +
                              (FromGlobularIndex.gap b.n c.n).succ := by
                        exact (Nat.succ_add (a.n + FromGlobularIndex.gap a.n b.n)
                          (FromGlobularIndex.gap b.n c.n).succ).symm
                    _ =
                        (a.n + (FromGlobularIndex.gap a.n b.n).succ) +
                              (FromGlobularIndex.gap b.n c.n).succ := by
                        rw [← Nat.add_succ a.n (FromGlobularIndex.gap a.n b.n)]
                have hcanon :
                    GlobeCategoryPresented.GlobeCat.obj
                          (a.n +
                            (FromGlobularIndex.gap a.n b.n +
                              (FromGlobularIndex.gap b.n c.n).succ).succ) =
                      GlobeCategoryPresented.GlobeCat.obj
                          ((a.n + (FromGlobularIndex.gap a.n b.n).succ) +
                            (FromGlobularIndex.gap b.n c.n).succ) :=
                  congrArg GlobeCategoryPresented.GlobeCat.obj hcanonNat
                haveI : Mono (eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₃.symm) := by infer_instance
                apply (cancel_mono (eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₃.symm)).1
                simp [fromGlobularIndexMap, GlobularIndex.Hom.comp, Category.assoc]
                have hgap :
                    GlobeCategoryPresented.GlobeCat.canonMor a.n fb (FromGlobularIndex.gap a.n c.n) =
                      GlobeCategoryPresented.GlobeCat.canonMor a.n fb
                          (FromGlobularIndex.gap a.n b.n +
                            (FromGlobularIndex.gap b.n c.n).succ) ≫
                        eqToHom (C := GlobeCategoryPresented.GlobeCat) (by simp [hklen]) := by
                  simp [hklen]
                rw [hgap]
                symm
                -- Normalize `eqToHom` proof arguments (proof-irrelevance) so later rewrites match
                -- the named transports `hb₁`, `hb₂`, `hb₃`.
                have eqToHom_proof_irrel {X Y : GlobeCat} (p q : X = Y) :
                    (eqToHom (C := GlobeCategoryPresented.GlobeCat) p) =
                      (eqToHom (C := GlobeCategoryPresented.GlobeCat) q) := by
                  cases p
                  cases q
                  rfl
                rw [eqToHom_proof_irrel (q := hb₁)]
                rw [eqToHom_proof_irrel (q := hb₂.trans hb₃.symm)]
                -- Expand the composite transport back into `eqToHom hb₂ ≫ eqToHom hb₃.symm`.
                rw [← CategoryTheory.eqToHom_trans hb₂ hb₃.symm]
                have hmove_raw :
                    eqToHom (C := GlobeCategoryPresented.GlobeCat)
                        (by
                          simp [hk₁.symm] :
                            GlobeCategoryPresented.GlobeCat.obj
                                  (a.n + (FromGlobularIndex.gap a.n b.n).succ) =
                              GlobeCategoryPresented.GlobeCat.obj b.n) ≫
                        GlobeCategoryPresented.GlobeCat.canonMor b.n gb (FromGlobularIndex.gap b.n c.n) =
                      GlobeCategoryPresented.GlobeCat.canonMor
                              (a.n + (FromGlobularIndex.gap a.n b.n).succ) gb
                              (FromGlobularIndex.gap b.n c.n) ≫
                        eqToHom (C := GlobeCategoryPresented.GlobeCat)
                          (by
                            simp [hk₁.symm] :
                              GlobeCategoryPresented.GlobeCat.obj
                                    ((a.n + (FromGlobularIndex.gap a.n b.n).succ) +
                                      (FromGlobularIndex.gap b.n c.n).succ) =
                                GlobeCategoryPresented.GlobeCat.obj
                                    (b.n + (FromGlobularIndex.gap b.n c.n).succ)) := by
                  exact
                    (CategoryTheory.eqToHom_naturality (C := GlobeCategoryPresented.GlobeCat)
                      (f := fun n : Nat => GlobeCategoryPresented.GlobeCat.obj n)
                      (g := fun n : Nat =>
                        GlobeCategoryPresented.GlobeCat.obj (n + (FromGlobularIndex.gap b.n c.n).succ))
                      (z := fun n : Nat =>
                        GlobeCategoryPresented.GlobeCat.canonMor n gb (FromGlobularIndex.gap b.n c.n))
                      (j := a.n + (FromGlobularIndex.gap a.n b.n).succ) (j' := b.n) hk₁.symm).symm
                have hmove :
                    eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₁ ≫
                        GlobeCategoryPresented.GlobeCat.canonMor b.n gb (FromGlobularIndex.gap b.n c.n) =
                      GlobeCategoryPresented.GlobeCat.canonMor
                              (a.n + (FromGlobularIndex.gap a.n b.n).succ) gb
                              (FromGlobularIndex.gap b.n c.n) ≫
                        eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₁g := by
                  have hf :
                      (by
                          simp [hk₁.symm] :
                            GlobeCategoryPresented.GlobeCat.obj
                                  (a.n + (FromGlobularIndex.gap a.n b.n).succ) =
                              GlobeCategoryPresented.GlobeCat.obj b.n) =
                        hb₁ :=
                    Subsingleton.elim _ _
                  have hg :
                      (by
                          simp [hk₁.symm] :
                            GlobeCategoryPresented.GlobeCat.obj
                                  ((a.n + (FromGlobularIndex.gap a.n b.n).succ) +
                                    (FromGlobularIndex.gap b.n c.n).succ) =
                              GlobeCategoryPresented.GlobeCat.obj
                                  (b.n + (FromGlobularIndex.gap b.n c.n).succ)) =
                        hb₁g :=
                    Subsingleton.elim _ _
                  cases hf
                  cases hg
                  simp at hmove_raw
                  exact hmove_raw
                have htransport :
                    eqToHom (C := GlobeCategoryPresented.GlobeCat) hcanon ≫
                        eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₁g ≫
                          eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₂ ≫
                            eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₃.symm =
                      eqToHom (C := GlobeCategoryPresented.GlobeCat) (by simp [hklen]) := by
                  have hchain :
                      eqToHom (C := GlobeCategoryPresented.GlobeCat) hcanon ≫
                          eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₁g ≫
                            eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₂ ≫
                              eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₃.symm =
                        eqToHom (C := GlobeCategoryPresented.GlobeCat)
                          (hcanon.trans (hb₁g.trans (hb₂.trans hb₃.symm))) := by
                    simp
                  have heq :
                      hcanon.trans (hb₁g.trans (hb₂.trans hb₃.symm)) =
                        (by
                          simp [hklen] :
                            GlobeCategoryPresented.GlobeCat.obj
                                  (a.n +
                                    (FromGlobularIndex.gap a.n b.n +
                                      (FromGlobularIndex.gap b.n c.n).succ).succ) =
                              GlobeCategoryPresented.GlobeCat.obj
                                  (a.n + (FromGlobularIndex.gap a.n c.n).succ)) :=
                    Subsingleton.elim _ _
                  cases heq
                  exact hchain
                have hcompCanon :
                    GlobeCategoryPresented.GlobeCat.canonMor a.n fb (FromGlobularIndex.gap a.n b.n) ≫
                        GlobeCategoryPresented.GlobeCat.canonMor
                              (a.n + (FromGlobularIndex.gap a.n b.n).succ) gb
                              (FromGlobularIndex.gap b.n c.n) =
                      GlobeCategoryPresented.GlobeCat.canonMor a.n fb
                          (FromGlobularIndex.gap a.n b.n +
                            (FromGlobularIndex.gap b.n c.n).succ) ≫
                        eqToHom (C := GlobeCategoryPresented.GlobeCat) hcanon := by
                  classical
                  have h0 :=
                    GlobeCategoryPresented.GlobeCat.canonMor_comp_canonMor (n := a.n) (b₁ := fb) (b₂ := gb)
                      (k₁ := FromGlobularIndex.gap a.n b.n) (k₂ := FromGlobularIndex.gap b.n c.n)
                  convert h0 using 1
                have h1raw :=
                  congrArg
                    (fun t =>
                      GlobeCategoryPresented.GlobeCat.canonMor a.n fb (FromGlobularIndex.gap a.n b.n) ≫ t ≫
                        eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₂ ≫
                          eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₃.symm)
                    hmove
                have h1 :
                    GlobeCategoryPresented.GlobeCat.canonMor a.n fb (FromGlobularIndex.gap a.n b.n) ≫
                        eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₁ ≫
                          GlobeCategoryPresented.GlobeCat.canonMor b.n gb (FromGlobularIndex.gap b.n c.n) ≫
                            eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₂ ≫
                              eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₃.symm =
                      GlobeCategoryPresented.GlobeCat.canonMor a.n fb (FromGlobularIndex.gap a.n b.n) ≫
                        GlobeCategoryPresented.GlobeCat.canonMor
                              (a.n + (FromGlobularIndex.gap a.n b.n).succ) gb
                              (FromGlobularIndex.gap b.n c.n) ≫
                          eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₁g ≫
                              eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₂ ≫
                              eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₃.symm := by
                  simp only [Category.assoc] at h1raw
                  exact h1raw
                have h2raw :=
                  congrArg
                    (fun t =>
                      t ≫ eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₁g ≫
                        eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₂ ≫
                          eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₃.symm)
                    hcompCanon
                have h2 :
                    GlobeCategoryPresented.GlobeCat.canonMor a.n fb (FromGlobularIndex.gap a.n b.n) ≫
                        GlobeCategoryPresented.GlobeCat.canonMor
                              (a.n + (FromGlobularIndex.gap a.n b.n).succ) gb
                              (FromGlobularIndex.gap b.n c.n) ≫
                          eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₁g ≫
                            eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₂ ≫
                              eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₃.symm =
                      GlobeCategoryPresented.GlobeCat.canonMor a.n fb
                          (FromGlobularIndex.gap a.n b.n +
                            (FromGlobularIndex.gap b.n c.n).succ) ≫
                        eqToHom (C := GlobeCategoryPresented.GlobeCat) hcanon ≫
                          eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₁g ≫
                              eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₂ ≫
                              eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₃.symm := by
                  simp only [Category.assoc] at h2raw
                  exact h2raw
                have h3raw :=
                  congrArg
                    (fun t =>
                      GlobeCategoryPresented.GlobeCat.canonMor a.n fb
                          (FromGlobularIndex.gap a.n b.n +
                            (FromGlobularIndex.gap b.n c.n).succ) ≫ t)
                    htransport
                have h3 :
                    GlobeCategoryPresented.GlobeCat.canonMor a.n fb
                          (FromGlobularIndex.gap a.n b.n +
                            (FromGlobularIndex.gap b.n c.n).succ) ≫
                        eqToHom (C := GlobeCategoryPresented.GlobeCat) hcanon ≫
                          eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₁g ≫
                            eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₂ ≫
                              eqToHom (C := GlobeCategoryPresented.GlobeCat) hb₃.symm =
                      GlobeCategoryPresented.GlobeCat.canonMor a.n fb
                          (FromGlobularIndex.gap a.n b.n +
                            (FromGlobularIndex.gap b.n c.n).succ) ≫
                        eqToHom (C := GlobeCategoryPresented.GlobeCat) (by simp [hklen]) := by
                  exact h3raw
                exact h1.trans (h2.trans h3)

private theorem to_map_canonMor_kind (n : Nat) (b : Bool) :
    ∀ k : Nat, (toGlobularIndex.map (GlobeCategoryPresented.GlobeCat.canonMor n b k)).kind = some b := by
  intro k
  induction k with
  | zero =>
      cases b <;>
        simp [GlobeCategoryPresented.GlobeCat.canonMor, GlobeCategoryPresented.ToGlobularIndex.functor,
          GlobeCategoryPresented.GlobeCat.sigma, GlobeCategoryPresented.GlobeCat.tau,
          GlobeCategoryPresented.GlobeCat.quotientFunctor, CategoryTheory.Quotient.lift_map_functor_map,
          GlobularIndex.src, GlobularIndex.tgt, GlobularIndex.Hom.src, GlobularIndex.Hom.tgt]
  | succ k ih =>
      -- `canonMor` extends by `σ`, and `GlobularIndex` composition is left-biased.
      cases h : toGlobularIndex.map (GlobeCategoryPresented.GlobeCat.canonMor n b k) with
      | mk kind valid =>
          have hk : kind = some b := by simpa [h] using ih
          cases kind with
          | none => cases hk
          | some fb =>
              have hfb : fb = b := by cases hk; rfl
              -- compute the kind after appending `σ`
              have hcompKind :
                  (({ kind := some fb, valid := valid } : GlobularIndex.Hom _ _) ≫
                    toGlobularIndex.map (GlobeCategoryPresented.GlobeCat.sigma (n + k + 1))).kind =
                    some fb := by
                simpa [GlobularIndex.Hom.comp] using
                  (GlobularIndex.Hom.comp_kind_some fb valid
                    (toGlobularIndex.map (GlobeCategoryPresented.GlobeCat.sigma (n + k + 1))))
              -- unfold `canonMor` recursion and finish
              have hcanonSucc :
                  (toGlobularIndex.map (GlobeCategoryPresented.GlobeCat.canonMor n b (k + 1))).kind = some fb := by
                simpa [GlobeCategoryPresented.GlobeCat.canonMor, Functor.map_comp, Category.assoc, h] using hcompKind
              simpa [hfb] using hcanonSucc

private theorem from_to_id {X Y : GlobeCat} (f : X ⟶ Y) :
    fromGlobularIndex.map (toGlobularIndex.map f) = f := by
  classical
  -- Reduce to a representative path in the free path category.
  refine CategoryTheory.Quotient.induction (r := GlobeCategoryPresented.Rel)
    (P := fun {A B : GlobeCat} (f : A ⟶ B) =>
      fromGlobularIndex.map (toGlobularIndex.map f) = f) ?_ f
  intro a b p
  -- `a b : Obj` and `p : Quiver.Path a b`.
  -- Unfold `toGlobularIndex` on a quotient morphism.
  -- This is definitional for `Quotient.lift`.
  -- Goal becomes: `from.map (pathsFunctor.map p) = quotientFunctor.map p`.
  change fromGlobularIndex.map (GlobeCategoryPresented.ToGlobularIndex.pathsFunctor.map p) =
    GlobeCategoryPresented.GlobeCat.quotientFunctor.map p
  -- Work with the strict morphism computed by `pathsFunctor`.
  let g := GlobeCategoryPresented.ToGlobularIndex.pathsFunctor.map p
  cases hg : g with
  | mk gkind gvalid =>
      have hk :
          gkind =
            match p with
            | Quiver.Path.nil => none
            | _ => some (GlobeCategoryPresented.PathsCat.firstBool p) := by
        simpa [g, hg] using (GlobeCatEquivalence.pathsFunctor_kind (p := p))
      cases gkind with
      | none =>
          -- Only possible when `p` is the identity.
          cases p with
          | nil =>
              cases gvalid
              -- both sides are identities
              simp [fromGlobularIndex, fromGlobularIndexMap,
                GlobeCategoryPresented.ToGlobularIndex.pathsFunctor,
                CategoryTheory.Quotient.functor,
                CategoryStruct.id, GlobularIndex.Hom.id]
          | cons _ _ =>
              -- `pathsFunctor_kind` forces a nonempty path to have `some _` kind.
              cases hk
      | some fb =>
          cases p with
          | nil =>
              cases hk
          | cons p₀ e₀ =>
              -- Unpack the indices.
              cases a with
              | mk an =>
                cases b with
                | mk bn =>
                  have hfb : fb = GlobeCategoryPresented.PathsCat.firstBool (Quiver.Path.cons p₀ e₀) := by
                    have hk' :
                        some fb =
                          some (GlobeCategoryPresented.PathsCat.firstBool (Quiver.Path.cons p₀ e₀)) := by
                      simpa using hk
                    exact Option.some.inj hk'
                  have hab : an < bn := gvalid
                  let k : Nat := FromGlobularIndex.gap an bn
                  have hk' : bn = an + k.succ := FromGlobularIndex.gap_spec (a := an) (b := bn) hab

                  -- Object transport for the codomain (`bn = an + k.succ`).
                  have hbQ :
                      GlobeCategoryPresented.GlobeCat.obj bn =
                        GlobeCategoryPresented.GlobeCat.obj (an + k.succ) :=
                    congrArg GlobeCategoryPresented.GlobeCat.obj hk'

                  -- Normalize directly (no casts on the input path).
                  have hn :
                      GlobeCategoryPresented.GlobeCat.quotientFunctor.map (Quiver.Path.cons p₀ e₀) ≫
                        eqToHom (C := GlobeCategoryPresented.GlobeCat) hbQ =
                        GlobeCategoryPresented.GlobeCat.canonMor an
                          (GlobeCategoryPresented.PathsCat.firstBool (Quiver.Path.cons p₀ e₀)) k := by
                    simpa using
                      (GlobeCategoryPresented.GlobeCat.normalize_path_eqToHom
                        (n := an) (k := k) (m := bn) hk' (p := Quiver.Path.cons p₀ e₀))

                  have hfrom :
                      fromGlobularIndex.map
                          (GlobeCategoryPresented.ToGlobularIndex.pathsFunctor.map (Quiver.Path.cons p₀ e₀)) ≫
                        eqToHom (C := GlobeCategoryPresented.GlobeCat) hbQ =
                          GlobeCategoryPresented.GlobeCat.canonMor an
                            (GlobeCategoryPresented.PathsCat.firstBool (Quiver.Path.cons p₀ e₀)) k := by
                    have hrepr :
                        GlobeCategoryPresented.ToGlobularIndex.pathsFunctor.map (Quiver.Path.cons p₀ e₀) =
                          { kind := some fb, valid := hab } := by
                      have : g = { kind := some fb, valid := hab } := by
                        simpa [hab] using hg
                      simpa [g] using this
                    have hbQ' :
                        GlobeCategoryPresented.GlobeCat.obj (an + k.succ) =
                          GlobeCategoryPresented.GlobeCat.obj bn :=
                      congrArg GlobeCategoryPresented.GlobeCat.obj hk'.symm
                    -- Avoid rewriting `bn` in terms of `k`; use `comp_eqToHom_iff` to cancel transports.
                    have hbase :
                        fromGlobularIndex.map
                            (GlobeCategoryPresented.ToGlobularIndex.pathsFunctor.map (Quiver.Path.cons p₀ e₀)) =
                          GlobeCategoryPresented.GlobeCat.canonMor an fb k ≫
                            eqToHom (C := GlobeCategoryPresented.GlobeCat) hbQ' := by
                      -- First rewrite the strict morphism, then unfold `fromGlobularIndexMap` (avoid expanding `pathsFunctor.map`).
                      -- Reduce to a comparison of transports; then use proof irrelevance for the remaining equality proof.
                      simp [fromGlobularIndex, fromGlobularIndexMap, FromGlobularIndex.gap, k, hrepr]
                      -- Unfold objects computed by `pathsFunctor.obj`.
                      simp [GlobeCategoryPresented.ToGlobularIndex.pathsFunctor,
                        GlobeCategoryPresented.ToGlobularIndex.genPrefunctor]
                      -- The remaining `eqToHom` proof is definitional equal to `hbQ'` up to proof irrelevance.
                      rfl
                    have hstep :
                        fromGlobularIndex.map
                            (GlobeCategoryPresented.ToGlobularIndex.pathsFunctor.map (Quiver.Path.cons p₀ e₀)) ≫
                          eqToHom (C := GlobeCategoryPresented.GlobeCat) hbQ =
                            GlobeCategoryPresented.GlobeCat.canonMor an fb k := by
                      -- Transport cancellation without substituting `bn`.
                      refine (CategoryTheory.comp_eqToHom_iff (p := hbQ)
                        (f := fromGlobularIndex.map
                          (GlobeCategoryPresented.ToGlobularIndex.pathsFunctor.map (Quiver.Path.cons p₀ e₀)))
                        (g := GlobeCategoryPresented.GlobeCat.canonMor an fb k)).2 ?_
                      -- Now both sides land in `GlobeCat.obj bn`.
                      simpa [Category.assoc, hbQ'] using hbase
                    simpa [hfb] using hstep

                  haveI : Mono (eqToHom (C := GlobeCategoryPresented.GlobeCat) hbQ) := by infer_instance
                  exact (cancel_mono (eqToHom (C := GlobeCategoryPresented.GlobeCat) hbQ)).1
                    (by simpa [Category.assoc, hn] using hfrom)

private theorem to_from_id {X Y : GlobularIndex.Obj} (f : X ⟶ Y) :
    toGlobularIndex.map (fromGlobularIndex.map f) = f := by
  classical
  cases f with
  | mk kind valid =>
    cases kind with
    | none =>
        cases valid
        apply GlobularIndex.Hom.ext
        rfl
    | some fb =>
        have hab : X.n < Y.n := valid
        let k : Nat := FromGlobularIndex.gap X.n Y.n
        have hk : Y.n = X.n + k.succ := FromGlobularIndex.gap_spec (a := X.n) (b := Y.n) hab
        have hbQ :
            GlobeCategoryPresented.GlobeCat.obj (X.n + k.succ) =
              GlobeCategoryPresented.GlobeCat.obj Y.n :=
          congrArg GlobeCategoryPresented.GlobeCat.obj hk.symm
        apply GlobularIndex.Hom.ext
        have hkcanon :
            (toGlobularIndex.map (GlobeCategoryPresented.GlobeCat.canonMor X.n fb k)).kind = some fb :=
          to_map_canonMor_kind (n := X.n) (b := fb) k
        have hcomp :
            ((toGlobularIndex.map (GlobeCategoryPresented.GlobeCat.canonMor X.n fb k)) ≫
                toGlobularIndex.map (eqToHom (C := GlobeCategoryPresented.GlobeCat) hbQ)).kind =
              some fb := by
          cases hpre : (toGlobularIndex.map (GlobeCategoryPresented.GlobeCat.canonMor X.n fb k)) with
          | mk preKind preValid =>
              have hpreKind : preKind = some fb := by
                simpa [hpre] using hkcanon
              cases preKind with
              | none => cases hpreKind
              | some fb' =>
                  have hfb' : fb' = fb := by cases hpreKind; rfl
                  have :
                      (({ kind := some fb', valid := preValid } : GlobularIndex.Hom _ _) ≫
                          toGlobularIndex.map (eqToHom (C := GlobeCategoryPresented.GlobeCat) hbQ)).kind =
                        some fb' := by
                    simpa [GlobularIndex.Hom.comp] using
                      (GlobularIndex.Hom.comp_kind_some fb' preValid
                        (toGlobularIndex.map (eqToHom (C := GlobeCategoryPresented.GlobeCat) hbQ)))
                  simpa [hfb'] using this
        simpa [fromGlobularIndex, fromGlobularIndexMap, FromGlobularIndex.gap, k, hk, hbQ,
          Functor.map_comp, Category.assoc] using hcomp

noncomputable def globeCatEquivalence : GlobeCat ≌ GlobularIndex.Obj :=
  CategoryTheory.Equivalence.mk
    toGlobularIndex
    fromGlobularIndex
    (NatIso.ofComponents
      (fun X => Iso.refl X)
      (by
        intro X Y f
        simpa [Category.id_comp, Category.comp_id] using (from_to_id (X := X) (Y := Y) (f := f)).symm))
    (NatIso.ofComponents
      (fun X => Iso.refl X)
      (by
        intro X Y f
        calc
          toGlobularIndex.map (fromGlobularIndex.map f) ≫ 𝟙 Y =
              toGlobularIndex.map (fromGlobularIndex.map f) := by
                exact Category.comp_id (toGlobularIndex.map (fromGlobularIndex.map f))
          _ = f := to_from_id (X := X) (Y := Y) (f := f)
          _ = 𝟙 X ≫ f := by
                exact (Category.id_comp f).symm))

/-!
## Presheaf rebasing
-/

universe u

abbrev GlobularSetPshPresented :=
  (GlobeCatᵒᵖ ⥤ Type u)

noncomputable def globularPresheafRebase :
    GlobularSetPshPresented ≌ GlobularSetPsh.{u} :=
  (globeCatEquivalence.op).congrLeft

end GlobeCatEquivalence

end IteratedVirtual
end HeytingLean
