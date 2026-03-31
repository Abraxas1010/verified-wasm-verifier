import Std
import Mathlib.Data.List.Sort
import Mathlib.Data.String.Basic
import HeytingLean.Numbers.Surreal.CanonicalizeWF.Core

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Proofs

open List Surreal
open SurrealCore
open scoped Classical

noncomputable section

abbrev Pair := (String × SurrealCore.PreGame)

def PairLE (a b : Pair) : Prop := a.fst ≤ b.fst

@[inline] def pairLEb (a b : Pair) : Bool := decide (PairLE a b)

instance instIsTransPairLE : IsTrans Pair PairLE where
  trans := by
    intro a b c h₁ h₂
    exact le_trans h₁ h₂

instance instIsTotalPairLE : IsTotal Pair PairLE := by
  constructor
  intro a b
  simpa [PairLE] using le_total a.fst b.fst

instance instDecidablePairLE : DecidableRel PairLE := by
  intro a b; classical
  exact inferInstance

/-- Proof-only mergeSort by key; relies on mathlib lemmas. -/
def sortPairsMS (xs : List Pair) : List Pair :=
  xs.mergeSort pairLEb

/-- Proof-only dedup that drops subsequent entries sharing the head's key. -/
def dedupSorted : List Pair → List Pair
  | [] => []
  | x :: xs =>
      x :: dedupSorted (xs.dropWhile (fun y => y.fst = x.fst))
termination_by xs => xs.length
decreasing_by
  simp_wf
  have h := List.length_dropWhile_le (fun y => y.fst = x.fst) xs
  exact Nat.lt_of_le_of_lt h (Nat.lt_succ_self _)

@[inline] def keys (xs : List Pair) : List String :=
  xs.map Prod.fst

@[inline] def fkeys (ys : List SurrealCore.PreGame) : List String :=
  ys.map key

@[inline] def mkPairs (ys : List SurrealCore.PreGame) : List Pair :=
  ys.map fun g => (key g, g)

@[inline] def normPairsMS (ys : List SurrealCore.PreGame) : List Pair :=
  dedupSorted (sortPairsMS (mkPairs ys))

/-- Core `pairLEb` coincides with the proof-only copy. -/
lemma pairLEb_eq_surreal : pairLEb = Surreal.pairLEb := by
  funext a b
  simp [pairLEb, Surreal.pairLEb, PairLE]

/-- Proof-only mergeSort equals the core mergeSort. -/
lemma sortPairsMS_eq_surreal (xs : List Pair) :
    sortPairsMS xs = Surreal.sortPairsMS xs := by
  simp [sortPairsMS, Surreal.sortPairsMS, pairLEb_eq_surreal]

/-- Proof-only `mkPairs` agrees with the core version. -/
lemma mkPairs_eq_surreal (ys : List SurrealCore.PreGame) :
    mkPairs ys = Surreal.mkPairs ys := rfl

/-- Proof-only `dedupSorted` agrees extensionally with the core version. -/
lemma dedupSorted_eq_surreal :
    ∀ xs : List Pair, dedupSorted xs = Surreal.dedupSorted xs
  | [] => by simp [dedupSorted, Surreal.dedupSorted]
  | x :: xs => by
      have htail :
          dedupSorted (xs.dropWhile (fun y => y.fst = x.fst)) =
            Surreal.dedupSorted (xs.dropWhile (fun y => y.fst = x.fst)) :=
        dedupSorted_eq_surreal (xs := xs.dropWhile (fun y => y.fst = x.fst))
      simp [dedupSorted, Surreal.dedupSorted, htail]
termination_by xs => xs.length
decreasing_by
  simp_wf
  have h := List.length_dropWhile_le (fun y => y.fst = x.fst) xs
  exact Nat.lt_of_le_of_lt h (Nat.lt_succ_self _)

/-- Proof-only `normPairsMS` agrees with the core normalizer. -/
lemma normPairsMS_eq_surreal (ys : List SurrealCore.PreGame) :
    normPairsMS ys = Surreal.normPairsMS ys := by
  simp [normPairsMS, Surreal.normPairsMS, mkPairs, Surreal.mkPairs,
        dedupSorted_eq_surreal, sortPairsMS_eq_surreal]

/-- Proof-only `normListMS` agrees with the core version. -/
lemma normListMS_eq_surreal (ys : List SurrealCore.PreGame) :
    normListMS ys = Surreal.normListMS ys := by
  simp [normListMS, Surreal.normListMS]

/-- `dedupSorted` never introduces new elements; it stays a sublist of the input. -/
lemma dedupSorted_sublist :
    ∀ xs : List Pair, dedupSorted xs <+ xs
  | [] => by simp [dedupSorted]
  | x :: xs => by
      classical
      have htail :
          dedupSorted (xs.dropWhile (fun y => y.fst = x.fst))
              <+ xs.dropWhile (fun y => y.fst = x.fst) :=
        dedupSorted_sublist _
      have htail' :
          dedupSorted (xs.dropWhile (fun y => y.fst = x.fst))
              <+ xs :=
        htail.trans (List.dropWhile_sublist _)
      have :
          x :: dedupSorted (xs.dropWhile (fun y => y.fst = x.fst))
              <+ x :: xs :=
        (List.cons_sublist_cons).2 htail'
      simpa [dedupSorted]
termination_by xs => xs.length
decreasing_by
  simp_wf
  have h := List.length_dropWhile_le (fun y => y.fst = x.fst) xs
  exact Nat.lt_of_le_of_lt h (Nat.lt_succ_self _)

/-- Proof-only normalizer built from mergeSort + structural dedup. -/
def normListMS (ys : List SurrealCore.PreGame) : List SurrealCore.PreGame :=
  (dedupSorted (sortPairsMS (ys.map (fun g => (key g, g))))).map Prod.snd

/-- mergeSort output is pairwise nondecreasing. -/
theorem sortPairsMS_pairwise (xs : List Pair) :
    (sortPairsMS xs).Pairwise (fun a b => PairLE a b) := by
  classical
  have htrans :
      ∀ a b c, pairLEb a b = true → pairLEb b c = true → pairLEb a c = true := by
    intro a b c hab hbc
    have hab' : PairLE a b := of_decide_eq_true hab
    have hbc' : PairLE b c := of_decide_eq_true hbc
    have : PairLE a c := le_trans hab' hbc'
    simp [pairLEb, this]
  have htotal :
      ∀ a b, (pairLEb a b || pairLEb b a) = true := by
    intro a b
    obtain h | h := le_total a.fst b.fst
    · have : pairLEb a b = true := by simp [pairLEb, PairLE, h]
      simp [this]
    · have : pairLEb b a = true := by simp [pairLEb, PairLE, h]
      simp [this]
  have hsorted :
      (sortPairsMS xs).Pairwise (fun a b => pairLEb a b = true) := by
    simpa [sortPairsMS] using
      (List.sorted_mergeSort (le := pairLEb) htrans htotal xs)
  exact hsorted.imp (by
    intro a b h
    exact of_decide_eq_true h)

/-- mergeSort on pairs is a permutation of the input. -/
lemma sortPairsMS_perm (xs : List Pair) :
    sortPairsMS xs ~ xs := by
  classical
  simpa [sortPairsMS, pairLEb] using
    (List.mergeSort_perm xs pairLEb)

/-- Filtering preserves pairwise relations. -/
theorem pairwise_filter {α} {r : α → α → Prop}
    (p : α → Bool) (xs : List α) (h : xs.Pairwise r) :
    (xs.filter (fun x => p x)).Pairwise r := by
  have hsorted : List.Sorted r xs := by
    simpa [List.Sorted, Sorted] using h
  have hsorted' : List.Sorted r (xs.filter (fun x => p x)) :=
    List.Sorted.filter _ hsorted
  simpa [List.Sorted, Sorted] using hsorted'

/-- dedupSorted keeps pairwise-≤. -/
theorem dedupSorted_pairwise (xs : List Pair)
    (h : xs.Pairwise (fun a b => PairLE a b)) :
    (dedupSorted xs).Pairwise (fun a b => PairLE a b) := by
  exact h.sublist (dedupSorted_sublist xs)

section KeysOnly

open List

/-- Projecting a pairwise-`PairLE` list of pairs to keys keeps the keys pairwise nondecreasing. -/
lemma keys_pairwise_of_pairwise :
    ∀ xs : List Pair, xs.Pairwise PairLE →
      (keys xs).Pairwise (· ≤ ·)
  | [] => by intro _; simp [keys]
  | x :: xs => by
      intro h
      have hcons := List.pairwise_cons.1 h
      have hx := hcons.1
      have htail := hcons.2
      apply List.pairwise_cons.2
      constructor
      · intro k hk
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hk
        exact hx _ hy
      · simpa [keys] using
          (keys_pairwise_of_pairwise (xs := xs) htail)

/-- Dropping pairs whose key matches `x`'s key mirrors dropping those keys from the projected list. -/
lemma keys_dropWhile_keys (x : Pair) :
    ∀ xs : List Pair,
      keys (xs.dropWhile (fun y => y.fst = x.fst)) =
        (keys xs).dropWhile (fun k => k = x.fst)
  | [] => by simp [keys]
  | y :: ys => by
      classical
      by_cases hy : y.fst = x.fst
      ·
          simp [keys, List.dropWhile, hy]
          exact keys_dropWhile_keys (x := x) (xs := ys)
      · simp [keys, List.dropWhile, hy]

/-- Filtering out the key `a` leaves a list unchanged if none of its entries equal `a`. -/
lemma filter_beq_eq_self_of_forall_ne (a : String) :
    ∀ {ks : List String},
      (∀ k ∈ ks, k ≠ a) →
        ks.filter (fun k => !(k == a)) = ks
  | [], _ => by simp
  | k :: ks, h => by
      classical
      have hk : k ≠ a := h _ (by simp)
      have htail :
          ∀ k' ∈ ks, k' ≠ a := by
        intro k' hk'
        exact h _ (by simp [hk'])
      have hind :=
        filter_beq_eq_self_of_forall_ne a (ks := ks) htail
      have hkbeq : (k == a) = false := by
        by_cases hk' : k = a
        · exact (hk hk').elim
        · simp [hk']
      simp [List.filter, hkbeq, hind]

/-- For a pairwise-sorted key list headed by `a`, dropping leading `a`s matches filtering them out. -/
lemma dropWhile_eq_filter_ne_of_pairwise
    {a : String} :
    ∀ {ks : List String},
      (a :: ks).Pairwise (· ≤ ·) →
        ks.dropWhile (fun k => k = a) =
          ks.filter (fun k => !(k == a))
  | [], _ => by simp
  | k :: ks, h => by
      classical
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.1 h
      by_cases hk : k = a
      ·
        have hk' := hk
        subst hk'
        simpa [List.dropWhile, List.filter] using
          dropWhile_eq_filter_ne_of_pairwise (a := k) (ks := ks) htail
      · have hno :
          ∀ y ∈ ks, y ≠ a := by
            intro y hy
            intro hy'
            have ha_le_k : a ≤ k := hhead _ (by simp)
            have hk_le_y :
                k ≤ y := (List.pairwise_cons.1 htail).1 _ hy
            have hk_le_a :
                k ≤ a := by simpa [hy'] using hk_le_y
            have : k = a := le_antisymm hk_le_a ha_le_k
            exact hk this
        have hfilter :=
          filter_beq_eq_self_of_forall_ne a (ks := ks) hno
        have hkbeq : (k == a) = false := by
          by_cases hk' : k = a
          · exact (hk hk').elim
          · simp [hk']
        have hdec :
            decide (k = a) = false :=
          (decide_eq_false_iff_not (p := k = a)).2 hk
        have hdropEq :
            dropWhile (fun k => decide (k = a)) (k :: ks) = k :: ks := by
          simp [List.dropWhile, hdec]
        have hfilterEq :
            filter (fun k => !(k == a)) (k :: ks) = k :: ks := by
          simp [List.filter, hkbeq, hfilter]
        calc
          dropWhile (fun k => decide (k = a)) (k :: ks)
              = k :: ks := hdropEq
          _ = filter (fun k => !(k == a)) (k :: ks) :=
              hfilterEq.symm

/-- Deduplicating a sorted list of pairs has the same effect as erasing duplicate keys. -/
lemma keys_dedupSorted_eq_eraseDups_keys :
    ∀ {xs : List Pair},
      xs.Pairwise PairLE →
        keys (dedupSorted xs) = (keys xs).eraseDups
  | [], _ => by simp [keys, dedupSorted]
  | x :: xs, h => by
      classical
      have hx_tail :
          xs.Pairwise PairLE := (List.pairwise_cons.1 h).2
      have hdrop :
          (xs.dropWhile (fun y => y.fst = x.fst)).Pairwise PairLE :=
        hx_tail.sublist (List.dropWhile_sublist _)
      have hkeys_pair :
          (x.fst :: keys xs).Pairwise (· ≤ ·) := by
        simpa [keys] using
          (keys_pairwise_of_pairwise (x :: xs) h)
      have hdrop_keys :
          keys (xs.dropWhile (fun y => y.fst = x.fst)) =
            (keys xs).dropWhile (fun k => k = x.fst) :=
        keys_dropWhile_keys (x := x) (xs := xs)
      have hdrop_filter :
          (keys xs).dropWhile (fun k => k = x.fst) =
            (keys xs).filter (fun k => !(k == x.fst)) :=
        dropWhile_eq_filter_ne_of_pairwise
          (a := x.fst) (ks := keys xs) hkeys_pair
      have hrec :
          keys (dedupSorted (xs.dropWhile (fun y => y.fst = x.fst))) =
            ((keys xs).dropWhile (fun k => k = x.fst)).eraseDups := by
        simpa [hdrop_keys] using
          keys_dedupSorted_eq_eraseDups_keys
            (xs := xs.dropWhile (fun y => y.fst = x.fst))
            hdrop
      have hfilter_bool :
          (keys xs).filter (fun k => !(k == x.fst)) =
            (keys xs).dropWhile (fun k => k = x.fst) :=
        hdrop_filter.symm
      calc
        keys (dedupSorted (x :: xs))
            = x.fst :: keys (dedupSorted (xs.dropWhile (fun y => y.fst = x.fst))) := by
                simp [dedupSorted, keys]
        _ = x.fst ::
            ((keys xs).dropWhile (fun k => k = x.fst)).eraseDups := by
                simp [hrec]
        _ = x.fst ::
            ((keys xs).filter (fun k => !(k == x.fst))).eraseDups := by
                simp [hdrop_filter]
        _ = (keys (x :: xs)).eraseDups := by
                simp [keys, List.eraseDups_cons]
termination_by xs => xs.length
decreasing_by
  simp_wf
  have hlen :
      (xs.dropWhile (fun y => y.fst = x.fst)).length ≤ xs.length :=
    List.length_dropWhile_le _ _
  exact lt_of_le_of_lt hlen (Nat.lt_succ_self _)

/-- Keys become `Nodup` after `dedupSorted`. -/
theorem dedupSorted_keys_nodup :
    ∀ xs : List Pair,
      xs.Pairwise PairLE →
        (keys (dedupSorted xs)).Nodup
  | [], _ => by simp [dedupSorted, keys]
  | x :: xs, h => by
      classical
      have htail :
          xs.Pairwise PairLE := (List.pairwise_cons.1 h).2
      have hdrop_pair :
          (xs.dropWhile (fun y => y.fst = x.fst)).Pairwise PairLE :=
        htail.sublist (List.dropWhile_sublist _)
      have hrec :
          (keys (dedupSorted (xs.dropWhile (fun y => y.fst = x.fst)))).Nodup :=
        dedupSorted_keys_nodup
          (xs := xs.dropWhile (fun y => y.fst = x.fst))
          hdrop_pair
      have hkeys_pair :
          (x.fst :: keys xs).Pairwise (· ≤ ·) := by
        simpa [keys] using
          (keys_pairwise_of_pairwise (x :: xs) h)
      have hdrop_keys :
          keys (xs.dropWhile (fun y => y.fst = x.fst)) =
            (keys xs).dropWhile (fun k => k = x.fst) :=
        keys_dropWhile_keys (x := x) (xs := xs)
      have hdrop_filter :
          (keys xs).dropWhile (fun k => k = x.fst) =
            (keys xs).filter (fun k => !(k == x.fst)) :=
        dropWhile_eq_filter_ne_of_pairwise
          (a := x.fst) (ks := keys xs) hkeys_pair
      have hnotmem_drop :
          x.fst ∉ keys (xs.dropWhile (fun y => y.fst = x.fst)) := by
        have : x.fst ∉ (keys xs).filter (fun k => !(k == x.fst)) := by
          simp
        simp [hdrop_keys, hdrop_filter]
      have hsub :
          keys (dedupSorted (xs.dropWhile (fun y => y.fst = x.fst))) <+
            keys (xs.dropWhile (fun y => y.fst = x.fst)) := by
        simpa [keys] using
          (dedupSorted_sublist
            (xs := xs.dropWhile (fun y => y.fst = x.fst))).map Prod.fst
      have hnotmem_tail :
          x.fst ∉ keys (dedupSorted (xs.dropWhile (fun y => y.fst = x.fst))) := by
        intro hx
        exact hnotmem_drop (hsub.subset hx)
      have hkeys_cons :
          keys (dedupSorted (x :: xs)) =
            x.fst ::
              keys (dedupSorted (xs.dropWhile (fun y => y.fst = x.fst))) := by
        simp [dedupSorted, keys]
      refine hkeys_cons ▸ ?_
      apply List.nodup_cons.2
      constructor
      · exact hnotmem_tail
      · exact hrec
termination_by xs => xs.length
decreasing_by
  simp_wf
  have hlen :
      (xs.dropWhile (fun y => y.fst = x.fst)).length ≤ xs.length :=
    List.length_dropWhile_le _ _
  exact lt_of_le_of_lt hlen (Nat.lt_succ_self _)

instance instIsTransStringLE : IsTrans String (fun a b => a ≤ b) where
  trans := by
    intro a b c h₁ h₂
    exact le_trans h₁ h₂

instance instIsTotalStringLE :
    IsTotal String (fun a b => a ≤ b) := by
  refine ⟨?_⟩
  intro a b
  exact le_total a b

instance instIsAntisymmStringLE :
    IsAntisymm String (fun a b => a ≤ b) where
  antisymm := by
    intro a b h₁ h₂
    exact le_antisymm h₁ h₂

/-- Sort keys using `mergeSort` with the standard string order. -/
def sortKeys (ks : List String) : List String :=
  ks.mergeSort (· ≤ ·)

/-- Normalize keys by sorting and erasing duplicates (keeps the first occurrence). -/
def normKeys (ks : List String) : List String :=
  (sortKeys ks).eraseDups

/-- mergeSort produces a pairwise-nondecreasing list of keys. -/
lemma sortKeys_pairwise (ks : List String) :
    (sortKeys ks).Pairwise (· ≤ ·) := by
  classical
  have hsorted :
      List.Sorted (· ≤ ·) (sortKeys ks) := by
    simpa [sortKeys, List.Sorted, Sorted] using
      (List.sorted_mergeSort'
        (r := fun a b : String => a ≤ b) (l := ks))
  simpa [List.Sorted, Sorted] using hsorted

lemma sortKeys_perm (ks : List String) :
    sortKeys ks ~ ks := by
  classical
  simpa [sortKeys] using
    (List.mergeSort_perm ks (fun a b : String => a ≤ b))

/-- `eraseDups` does not introduce new keys; it stays a sublist. -/
lemma eraseDups_sublist :
    ∀ ks : List String, ks.eraseDups <+ ks
  | [] => by simp
  | k :: ks => by
      classical
      have htail :
          (ks.filter fun k' => !(k' == k)).eraseDups
            <+ ks.filter fun k' => !(k' == k) :=
        eraseDups_sublist _
      have htail' :
          (ks.filter fun k' => !(k' == k)).eraseDups <+ ks :=
        htail.trans
          (List.filter_sublist (p := fun k' => !(k' == k)) (l := ks))
      have hcons :
          k :: (ks.filter fun k' => !(k' == k)).eraseDups
              <+ k :: ks :=
        (List.cons_sublist_cons).2 htail'
      simpa [List.eraseDups_cons] using hcons
termination_by ks => ks.length
decreasing_by
  simp_wf
  have hlen :
      (ks.filter fun k' => !(k' == k)).length ≤ ks.length :=
    List.length_filter_le _ ks
  exact lt_of_le_of_lt hlen (Nat.lt_succ_self _)

/-- `eraseDups` on strings produces a nodup list. -/
lemma eraseDups_nodup :
    ∀ ks : List String, (ks.eraseDups).Nodup
  | [] => by simp
  | k :: ks => by
      classical
      have htail_nodup :
          ((ks.filter fun k' => !(k' == k)).eraseDups).Nodup :=
        eraseDups_nodup (ks.filter fun k' => !(k' == k))
      have htail_sub :
          (ks.filter fun k' => !(k' == k)).eraseDups
            <+ ks.filter fun k' => !(k' == k) :=
        eraseDups_sublist (ks.filter fun k' => !(k' == k))
      have hnotmem :
          k ∉ (ks.filter fun k' => !(k' == k)) := by simp
      have hnotmem_tail :
          k ∉ (ks.filter fun k' => !(k' == k)).eraseDups :=
        fun hk => hnotmem (htail_sub.subset hk)
      simpa [List.eraseDups_cons] using
        (List.nodup_cons.2 ⟨hnotmem_tail, htail_nodup⟩)
termination_by ks => ks.length
decreasing_by
  simp_wf
  have hlen :
      (ks.filter fun k' => !(k' == k)).length ≤ ks.length :=
    List.length_filter_le _ ks
  exact lt_of_le_of_lt hlen (Nat.lt_succ_self _)

/-- If a string list is already `Nodup`, `eraseDups` is a no-op. -/
lemma eraseDups_eq_self_of_nodup {ks : List String}
    (h : ks.Nodup) :
    ks.eraseDups = ks := by
  classical
  induction ks with
  | nil => simp
  | cons k ks ih =>
      obtain ⟨hnotmem, htail⟩ := List.nodup_cons.1 h
      have htail_eq : ks.eraseDups = ks := ih htail
      have hfilter :
          ks.filter (fun k' => !(k' == k)) = ks := by
        apply filter_beq_eq_self_of_forall_ne (a := k)
        intro k' hk'
        intro hk
        exact hnotmem (by simpa [hk] using hk')
      simp [List.eraseDups_cons, hfilter, htail_eq]

/-- On already-sorted key lists, normalization agrees with `eraseDups`. -/
lemma normKeys_eq_dedup_of_pairwise {ks : List String}
    (h : ks.Pairwise (· ≤ ·)) :
    normKeys ks = ks.eraseDups := by
  classical
  unfold normKeys
  have h_perm : sortKeys ks ~ ks := sortKeys_perm ks
  have h_sorted_sort :
      List.Sorted (· ≤ ·) (sortKeys ks) := by
    simpa [List.Sorted, Sorted, sortKeys]
      using
        (List.sorted_mergeSort'
          (r := fun a b : String => a ≤ b) (l := ks))
  have h_sorted_ks :
      List.Sorted (· ≤ ·) ks := by
    simpa [List.Sorted, Sorted] using h
  have hsortEq :
      sortKeys ks = ks :=
    List.eq_of_perm_of_sorted
      h_perm h_sorted_sort h_sorted_ks
  simp [hsortEq]

/-- Sorting + eraseDups is a fixed point on keys. -/
lemma normKeys_idem (ks : List String) :
    normKeys (normKeys ks) = normKeys ks := by
  classical
  have hpair_sort : (sortKeys ks).Pairwise (· ≤ ·) :=
    sortKeys_pairwise ks
  have hpair_norm :
      (normKeys ks).Pairwise (· ≤ ·) :=
    hpair_sort.sublist (eraseDups_sublist (sortKeys ks))
  have hsorted_norm :
      List.Sorted (· ≤ ·) (normKeys ks) := by
    simpa [List.Sorted, Sorted] using hpair_norm
  have hsorted_sort :
      List.Sorted (· ≤ ·) (sortKeys (normKeys ks)) := by
    simpa [List.Sorted, Sorted] using sortKeys_pairwise (normKeys ks)
  have hperm_sort :
      sortKeys (normKeys ks) ~ normKeys ks :=
    sortKeys_perm (normKeys ks)
  have hsort_eq :
      sortKeys (normKeys ks) = normKeys ks :=
    List.eq_of_perm_of_sorted hperm_sort hsorted_sort hsorted_norm
  have hnodup_norm : (normKeys ks).Nodup := by
    simpa [normKeys] using eraseDups_nodup (sortKeys ks)
  calc
    normKeys (normKeys ks)
        = (sortKeys (normKeys ks)).eraseDups := rfl
    _ = (normKeys ks).eraseDups := by simp [hsort_eq]
    _ = normKeys ks := eraseDups_eq_self_of_nodup hnodup_norm

/-- Normalization respects permutations of key lists. -/
lemma normKeys_perm {ks ks' : List String}
    (h : ks ~ ks') :
    normKeys ks = normKeys ks' := by
  classical
  unfold normKeys
  have hperm_left := sortKeys_perm ks
  have hperm_right := sortKeys_perm ks'
  have hperm :
      sortKeys ks ~ sortKeys ks' :=
    hperm_left.trans (h.trans hperm_right.symm)
  have hsorted_left :
      List.Sorted (· ≤ ·) (sortKeys ks) := by
    simpa [sortKeys, List.Sorted, Sorted]
      using
        (List.sorted_mergeSort'
          (r := fun a b : String => a ≤ b) (l := ks))
  have hsorted_right :
      List.Sorted (· ≤ ·) (sortKeys ks') := by
    simpa [sortKeys, List.Sorted, Sorted]
      using
        (List.sorted_mergeSort'
          (r := fun a b : String => a ≤ b) (l := ks'))
  have hsortEq :
      sortKeys ks = sortKeys ks' :=
    List.eq_of_perm_of_sorted hperm hsorted_left hsorted_right
  simp [hsortEq]

/-- Keys commute with mergeSort on pairs when the comparator is on the first component. -/
lemma keys_sortPairsMS (xs : List Pair) :
    keys (sortPairsMS xs) = sortKeys (keys xs) := by
  classical
  have hperm_pairs : sortPairsMS xs ~ xs :=
    sortPairsMS_perm xs
  have hperm_keys :
      keys (sortPairsMS xs) ~ keys xs :=
    hperm_pairs.map _
  have hperm :
      keys (sortPairsMS xs) ~ sortKeys (keys xs) :=
    hperm_keys.trans (sortKeys_perm (keys xs)).symm
  have hsorted_left :
      List.Sorted (· ≤ ·) (keys (sortPairsMS xs)) := by
    simpa [List.Sorted, Sorted] using
      (keys_pairwise_of_pairwise
        (xs := sortPairsMS xs)
        (sortPairsMS_pairwise xs))
  have hsorted_right :
      List.Sorted (· ≤ ·) (sortKeys (keys xs)) := by
    simpa [List.Sorted, Sorted] using
      (sortKeys_pairwise (keys xs))
  exact List.eq_of_perm_of_sorted hperm hsorted_left hsorted_right

/-- Keys of `mkPairs` are just the PreGame fingerprints. -/
lemma keys_mkPairs (ys : List SurrealCore.PreGame) :
    keys (mkPairs ys) = fkeys ys := by
  simp [keys, mkPairs, fkeys]

/-- Keys of the pair normalizer equal normalized keys of the input pairs. -/
lemma keys_normPairsMS (ys : List SurrealCore.PreGame) :
    keys (normPairsMS ys) = normKeys (keys (mkPairs ys)) := by
  classical
  have h :=
    keys_dedupSorted_eq_eraseDups_keys
      (xs := sortPairsMS (mkPairs ys))
      (sortPairsMS_pairwise (mkPairs ys))
  simpa [normPairsMS, normKeys, keys_sortPairsMS] using h

/-- Every pair produced by `normPairsMS` has a key matching the `key` of its payload component. -/
lemma key_snd_eq_fst_of_mem_normPairsMS
    {ys : List SurrealCore.PreGame} {p : Pair}
    (hp : p ∈ normPairsMS ys) :
    key p.snd = p.fst := by
  classical
  have hsub :
      normPairsMS ys <+ sortPairsMS (mkPairs ys) := by
    simpa [normPairsMS] using
      dedupSorted_sublist (sortPairsMS (mkPairs ys))
  have hmem_sort :
      p ∈ sortPairsMS (mkPairs ys) := hsub.subset hp
  have hperm := sortPairsMS_perm (mkPairs ys)
  have hmem :
      p ∈ mkPairs ys :=
        (List.Perm.mem_iff hperm).1 hmem_sort
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hmem
  simp

end KeysOnly

/-- If every element in `xs` has a key different from `x`, `dropWhile` is the identity. -/
lemma dropWhile_eq_self_of_forall_key_ne
    {x : Pair} :
    ∀ {xs : List Pair},
      (∀ y ∈ xs, y.fst ≠ x.fst) →
        xs.dropWhile (fun y => y.fst = x.fst) = xs
  | [], _ => by simp
  | y :: ys, h => by
      have hy : y.fst ≠ x.fst := h _ (by simp)
      simp [List.dropWhile, hy]

/-- On a pairwise-sorted list whose keys are already `Nodup`, `dedupSorted` is a no-op. -/
lemma dedupSorted_eq_of_pairwise_and_keys_nodup
    : ∀ {xs : List Pair},
        xs.Pairwise PairLE →
          (keys xs).Nodup →
            dedupSorted xs = xs
  | [], _, _ => by
      simp [dedupSorted]
  | x :: xs, hpair, hnodup => by
      classical
      have hpair_tail :
          xs.Pairwise PairLE := (List.pairwise_cons.1 hpair).2
      have hnodup_cons :
          x.fst ∉ keys xs ∧ (keys xs).Nodup :=
        List.nodup_cons.1 (by simpa [keys] using hnodup)
      have hdrop :
          xs.dropWhile (fun y => y.fst = x.fst) = xs := by
        have hdisj : ∀ y ∈ xs, y.fst ≠ x.fst := by
          intro y hy hykey
          exact hnodup_cons.1
            (by
              apply List.mem_map.2
              exact ⟨y, hy, hykey⟩)
        exact dropWhile_eq_self_of_forall_key_ne
          (x := x) (xs := xs) hdisj
      have hrec :
          dedupSorted xs = xs :=
        dedupSorted_eq_of_pairwise_and_keys_nodup
          (xs := xs) hpair_tail hnodup_cons.2
      simp [dedupSorted, hdrop, hrec]

/-- `dedupSorted` is idempotent on sorted inputs. -/
theorem dedupSorted_idem (xs : List Pair)
    (h : xs.Pairwise PairLE) :
    dedupSorted (dedupSorted xs) = dedupSorted xs := by
  classical
  have hpair : (dedupSorted xs).Pairwise PairLE :=
    dedupSorted_pairwise (xs := xs) h
  have hnodup : (keys (dedupSorted xs)).Nodup :=
    dedupSorted_keys_nodup (xs := xs) h
  have hfix :
      dedupSorted (dedupSorted xs) = dedupSorted xs :=
    dedupSorted_eq_of_pairwise_and_keys_nodup
      (xs := dedupSorted xs) hpair hnodup
  simpa using hfix

/-- Rebuilding pairs from their payloads leaves a pair list unchanged if the keys line up. -/
theorem mkPairs_map_snd_eq_self
    {ps : List Pair}
    (hkey : ∀ p ∈ ps, key p.snd = p.fst) :
    mkPairs (ps.map Prod.snd) = ps := by
  classical
  induction ps with
  | nil =>
      simp [mkPairs]
  | cons p ps ih =>
      -- the head payload's key matches its stored key
      have hhead : key p.snd = p.fst := hkey _ (by simp)
      -- the induction hypothesis applies to the tail
      have htail : ∀ p' ∈ ps, key p'.snd = p'.fst := by
        intro p' hp'
        exact hkey _ (by simp [hp'])
      have hih : mkPairs (ps.map Prod.snd) = ps := ih htail
      have hih' :
          (ps.map Prod.snd).map (fun g => (key g, g)) = ps := by
        simpa [mkPairs] using hih
      cases p with
      | _ k g =>
          -- rebuild and simplify
          simp [mkPairs, hhead, hih']

/-- Proof-only normalizer is idempotent. -/
theorem normListMS_idem (ys : List PreGame) :
    normListMS (normListMS ys) = normListMS ys := by
  classical
  -- rebuild pairs from the inner normalization
  have hkey :
      ∀ p ∈ normPairsMS ys, key p.snd = p.fst :=
    fun p hp => key_snd_eq_fst_of_mem_normPairsMS (ys := ys) hp
  have hmk : mkPairs (normListMS ys) = normPairsMS ys := by
    have hmap :
        mkPairs ((normPairsMS ys).map Prod.snd) = normPairsMS ys :=
      mkPairs_map_snd_eq_self (ps := normPairsMS ys) (hkey := hkey)
    simpa [normListMS] using hmap
  -- normalize the pair list a second time; sorted + dedup is a fixed point
  have hpair : (normPairsMS ys).Pairwise PairLE :=
    dedupSorted_pairwise _ (sortPairsMS_pairwise (mkPairs ys))
  have hsort : sortPairsMS (normPairsMS ys) = normPairsMS ys := by
    classical
      have hbool :
          (normPairsMS ys).Pairwise (fun a b => pairLEb a b = true) :=
        hpair.imp (by
          intro a b h
          simp [pairLEb, h])
    simpa [sortPairsMS] using
      (List.mergeSort_of_sorted (le := pairLEb) hbool)
  have hnodup : (keys (normPairsMS ys)).Nodup := by
    -- normPairsMS is a dedup of a sorted list
    have :
        (keys
          (dedupSorted (sortPairsMS (mkPairs ys)))).Nodup :=
      dedupSorted_keys_nodup
        (xs := sortPairsMS (mkPairs ys))
        (sortPairsMS_pairwise (mkPairs ys))
    simpa [normPairsMS] using this
  have hdedup : dedupSorted (normPairsMS ys) = normPairsMS ys :=
    dedupSorted_eq_of_pairwise_and_keys_nodup
      (xs := normPairsMS ys) hpair hnodup
  have hpairNorm :
      normPairsMS (normListMS ys) = normPairsMS ys := by
    calc
      normPairsMS (normListMS ys)
          = dedupSorted (sortPairsMS (mkPairs (normListMS ys))) := rfl
      _ = dedupSorted (sortPairsMS (normPairsMS ys)) := by
          simp [hmk]
      _ = dedupSorted (normPairsMS ys) := by
          simp [hsort]
      _ = normPairsMS ys := by
          simp [hdedup]
  calc
    normListMS (normListMS ys)
        = (normPairsMS (normListMS ys)).map Prod.snd := rfl
    _ = (normPairsMS ys).map Prod.snd := by
            simp [hpairNorm]
    _ = normListMS ys := rfl

/-- Keys from proof-only normalizer match uniqueSortedKeys. -/
theorem keys_normListMS_eq_uniqueSortedKeys (ys : List SurrealCore.PreGame) :
    (normListMS ys).map key = uniqueSortedKeys ys := by
  classical
  have hmap :
      (normPairsMS ys).map (fun p => key p.snd) =
        (normPairsMS ys).map Prod.fst := by
    apply (List.map_inj_left).2
    intro p hp
    simpa using key_snd_eq_fst_of_mem_normPairsMS (ys := ys) hp
  have hkeys :
      ((normPairsMS ys).map Prod.snd).map key =
        pairKeys (normPairsMS ys) := by
    simpa [List.map_map, pairKeys] using hmap
  have hconv : normPairsMS ys = Surreal.normPairsMS ys :=
    normPairsMS_eq_surreal (ys := ys)
  calc
    (normListMS ys).map key
        = ((normPairsMS ys).map Prod.snd).map key := by
            rfl
    _ = pairKeys (normPairsMS ys) := hkeys
    _ = pairKeys (Surreal.normPairsMS ys) := by
            simp [hconv]
    _ = uniqueSortedKeys ys := rfl

/-- Keys from normListCore match uniqueSortedKeys. -/
theorem keys_normListCore_eq_uniqueSortedKeys (ys : List SurrealCore.PreGame) :
    (normListCore ys).map key = uniqueSortedKeys ys := by
  have hkeys : (normListMS ys).map key = uniqueSortedKeys ys :=
    keys_normListMS_eq_uniqueSortedKeys (ys := ys)
  have hconvList :
      normListMS ys = Surreal.normListMS ys := by
    simpa [normListMS, Surreal.normListMS] using
      (congrArg (List.map Prod.snd) (normPairsMS_eq_surreal (ys := ys)))
  have hkeys_sur :
      (Surreal.normListMS ys).map key = uniqueSortedKeys ys := by
    calc
      (Surreal.normListMS ys).map key
          = (normListMS ys).map key := (congrArg (List.map key) hconvList.symm)
      _ = uniqueSortedKeys ys := hkeys
  simpa [normListCore] using hkeys_sur

/-- Keys (fingerprints) of the proof-only normalizer equal normalized keys. -/
lemma fkeys_normListMS (ys : List SurrealCore.PreGame) :
    fkeys (normListMS ys) = normKeys (fkeys ys) := by
  classical
  have hmap :
      ((normPairsMS ys).map Prod.snd).map key =
        keys (normPairsMS ys) := by
    have :
        (normPairsMS ys).map (fun p => key p.snd) =
          (normPairsMS ys).map Prod.fst := by
      apply (List.map_inj_left).2
      intro p hp
      simpa using key_snd_eq_fst_of_mem_normPairsMS (ys := ys) hp
    simpa [List.map_map, keys] using this
  calc
    fkeys (normListMS ys)
        = ((normPairsMS ys).map Prod.snd).map key := by
            simp [fkeys, normListMS, normPairsMS, mkPairs, List.map_map]
    _ = keys (normPairsMS ys) := hmap
    _ = normKeys (keys (mkPairs ys)) := keys_normPairsMS ys
    _ = normKeys (fkeys ys) := by
            simp [fkeys, keys_mkPairs]
end

end Proofs
end Surreal
end Numbers
end HeytingLean
