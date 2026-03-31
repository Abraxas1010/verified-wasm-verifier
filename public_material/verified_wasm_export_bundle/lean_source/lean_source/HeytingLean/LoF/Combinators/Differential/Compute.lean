import HeytingLean.LoF.Combinators.SKYMultiway
import HeytingLean.LoF.Combinators.Differential.LinearComb

/-!
# Differential combinators: small computable “formal sum” backend (Rat coefficients)

Mathlib's `Finsupp` API is extremely convenient for *library* work, but many constructors are
noncomputable because they avoid requiring decidable equality on coefficients.

For executables we provide a tiny, fully computable backend:

`FSum := List (Comb × Rat)`

with normalization-by-insertion to combine like terms and drop zero coefficients. This is meant
only for demos and runtime sanity checks.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Differential
namespace Compute

open HeytingLean.LoF

abbrev FSum := List (Comb × Rat)

def addTerm (t : Comb) (c : Rat) : FSum → FSum
  | [] =>
      if c = 0 then [] else [(t, c)]
  | (t', c') :: rest =>
      if t' = t then
        let c'' := c' + c
        if c'' = 0 then rest else (t, c'') :: rest
      else
        (t', c') :: addTerm t c rest

def normalize (v : FSum) : FSum :=
  v.foldl (fun acc tc => addTerm tc.1 tc.2 acc) []

def add (a b : FSum) : FSum :=
  b.foldl (fun acc tc => addTerm tc.1 tc.2 acc) a

def neg (v : FSum) : FSum :=
  v.map (fun tc => (tc.1, -tc.2))

def sub (a b : FSum) : FSum :=
  add a (neg b)

def smul (r : Rat) (v : FSum) : FSum :=
  normalize <| v.map (fun tc => (tc.1, r * tc.2))

def coeff (t : Comb) : FSum → Rat
  | [] => 0
  | (t', c) :: rest => (if t' = t then c else 0) + coeff t rest

def dot (a b : FSum) : Rat :=
  let an := normalize a
  let bn := normalize b
  an.foldl (fun acc tc => acc + tc.2 * coeff tc.1 bn) 0

def l2NormSq (v : FSum) : Rat :=
  (normalize v).foldl (fun acc tc => acc + tc.2 * tc.2) 0

private theorem foldSquares_nonneg (rows : FSum) (acc : Rat) (hacc : 0 ≤ acc) :
    0 ≤ rows.foldl (fun a tc => a + tc.2 * tc.2) acc := by
  induction rows generalizing acc with
  | nil =>
      simpa using hacc
  | cons tc rest ih =>
      rcases tc with ⟨_t, c⟩
      have hnext : 0 ≤ acc + c * c := by
        exact add_nonneg hacc (mul_self_nonneg c)
      simpa [List.foldl] using ih (acc := acc + c * c) hnext

theorem l2NormSq_nonneg (v : FSum) : 0 ≤ l2NormSq v := by
  unfold l2NormSq
  exact foldSquares_nonneg (normalize v) 0 (by simp)

def single (t : Comb) (c : Rat := 1) : FSum :=
  if c = 0 then [] else [(t, c)]

def app (f x : FSum) : FSum :=
  f.foldl
    (fun acc tc =>
      x.foldl
        (fun acc' uc => addTerm (Comb.app tc.1 uc.1) (tc.2 * uc.2) acc')
        acc)
    []

def stepSum (t : Comb) : FSum :=
  (Comb.stepEdgesList t).foldl (fun acc e => addTerm e.2 1 acc) []

def steps (v : FSum) : FSum :=
  v.foldl (fun acc tc => add acc (smul tc.2 (stepSum tc.1))) []

def stepsIter : Nat → FSum → FSum
  | 0, v => v
  | Nat.succ n, v => steps (stepsIter n v)

def reachabilityBounded (fuel : Nat) (v : FSum) : FSum :=
  (List.range (fuel + 1)).foldl (fun acc n => add acc (stepsIter n v)) []

/-- Count nodes in a combinator term. -/
def combSize : Comb → Nat
  | .K => 1
  | .S => 1
  | .Y => 1
  | .app f x => 1 + combSize f + combSize x

/-- Depth-bounded structural similarity in `[0, 1]`. Exact term match is `1`. -/
def combSimilarity : Comb → Comb → Nat → Rat
  | c1, c2, 0 =>
      if c1 == c2 then 1 else 0
  | c1, c2, Nat.succ d =>
      if c1 == c2 then 1
      else
        match c1, c2 with
        | .app f1 x1, .app f2 x2 =>
            (combSimilarity f1 f2 d + combSimilarity x1 x2 d) / 2
        | _, _ => 0

/-!
Issue C hardening:
`softDot` is implemented through an explicit feature-lift into `FSum`,
then standard dot-product in the lifted space. This is PSD by construction.
-/
/-- Depth-bounded feature expansion of a term. -/
def termFeatures : Nat → Comb → FSum
  | 0, t => single t 1
  | Nat.succ d, t =>
      match t with
      | .app f x =>
          normalize <| add (single t 1) (smul ((1 : Rat) / 2) (add (termFeatures d f) (termFeatures d x)))
      | _ => single t 1

/-- Lift an `FSum` into feature space induced by `termFeatures`. -/
def liftFeatures (depth : Nat) (v : FSum) : FSum :=
  normalize <| v.foldl (fun acc tc => add acc (smul tc.2 (termFeatures depth tc.1))) []

/-- Kernel-weighted dot product using the explicit PSD feature lift. -/
def softDot (depth : Nat) (a b : FSum) : Rat :=
  dot (liftFeatures depth a) (liftFeatures depth b)

/-- Apply one root-level SKY reduction (K/S/Y) when present. -/
def rootReduce : Comb → Option Comb
  | .app (.app .K x) _y => some x
  | .app (.app (.app .S x) y) z => some (.app (.app x z) (.app y z))
  | .app .Y f => some (.app f (.app .Y f))
  | _ => none

/-- Depth-bounded simplifier for combinator terms using root reductions. -/
def simplifyTerm : Nat → Comb → Comb
  | 0, t => t
  | Nat.succ d, t =>
      match rootReduce t with
      | some t' => simplifyTerm d t'
      | none =>
          match t with
          | .app f x => .app (simplifyTerm d f) (simplifyTerm d x)
          | other => other

/-- Simplify each term in an `FSum` then normalize merged terms. -/
def simplifyFSum (maxDepth : Nat) (v : FSum) : FSum :=
  normalize (v.map (fun tc => (simplifyTerm maxDepth tc.1, tc.2)))

/-- Truncate a Rat to prevent numeral explosion during iterated arithmetic.
    Rounds to nearest multiple of 1/denom, capping numerator magnitude. -/
def truncRat (r : Rat) (denom : Nat := 10000) : Rat :=
  let d := max 1 denom
  let scaled := r * (Int.ofNat d : Rat)
  let rounded := if scaled ≥ 0 then
    (scaled.num + scaled.den / 2) / scaled.den
  else
    (scaled.num - (Int.ofNat (scaled.den / 2))) / scaled.den
  (rounded : Rat) / (Int.ofNat d : Rat)

private def absCoeff (r : Rat) : Rat :=
  if r < 0 then -r else r

private def insertByAbs (x : Comb × Rat) : List (Comb × Rat) → List (Comb × Rat)
  | [] => [x]
  | y :: ys =>
      if absCoeff x.2 > absCoeff y.2 then
        x :: y :: ys
      else
        y :: insertByAbs x ys

private def sortByAbsDesc (rows : List (Comb × Rat)) : List (Comb × Rat) :=
  rows.foldl (fun acc row => insertByAbs row acc) []

/-- Keep top-k terms by absolute coefficient, dropping tiny terms. -/
def pruneFSum (topK : Nat) (threshold : Rat := (1 : Rat) / 1000) (v : FSum) : FSum :=
  let filtered := v.filter (fun tc => absCoeff tc.2 >= threshold)
  (sortByAbsDesc filtered).take topK

def showFSum (v : FSum) : String :=
  let parts :=
    v.map (fun tc =>
      let tStr := reprStr tc.1
      let cStr := toString tc.2
      s!"({cStr})·{tStr}")
  "[" ++ String.intercalate ", " parts ++ "]"

/-! ## Runtime/Library correspondence (Issue A) -/

noncomputable def toFormalSum : FSum → FormalSum Rat
  | [] => 0
  | (t, c) :: rest => Finsupp.single t c + toFormalSum rest

noncomputable def fromFormalSum (v : FormalSum Rat) : FSum :=
  normalize <| v.support.toList.map (fun t => (t, v t))

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

@[simp] theorem toFormalSum_nil :
    toFormalSum ([] : FSum) = (0 : FormalSum Rat) := by
  rfl

@[simp] theorem toFormalSum_cons (t : Comb) (c : Rat) (rest : FSum) :
    toFormalSum ((t, c) :: rest) = Finsupp.single t c + toFormalSum rest := by
  rfl

theorem toFormalSum_single (t : Comb) (c : Rat) :
    toFormalSum [(t, c)] = Finsupp.single t c := by
  simp [toFormalSum]

theorem toFormalSum_app_single_single (t u : Comb) (a b : Rat) :
    toFormalSum (app [(t, a)] [(u, b)]) = Finsupp.single (Comb.app t u) (a * b) := by
  by_cases h : a * b = 0
  · simp [app, addTerm, h]
  · simp [app, addTerm, h]

theorem toFormalSum_addTerm (t : Comb) (c : Rat) (v : FSum) :
    toFormalSum (addTerm t c v) = Finsupp.single t c + toFormalSum v := by
  ext q
  induction v with
  | nil =>
      by_cases hc : c = 0
      · simp [addTerm, toFormalSum, hc]
      · simp [addTerm, toFormalSum, hc]
  | cons tc rest ih =>
      rcases tc with ⟨u, b⟩
      by_cases hEq : u = t
      · subst hEq
        by_cases hZero : b + c = 0
        · by_cases hq : q = u
          · subst q
            have hZero' : c + b = 0 := by simpa [add_comm] using hZero
            have hcore : (toFormalSum rest) u = c + (b + (toFormalSum rest) u) := by
              calc
                (toFormalSum rest) u = 0 + (toFormalSum rest) u := by simp
                _ = (c + b) + (toFormalSum rest) u := by simp [hZero']
                _ = c + (b + (toFormalSum rest) u) := by ac_rfl
            simpa [addTerm, toFormalSum, hZero] using hcore
          · simp [addTerm, toFormalSum, hZero, hq, ih]
        · by_cases hq : q = u
          · subst q
            have hZero' : ¬(c + b = 0) := by simpa [add_comm] using hZero
            simp [addTerm, toFormalSum, hZero, hZero', add_assoc, add_left_comm, add_comm]
          · simp [addTerm, toFormalSum, hZero, hq, ih]
      · by_cases hq : q = u
        · subst hq
          simp [addTerm, toFormalSum, hEq, ih]
        · by_cases hqt : q = t
          · subst hqt
            simp [addTerm, toFormalSum, hEq, hq, ih, add_assoc, add_left_comm, add_comm]
          · simp [addTerm, toFormalSum, hEq, hq, hqt, ih, add_assoc, add_left_comm, add_comm]

theorem toFormalSum_foldl_addTerm (rows : List (Comb × Rat)) (acc : FSum) :
    toFormalSum (rows.foldl (fun a tc => addTerm tc.1 tc.2 a) acc)
      = toFormalSum acc + toFormalSum rows := by
  induction rows generalizing acc with
  | nil =>
      simp
  | cons tc rest ih =>
      rcases tc with ⟨t, c⟩
      simp [List.foldl, ih, toFormalSum_addTerm, add_assoc, add_left_comm, add_comm]

theorem toFormalSum_normalize (v : FSum) :
    toFormalSum (normalize v) = toFormalSum v := by
  simpa [normalize] using (toFormalSum_foldl_addTerm v ([] : FSum))

theorem normalize_idempotent (v : FSum) :
    toFormalSum (normalize (normalize v)) = toFormalSum (normalize v) := by
  simpa [toFormalSum_normalize] using (toFormalSum_normalize (normalize v))

theorem coeff_eq_toFormalSum_apply (t : Comb) (v : FSum) :
    coeff t v = toFormalSum v t := by
  induction v with
  | nil =>
      simp [coeff, toFormalSum]
  | cons tc rest ih =>
      rcases tc with ⟨u, c⟩
      by_cases h : u = t
      · subst h
        simp [coeff, toFormalSum, ih, add_assoc, add_left_comm, add_comm]
      · simp [coeff, toFormalSum, h, ih]

theorem toFormalSum_add (a b : FSum) :
    toFormalSum (add a b) = toFormalSum a + toFormalSum b := by
  simpa [add, add_assoc, add_left_comm, add_comm] using
    (toFormalSum_foldl_addTerm b a)

theorem toFormalSum_map_smul (r : Rat) (v : FSum) :
    toFormalSum (v.map (fun tc => (tc.1, r * tc.2))) = r • toFormalSum v := by
  induction v with
  | nil =>
      simp [toFormalSum]
  | cons tc rest ih =>
      rcases tc with ⟨t, c⟩
      simp [toFormalSum, ih, smul_add, mul_assoc, mul_left_comm, mul_comm]

theorem toFormalSum_smul (r : Rat) (v : FSum) :
    toFormalSum (smul r v) = r • toFormalSum v := by
  simp [smul, toFormalSum_normalize, toFormalSum_map_smul]

private theorem toFormalSum_app_single_fold
    (t : Comb) (a : Rat) (x acc : FSum) (vacc : FormalSum Rat)
    (hacc : toFormalSum acc = vacc) :
    toFormalSum
        (x.foldl (fun a' uc => addTerm (Comb.app t uc.1) (a * uc.2) a') acc) =
      vacc + Differential.FormalSum.app (K := Rat) (Finsupp.single t a) (toFormalSum x) := by
  induction x generalizing acc vacc with
  | nil =>
      simp [hacc, Differential.FormalSum.app]
  | cons uc rest ih =>
      rcases uc with ⟨u, b⟩
      have hacc' :
          toFormalSum (addTerm (Comb.app t u) (a * b) acc) =
            vacc + Finsupp.single (Comb.app t u) (a * b) := by
        calc
          toFormalSum (addTerm (Comb.app t u) (a * b) acc)
              = Finsupp.single (Comb.app t u) (a * b) + toFormalSum acc := by
                  simpa using toFormalSum_addTerm (Comb.app t u) (a * b) acc
          _ = Finsupp.single (Comb.app t u) (a * b) + vacc := by simpa [hacc]
          _ = vacc + Finsupp.single (Comb.app t u) (a * b) := by ac_rfl
      have ih' := ih (acc := addTerm (Comb.app t u) (a * b) acc)
          (vacc := vacc + Finsupp.single (Comb.app t u) (a * b)) hacc'
      calc
        toFormalSum
            (rest.foldl (fun a' uc => addTerm (Comb.app t uc.1) (a * uc.2) a')
              (addTerm (Comb.app t u) (a * b) acc))
            = (vacc + Finsupp.single (Comb.app t u) (a * b)) +
                Differential.FormalSum.app (K := Rat) (Finsupp.single t a) (toFormalSum rest) := by
                  simpa using ih'
        _ = vacc +
              (Finsupp.single (Comb.app t u) (a * b) +
                Differential.FormalSum.app (K := Rat) (Finsupp.single t a) (toFormalSum rest)) := by
                ac_rfl
        _ = vacc +
              Differential.FormalSum.app (K := Rat) (Finsupp.single t a)
                (Finsupp.single u b + toFormalSum rest) := by
                have hsum :
                    (Finsupp.single u b + toFormalSum rest).sum
                        (fun u b => Finsupp.single (Comb.app t u) (a * b))
                      = Finsupp.single (Comb.app t u) (a * b) +
                        (toFormalSum rest).sum (fun u b => Finsupp.single (Comb.app t u) (a * b)) := by
                      have hsum' :
                          (Finsupp.single u b + toFormalSum rest).sum
                              (fun u b => Finsupp.single (Comb.app t u) (a * b))
                            = (Finsupp.single u b).sum
                                (fun u b => Finsupp.single (Comb.app t u) (a * b)) +
                              (toFormalSum rest).sum
                                (fun u b => Finsupp.single (Comb.app t u) (a * b)) := by
                                  apply Finsupp.sum_add_index
                                  · intro i hi
                                    simp
                                  · intro i hi b₁ b₂
                                    simp [mul_add, Finsupp.single_add]
                      simpa [add_assoc, add_left_comm, add_comm] using hsum'
                simp [Differential.FormalSum.app, hsum, add_assoc, add_left_comm, add_comm]
        _ = vacc + Differential.FormalSum.app (K := Rat) (Finsupp.single t a) (toFormalSum ((u, b) :: rest)) := by
                simp [toFormalSum]

private theorem toFormalSum_app_fold
    (x f acc : FSum) (vacc : FormalSum Rat) (hacc : toFormalSum acc = vacc) :
    toFormalSum
        (f.foldl
          (fun a tc =>
            x.foldl (fun a' uc => addTerm (Comb.app tc.1 uc.1) (tc.2 * uc.2) a') a)
          acc) =
      vacc + Differential.FormalSum.app (K := Rat) (toFormalSum f) (toFormalSum x) := by
  induction f generalizing acc vacc with
  | nil =>
      simp [hacc, Differential.FormalSum.app]
  | cons tc rest ih =>
      rcases tc with ⟨t, a⟩
      have hacc' :
          toFormalSum
              (x.foldl (fun a' uc => addTerm (Comb.app t uc.1) (a * uc.2) a') acc) =
            vacc + Differential.FormalSum.app (K := Rat) (Finsupp.single t a) (toFormalSum x) := by
        simpa using toFormalSum_app_single_fold t a x acc vacc hacc
      have ih' := ih
        (acc := x.foldl (fun a' uc => addTerm (Comb.app t uc.1) (a * uc.2) a') acc)
        (vacc := vacc + Differential.FormalSum.app (K := Rat) (Finsupp.single t a) (toFormalSum x))
        hacc'
      calc
        toFormalSum
            (rest.foldl
              (fun a tc =>
                x.foldl (fun a' uc => addTerm (Comb.app tc.1 uc.1) (tc.2 * uc.2) a') a)
              (x.foldl (fun a' uc => addTerm (Comb.app t uc.1) (a * uc.2) a') acc))
            = (vacc + Differential.FormalSum.app (K := Rat) (Finsupp.single t a) (toFormalSum x)) +
                Differential.FormalSum.app (K := Rat) (toFormalSum rest) (toFormalSum x) := by
                  simpa using ih'
        _ = vacc +
              (Differential.FormalSum.app (K := Rat) (Finsupp.single t a) (toFormalSum x) +
                Differential.FormalSum.app (K := Rat) (toFormalSum rest) (toFormalSum x)) := by
                ac_rfl
        _ = vacc +
              Differential.FormalSum.app (K := Rat)
                (Finsupp.single t a + toFormalSum rest) (toFormalSum x) := by
                simp [Differential.FormalSum.app_add_left, add_assoc, add_left_comm, add_comm]
        _ = vacc + Differential.FormalSum.app (K := Rat) (toFormalSum ((t, a) :: rest)) (toFormalSum x) := by
                simp [toFormalSum]

theorem app_correspondence (f x : FSum) :
    toFormalSum (app f x) =
      Differential.FormalSum.app (K := Rat) (toFormalSum f) (toFormalSum x) := by
  simpa [app, toFormalSum_nil] using
    (toFormalSum_app_fold x f ([] : FSum) (0 : FormalSum Rat) rfl)

private theorem dot_fold_eq_sum_acc (rows bn : FSum) (acc : Rat) :
    rows.foldl (fun a tc => a + tc.2 * coeff tc.1 bn) acc =
      acc + (toFormalSum rows).sum (fun t a => a * coeff t bn) := by
  induction rows generalizing acc with
  | nil =>
      simp [toFormalSum]
  | cons tc rest ih =>
      rcases tc with ⟨t, a⟩
      have hsum :
          (Finsupp.single t a + toFormalSum rest).sum (fun t a => a * coeff t bn)
            = a * coeff t bn + (toFormalSum rest).sum (fun t a => a * coeff t bn) := by
              have hsum' :
                  (Finsupp.single t a + toFormalSum rest).sum (fun t a => a * coeff t bn)
                    = (Finsupp.single t a).sum (fun t a => a * coeff t bn) +
                      (toFormalSum rest).sum (fun t a => a * coeff t bn) := by
                        apply Finsupp.sum_add_index
                        · intro i hi
                          simp
                        · intro i hi b₁ b₂
                          simp [add_mul]
              simpa [add_assoc, add_left_comm, add_comm] using hsum'
      calc
        rest.foldl (fun a tc => a + tc.2 * coeff tc.1 bn) (acc + a * coeff t bn)
            = (acc + a * coeff t bn) +
                (toFormalSum rest).sum (fun t a => a * coeff t bn) := by
                  simpa using (ih (acc := acc + a * coeff t bn))
        _ = acc + (a * coeff t bn + (toFormalSum rest).sum (fun t a => a * coeff t bn)) := by
              ac_rfl
        _ = acc + (Finsupp.single t a + toFormalSum rest).sum (fun t a => a * coeff t bn) := by
              simpa [hsum]

private theorem dot_fold_eq_sum (rows bn : FSum) :
    rows.foldl (fun acc tc => acc + tc.2 * coeff tc.1 bn) 0 =
      (toFormalSum rows).sum (fun t a => a * coeff t bn) := by
  simpa [dot_fold_eq_sum_acc] using (dot_fold_eq_sum_acc rows bn 0)

theorem dot_correspondence (a b : FSum) :
    dot a b = Differential.FormalSum.dot (toFormalSum a) (toFormalSum b) := by
  unfold dot Differential.FormalSum.dot
  set an := normalize a
  set bn := normalize b
  calc
    an.foldl (fun acc tc => acc + tc.2 * coeff tc.1 bn) 0
        = (toFormalSum an).sum (fun t a => a * coeff t bn) := by
            simpa using dot_fold_eq_sum an bn
    _ = (toFormalSum an).sum (fun t a => a * (toFormalSum bn t)) := by
            simp [coeff_eq_toFormalSum_apply]
    _ = Differential.FormalSum.dot (toFormalSum an) (toFormalSum bn) := by
            simp [Differential.FormalSum.dot]
    _ = Differential.FormalSum.dot (toFormalSum a) (toFormalSum b) := by
            simp [an, bn, toFormalSum_normalize]

private theorem toFormalSum_stepSum_fold
    (edges : List (EventData × Comb)) (acc : FSum) (vacc : FormalSum Rat)
    (hacc : toFormalSum acc = vacc) :
    toFormalSum (edges.foldl (fun a e => addTerm e.2 1 a) acc) =
      edges.foldl (fun va e => va + Finsupp.single e.2 (1 : Rat)) vacc := by
  induction edges generalizing acc vacc with
  | nil =>
      simpa [hacc]
  | cons e rest ih =>
      have hacc' :
          toFormalSum (addTerm e.2 (1 : Rat) acc) =
            vacc + Finsupp.single e.2 (1 : Rat) := by
        calc
          toFormalSum (addTerm e.2 (1 : Rat) acc)
              = Finsupp.single e.2 (1 : Rat) + toFormalSum acc := by
                  simpa using toFormalSum_addTerm e.2 (1 : Rat) acc
          _ = Finsupp.single e.2 (1 : Rat) + vacc := by simpa [hacc]
          _ = vacc + Finsupp.single e.2 (1 : Rat) := by ac_rfl
      simpa [List.foldl] using
        (ih (acc := addTerm e.2 (1 : Rat) acc)
          (vacc := vacc + Finsupp.single e.2 (1 : Rat)) hacc')

theorem toFormalSum_stepSum (t : Comb) :
    toFormalSum (stepSum t) = Differential.FormalSum.stepSum (K := Rat) t := by
  unfold stepSum Differential.FormalSum.stepSum
  simpa using
    (toFormalSum_stepSum_fold (edges := Comb.stepEdgesList t) ([] : FSum) (0 : FormalSum Rat) rfl)

private theorem toFormalSum_steps_fold
    (rows : FSum) (acc : FSum) (vacc : FormalSum Rat)
    (hacc : toFormalSum acc = vacc) :
    toFormalSum
        (rows.foldl (fun a tc => add a (smul tc.2 (stepSum tc.1))) acc) =
      rows.foldl (fun va tc => va + tc.2 • Differential.FormalSum.stepSum (K := Rat) tc.1) vacc := by
  induction rows generalizing acc vacc with
  | nil =>
      simpa [hacc]
  | cons tc rest ih =>
      rcases tc with ⟨t, c⟩
      have hacc' :
          toFormalSum (add acc (smul c (stepSum t))) =
            vacc + c • Differential.FormalSum.stepSum (K := Rat) t := by
        calc
          toFormalSum (add acc (smul c (stepSum t)))
              = toFormalSum acc + toFormalSum (smul c (stepSum t)) := by
                  simpa using toFormalSum_add acc (smul c (stepSum t))
          _ = vacc + c • toFormalSum (stepSum t) := by
                  simp [hacc, toFormalSum_smul]
          _ = vacc + c • Differential.FormalSum.stepSum (K := Rat) t := by
                  simp [toFormalSum_stepSum]
      simpa [List.foldl] using
        (ih (acc := add acc (smul c (stepSum t)))
          (vacc := vacc + c • Differential.FormalSum.stepSum (K := Rat) t) hacc')

private theorem toFormalSum_sum_step_acc (rows : FSum) (acc : FormalSum Rat) :
    rows.foldl (fun va tc => va + tc.2 • Differential.FormalSum.stepSum (K := Rat) tc.1) acc =
      acc + (toFormalSum rows).sum (fun t a => a • Differential.FormalSum.stepSum (K := Rat) t) := by
  induction rows generalizing acc with
  | nil =>
      simp [toFormalSum]
  | cons tc rest ih =>
      rcases tc with ⟨t, c⟩
      have hsum :
          (Finsupp.single t c + toFormalSum rest).sum
              (fun t a => a • Differential.FormalSum.stepSum (K := Rat) t)
            = c • Differential.FormalSum.stepSum (K := Rat) t +
                (toFormalSum rest).sum
                  (fun t a => a • Differential.FormalSum.stepSum (K := Rat) t) := by
              have hsum' :
                  (Finsupp.single t c + toFormalSum rest).sum
                      (fun t a => a • Differential.FormalSum.stepSum (K := Rat) t)
                    = (Finsupp.single t c).sum
                        (fun t a => a • Differential.FormalSum.stepSum (K := Rat) t) +
                      (toFormalSum rest).sum
                        (fun t a => a • Differential.FormalSum.stepSum (K := Rat) t) := by
                          apply Finsupp.sum_add_index
                          · intro i hi
                            simp
                          · intro i hi b₁ b₂
                            simp [add_smul]
              simpa [add_assoc, add_left_comm, add_comm] using hsum'
      calc
        rest.foldl (fun va tc => va + tc.2 • Differential.FormalSum.stepSum (K := Rat) tc.1)
            (acc + c • Differential.FormalSum.stepSum (K := Rat) t)
            = (acc + c • Differential.FormalSum.stepSum (K := Rat) t) +
                (toFormalSum rest).sum
                  (fun t a => a • Differential.FormalSum.stepSum (K := Rat) t) := by
                    simpa using (ih (acc := acc + c • Differential.FormalSum.stepSum (K := Rat) t))
        _ = acc + (c • Differential.FormalSum.stepSum (K := Rat) t +
            (toFormalSum rest).sum (fun t a => a • Differential.FormalSum.stepSum (K := Rat) t)) := by
              ac_rfl
        _ = acc + (Finsupp.single t c + toFormalSum rest).sum
            (fun t a => a • Differential.FormalSum.stepSum (K := Rat) t) := by
              simpa [hsum]

private theorem toFormalSum_sum_step (rows : FSum) :
    rows.foldl (fun va tc => va + tc.2 • Differential.FormalSum.stepSum (K := Rat) tc.1) 0 =
      (toFormalSum rows).sum (fun t a => a • Differential.FormalSum.stepSum (K := Rat) t) := by
  simpa [toFormalSum_sum_step_acc] using (toFormalSum_sum_step_acc rows (0 : FormalSum Rat))

theorem steps_correspondence (v : FSum) :
    toFormalSum (steps v) = Differential.FormalSum.steps (K := Rat) (toFormalSum v) := by
  unfold steps Differential.FormalSum.steps
  calc
    toFormalSum (v.foldl (fun a tc => add a (smul tc.2 (stepSum tc.1))) [])
        = v.foldl (fun va tc => va + tc.2 • Differential.FormalSum.stepSum (K := Rat) tc.1) 0 := by
            simpa [toFormalSum_nil] using
              (toFormalSum_steps_fold v ([] : FSum) (0 : FormalSum Rat) rfl)
    _ = (toFormalSum v).sum (fun t a => a • Differential.FormalSum.stepSum (K := Rat) t) := by
            simpa using toFormalSum_sum_step v

theorem stepsIter_correspondence (fuel : Nat) (v : FSum) :
    toFormalSum (stepsIter fuel v) =
      Differential.FormalSum.stepsIter (K := Rat) fuel (toFormalSum v) := by
  induction fuel generalizing v with
  | zero =>
      simp [stepsIter, Differential.FormalSum.stepsIter]
  | succ n ih =>
      simp [stepsIter, Differential.FormalSum.stepsIter, steps_correspondence, ih]

end Compute
end Differential
end Combinators
end LoF
end HeytingLean
