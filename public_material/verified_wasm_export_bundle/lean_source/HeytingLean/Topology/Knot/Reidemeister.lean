import Std
import HeytingLean.Topology.Knot.PDGraph

/-!
# Knot theory: Reidemeister moves (Phase 1)

This module defines executable **local move constructors** on the label-free `PDGraph`
representation. The move operations are designed so that the new crossings are appended at
the end; this matches the recursive Kauffman bracket implementation (which smooths the last
crossing first) and enables direct algebraic proofs of invariance.

Moves implemented here:
- Reidemeister I: add/remove a curl on a chosen arc.
- Reidemeister II: add/remove a cancelling pair on two chosen arcs.

Reidemeister III is provided here as a **braid-style constructor** producing the two sides
of the move (`σ₁σ₂σ₁` vs `σ₂σ₁σ₂`) on three chosen disjoint arcs.
-/

namespace HeytingLean
namespace Topology
namespace Knot

open Std

namespace Reidemeister

inductive CurlKind where
  | pos
  | neg
deriving Repr, DecidableEq, Inhabited

/-- Internal helper: set `nbr[i]=j` and `nbr[j]=i` with bounds checking. -/
def setPair (nbr : Array Nat) (i j : Nat) : Except String (Array Nat) := do
  if i >= nbr.size || j >= nbr.size then
    throw "setPair: index out of bounds"
  let nbr := nbr.set! i j
  let nbr := nbr.set! j i
  return nbr

theorem setPair_eq_ok
    {nbr : Array Nat} {i j : Nat} (hi : i < nbr.size) (hj : j < nbr.size) :
    setPair nbr i j = .ok ((nbr.set! i j).set! j i) := by
  have hi' : ¬ i >= nbr.size := Nat.not_le_of_gt hi
  have hj' : ¬ j >= nbr.size := Nat.not_le_of_gt hj
  simp [setPair, hi', hj', Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Unchecked `setPair` used internally after bounds are established by validation/checks. -/
def setPair! (nbr : Array Nat) (i j : Nat) : Array Nat :=
  (nbr.set! i j).set! j i

/-- Add a Reidemeister-I curl along the arc incident to half-edge `x`. -/
def r1Add (g : PDGraph) (x : Nat) (kind : CurlKind) : Except String PDGraph :=
  match PDGraph.validate g with
  | .error e => .error e
  | .ok () =>
      let m := g.numHalfEdges
      if x >= m then
        .error s!"r1Add: x={x} out of range (m={m})"
      else
        let y := g.arcNbr[x]!
        if y >= m then
          .error "r1Add: corrupt arcNbr"
        else if g.arcNbr[y]! != x then
          -- Local involution check (useful as a proof handle; redundant if `validate` succeeded).
          .error "r1Add: arcNbr not an involution at x"
        else
          let base := m
          let nbr0 := g.arcNbr ++ Array.replicate 4 0
          let nbr :=
            match kind with
            | .pos =>
                -- internal loop: (0↔1); external arc is restored by A-smoothing (2↔3)
                let nbr := setPair! nbr0 (base + 0) (base + 1)
                let nbr := setPair! nbr x (base + 2)
                setPair! nbr y (base + 3)
            | .neg =>
                -- internal loop: (1↔2); external arc is restored by B-smoothing (3↔0)
                let nbr := setPair! nbr0 (base + 1) (base + 2)
                let nbr := setPair! nbr x (base + 0)
                setPair! nbr y (base + 3)
          let g' : PDGraph := { freeLoops := g.freeLoops, n := g.n + 1, arcNbr := nbr }
          -- Validate the output; this makes downstream rewriting (and proofs) robust.
          match PDGraph.validate g' with
          | .error e => .error e
          | .ok () => .ok g'

/-- Remove a Reidemeister-I curl, assuming the **last** crossing has the expected curl shape. -/
def r1RemoveLast (g : PDGraph) (kind : CurlKind) : Except String PDGraph :=
  match PDGraph.validate g with
  | .error e => .error e
  | .ok () =>
      if g.n = 0 then
        .error "r1RemoveLast: n=0"
      else
        let m := g.numHalfEdges
        let base := m - 4
        let (intA, intB, ext1, ext2) :=
          match kind with
          | .pos => (base + 0, base + 1, base + 2, base + 3)
          | .neg => (base + 1, base + 2, base + 0, base + 3)
        if g.arcNbr[intA]! != intB || g.arcNbr[intB]! != intA then
          .error "r1RemoveLast: internal loop arc mismatch"
        else
          let x := g.arcNbr[ext1]!
          let y := g.arcNbr[ext2]!
          let extOk : Bool := decide (x < base) && decide (y < base)
          if !extOk then
            .error "r1RemoveLast: expected external endpoints for the curl"
          else if g.arcNbr[x]! != ext1 || g.arcNbr[y]! != ext2 then
            .error "r1RemoveLast: external endpoints do not point back to the curl"
          else
            let nbr := setPair! (g.arcNbr.extract 0 base) x y
            let g' : PDGraph := { freeLoops := g.freeLoops, n := g.n - 1, arcNbr := nbr }
            match PDGraph.validate g' with
            | .error e => .error e
            | .ok () => .ok g'

/-- Add a Reidemeister-II cancelling pair between the arcs incident to half-edges `x` and `u`. -/
def r2Add (g : PDGraph) (x u : Nat) : Except String PDGraph :=
  match PDGraph.validate g with
  | .error e => .error e
  | .ok () =>
      let m := g.numHalfEdges
      if x >= m || u >= m then
        .error s!"r2Add: out of range (m={m})"
      else
        let y := g.arcNbr[x]!
        let v := g.arcNbr[u]!
        if y >= m || v >= m then
          .error "r2Add: corrupt arcNbr"
        else if g.arcNbr[y]! != x || g.arcNbr[v]! != u then
          -- Local involution checks (useful as proof handles).
          .error "r2Add: arcNbr not an involution at chosen endpoints"
        else if x == u || x == v || y == u || y == v then
          -- Ensure the two arcs are disjoint.
          .error "r2Add: arcs must be disjoint"
        else
          -- Canonicalize each chosen arc (endpoints are unordered in `PDGraph`) so that
          -- the move is independent of which endpoint the caller supplies.
          let (x0, y0) := if x < y then (x, y) else (y, x)
          let (u0, v0) := if u < v then (u, v) else (v, u)
          -- Canonicalize the order of the two arcs as well (commutativity at the API boundary).
          let (x0, y0, u0, v0) := if u0 < x0 then (u0, v0, x0, y0) else (x0, y0, u0, v0)

          let base1 := m
          let base2 := m + 4
          let nbr0 := g.arcNbr ++ Array.replicate 8 0
          -- External connections (split the two chosen arcs):
          -- Strand 1: x (left) ↔ y (right)
          -- Strand 2: u (left) ↔ v (right)
          let nbr := setPair! nbr0 x0 (base1 + 0)
          let nbr := setPair! nbr y0 (base2 + 1)
          let nbr := setPair! nbr u0 (base1 + 3)
          let nbr := setPair! nbr v0 (base2 + 2)
          -- Internal arcs between the two crossings (the bigon edges):
          let nbr := setPair! nbr (base1 + 1) (base2 + 0)
          let nbr := setPair! nbr (base1 + 2) (base2 + 3)
          let g' : PDGraph := { freeLoops := g.freeLoops, n := g.n + 2, arcNbr := nbr }
          match PDGraph.validate g' with
          | .error e => .error e
          | .ok () => .ok g'

/-- Remove a Reidemeister-II cancelling pair, assuming the **last two** crossings match `r2Add`. -/
def r2RemoveLast (g : PDGraph) : Except String PDGraph :=
  match PDGraph.validate g with
  | .error e => .error e
  | .ok () =>
      if g.n < 2 then
        .error "r2RemoveLast: need at least 2 crossings"
      else
        let m := g.numHalfEdges
        let base1 := m - 8
        let base2 := m - 4
        -- Check the two internal arcs (the bigon edges).
        if g.arcNbr[base1 + 1]! != base2 + 0 || g.arcNbr[base2 + 0]! != base1 + 1 then
          .error "r2RemoveLast: internal arc (1↔0) mismatch"
        else if g.arcNbr[base1 + 2]! != base2 + 3 || g.arcNbr[base2 + 3]! != base1 + 2 then
          .error "r2RemoveLast: internal arc (2↔3) mismatch"
        else
          let x := g.arcNbr[base1 + 0]!
          let u := g.arcNbr[base1 + 3]!
          let y := g.arcNbr[base2 + 1]!
          let v := g.arcNbr[base2 + 2]!
          let extOk : Bool :=
            decide (x < base1) && decide (u < base1) && decide (y < base1) && decide (v < base1)
          if !extOk then
            .error "r2RemoveLast: expected external endpoints for the pair"
          else if g.arcNbr[x]! != base1 + 0 || g.arcNbr[u]! != base1 + 3 then
            .error "r2RemoveLast: external endpoints do not point back (left crossing)"
          else if g.arcNbr[y]! != base2 + 1 || g.arcNbr[v]! != base2 + 2 then
            .error "r2RemoveLast: external endpoints do not point back (right crossing)"
          else
            let nbr := setPair! (setPair! (g.arcNbr.extract 0 base1) x y) u v
            let g' : PDGraph := { freeLoops := g.freeLoops, n := g.n - 2, arcNbr := nbr }
            match PDGraph.validate g' with
            | .error e => .error e
            | .ok () => .ok g'

/-- Construct the left side of Reidemeister III as a 3-strand braid word `σ₁σ₂σ₁`
on three disjoint arcs (identified by half-edges `x`, `u`, `w`). -/
def r3BraidLeft (g : PDGraph) (x u w : Nat) : Except String PDGraph := do
  PDGraph.validate g
  let m := g.numHalfEdges
  if x >= m || u >= m || w >= m then
    throw s!"r3BraidLeft: out of range (m={m})"
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  -- Ensure the three arcs are pairwise disjoint.
  let pts : List Nat := [x, x2, u, u2, w, w2]
  if pts.eraseDups.length != pts.length then
    throw "r3BraidLeft: arcs must be pairwise disjoint"

  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let mut nbr := g.arcNbr ++ Array.replicate 12 0

  -- σ₁σ₂σ₁ wiring (see `kaufman.md` Phase 1 notes):
  -- boundary
  nbr := setPair! nbr x (baseA + 0)
  nbr := setPair! nbr u (baseA + 1)
  nbr := setPair! nbr w (baseB + 1)
  nbr := setPair! nbr x2 (baseB + 3)
  nbr := setPair! nbr w2 (baseC + 2)
  nbr := setPair! nbr u2 (baseC + 3)
  -- internal strands
  nbr := setPair! nbr (baseA + 2) (baseC + 0)
  nbr := setPair! nbr (baseA + 3) (baseB + 0)
  nbr := setPair! nbr (baseB + 2) (baseC + 1)

  let g' : PDGraph := { freeLoops := g.freeLoops, n := g.n + 3, arcNbr := nbr }
  PDGraph.validate g'
  return g'

/-- Construct the right side of Reidemeister III as a 3-strand braid word `σ₂σ₁σ₂`
on three chosen disjoint arcs. -/
def r3BraidRight (g : PDGraph) (x u w : Nat) : Except String PDGraph := do
  PDGraph.validate g
  let m := g.numHalfEdges
  if x >= m || u >= m || w >= m then
    throw s!"r3BraidRight: out of range (m={m})"
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  let pts : List Nat := [x, x2, u, u2, w, w2]
  if pts.eraseDups.length != pts.length then
    throw "r3BraidRight: arcs must be pairwise disjoint"

  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let mut nbr := g.arcNbr ++ Array.replicate 12 0

  -- σ₂σ₁σ₂ wiring
  -- boundary
  nbr := setPair! nbr u (baseA + 0)
  nbr := setPair! nbr w (baseA + 1)
  nbr := setPair! nbr x (baseB + 0)
  nbr := setPair! nbr w2 (baseB + 2)
  nbr := setPair! nbr u2 (baseC + 2)
  nbr := setPair! nbr x2 (baseC + 3)
  -- internal strands
  nbr := setPair! nbr (baseA + 2) (baseB + 1)
  nbr := setPair! nbr (baseB + 3) (baseC + 0)
  nbr := setPair! nbr (baseA + 3) (baseC + 1)

  let g' : PDGraph := { freeLoops := g.freeLoops, n := g.n + 3, arcNbr := nbr }
  PDGraph.validate g'
  return g'

/-!
## Lemma-level inverse laws (Phase 6.1)

These lemmas connect the executable move constructors to their corresponding “remove last”
operations, enabling theorem-level reasoning beyond runtime regression checks.
-/

section InverseLaws

-- Prevent `simp` from unfolding the executable validator; our proofs reason via
-- `validate = .ok ()` handles and Prop-level `PDGraph.Valid`.
attribute [local irreducible] PDGraph.validate
attribute [local irreducible] setPair!

private theorem getBang_eq_getElem (a : Array Nat) (i : Nat) (hi : i < a.size) :
    a[i]! = a[i]'hi := by
  simp [hi]

private theorem setPair!_eq_set
    (nbr : Array Nat) (i j : Nat) (hi : i < nbr.size) (hj : j < nbr.size) :
    setPair! nbr i j = (nbr.set i j hi).set j i (by simpa [Array.size_set] using hj) := by
  unfold setPair!
  simp [Array.set!, Array.setIfInBounds, hi, hj]

private theorem setPair!_getBang_left
    (nbr : Array Nat) (i j : Nat) (hi : i < nbr.size) (hj : j < nbr.size) (hij : i ≠ j) :
    (setPair! nbr i j)[i]! = j := by
  have hj1 : j < (nbr.set i j hi).size := by
    simpa [Array.size_set] using hj
  have hi1 : i < (nbr.set i j hi).size := by
    simpa [Array.size_set] using hi
  have hi2 : i < ((nbr.set i j hi).set j i hj1).size := by
    simpa [Array.size_set] using hi
  have hEq : setPair! nbr i j = (nbr.set i j hi).set j i hj1 :=
    setPair!_eq_set nbr i j hi hj
  calc
    (setPair! nbr i j)[i]! = ((nbr.set i j hi).set j i hj1)[i]! := by simp [hEq]
    _ = ((nbr.set i j hi).set j i hj1)[i]'hi2 := by
      simpa using (getBang_eq_getElem ((nbr.set i j hi).set j i hj1) i hi2)
    _ = (nbr.set i j hi)[i]'hi1 := by
      simpa [hij.symm] using
        (Array.getElem_set_ne (xs := nbr.set i j hi) (i := j) (h' := hj1) (v := i) (j := i) (pj := hi1)
          (h := hij.symm))
    _ = j := by
      simp [Array.getElem_set_self]

private theorem setPair!_getBang_right
    (nbr : Array Nat) (i j : Nat) (hi : i < nbr.size) (hj : j < nbr.size) :
    (setPair! nbr i j)[j]! = i := by
  have hj1 : j < (nbr.set i j hi).size := by
    simpa [Array.size_set] using hj
  have hj2 : j < ((nbr.set i j hi).set j i hj1).size := by
    simpa [Array.size_set] using hj
  have hEq : setPair! nbr i j = (nbr.set i j hi).set j i hj1 :=
    setPair!_eq_set nbr i j hi hj
  calc
    (setPair! nbr i j)[j]! = ((nbr.set i j hi).set j i hj1)[j]! := by simp [hEq]
    _ = ((nbr.set i j hi).set j i hj1)[j]'hj2 := by
      simpa using (getBang_eq_getElem ((nbr.set i j hi).set j i hj1) j hj2)
    _ = i := by
      simp [Array.getElem_set_self]

private theorem setPair!_getBang_ne
    (nbr : Array Nat) (i j k : Nat)
    (hi : i < nbr.size) (hj : j < nbr.size) (hk : k < nbr.size)
    (hki : k ≠ i) (hkj : k ≠ j) :
    (setPair! nbr i j)[k]! = nbr[k]! := by
  have hj1 : j < (nbr.set i j hi).size := by
    simpa [Array.size_set] using hj
  have hk1 : k < (nbr.set i j hi).size := by
    simpa [Array.size_set] using hk
  have hk2 : k < ((nbr.set i j hi).set j i hj1).size := by
    simpa [Array.size_set] using hk
  have hEq : setPair! nbr i j = (nbr.set i j hi).set j i hj1 :=
    setPair!_eq_set nbr i j hi hj
  calc
    (setPair! nbr i j)[k]! = ((nbr.set i j hi).set j i hj1)[k]! := by simp [hEq]
    _ = ((nbr.set i j hi).set j i hj1)[k]'hk2 := by
      simpa using (getBang_eq_getElem ((nbr.set i j hi).set j i hj1) k hk2)
    _ = (nbr.set i j hi)[k]'hk1 := by
      simpa [hkj.symm] using
        (Array.getElem_set_ne (xs := nbr.set i j hi) (i := j) (h' := hj1) (v := i) (j := k) (pj := hk1)
          (h := hkj.symm))
    _ = nbr[k]! := by
      -- Reduce the inner `set` at a different index.
      have hk' : k < nbr.size := hk
      have hkElem : (nbr.set i j hi)[k]'hk1 = nbr[k]'hk' := by
        simpa [hki.symm] using
          (Array.getElem_set_ne (xs := nbr) (i := i) (h' := hi) (v := j) (j := k) (pj := hk') (h := hki.symm))
      -- Convert the RHS to `!` indexing.
      have hkBang : nbr[k]! = nbr[k]'hk' := by
        exact getBang_eq_getElem nbr k hk'
      -- Assemble.
      simpa [hkBang] using hkElem

private theorem getBang_take_of_lt
    (xs : Array Nat) (n k : Nat) (hk : k < n) (hn : n ≤ xs.size) :
    (xs.take n)[k]! = xs[k]! := by
  -- `take n` is `extract 0 n`.
  have hsize : (xs.take n).size = n := by
    simp [Array.take, Array.size_extract, Nat.min_eq_left hn]
  have hkTake : k < (xs.take n).size := by
    simpa [hsize] using hk
  have hkXs : k < xs.size := Nat.lt_of_lt_of_le hk hn
  -- Reduce both sides to explicit proof indexing.
  have hkTakeBang : (xs.take n)[k]! = (xs.take n)[k]'hkTake := by
    exact getBang_eq_getElem (xs.take n) k hkTake
  have hkXsBang : xs[k]! = xs[k]'hkXs := by
    exact getBang_eq_getElem xs k hkXs
  -- Compute the `take` element via `extract`.
  have hkTakeElem : (xs.take n)[k]'hkTake = xs[k]'hkXs := by
    simp [Array.take, Array.getElem_extract]
  -- Assemble.
  calc
    (xs.take n)[k]! = (xs.take n)[k]'hkTake := hkTakeBang
    _ = xs[k]'hkXs := hkTakeElem
    _ = xs[k]! := hkXsBang.symm

private theorem getBang_append_left (xs ys : Array Nat) (k : Nat) (hk : k < xs.size) :
    (xs ++ ys)[k]! = xs[k]! := by
  have hk' : k < (xs ++ ys).size := by
    have hle : xs.size ≤ (xs ++ ys).size := by
      simp [Array.size_append]
    exact Nat.lt_of_lt_of_le hk hle
  calc
    (xs ++ ys)[k]! = (xs ++ ys)[k]'hk' := getBang_eq_getElem (xs ++ ys) k hk'
    _ = xs[k]'hk := by
      simp [hk]
    _ = xs[k]! := (getBang_eq_getElem xs k hk).symm

theorem r1RemoveLast_of_r1Add_ok
    {g g' : PDGraph} {x : Nat} {kind : CurlKind}
    (h : r1Add g x kind = .ok g') :
    r1RemoveLast g' kind = .ok g := by
  classical
  cases kind with
  | pos =>
      -- Extract `validate g = ok` from successful `r1Add`.
      cases hvg : PDGraph.validate g with
      | error e =>
          simp [r1Add, hvg] at h
      | ok u =>
          cases u
          let m : Nat := g.numHalfEdges
          have hgValid : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok (g := g) hvg

          have hx_ge : ¬ x >= m := by
            intro hx_ge
            have hx_ge' : x >= g.numHalfEdges := by
              simpa [m] using hx_ge
            have hcontra := h
            simp [r1Add, hvg, hx_ge'] at hcontra
          have hx : x < m := Nat.lt_of_not_ge hx_ge

          let y : Nat := g.arcNbr[x]!
          have hy : y < m := PDGraph.Valid.get_lt hgValid (i := x) (hi := hx)
          have hy_ne : y ≠ x := PDGraph.Valid.get_ne hgValid (i := x) (hi := hx)
          have hy_invol : g.arcNbr[y]! = x := PDGraph.Valid.invol hgValid (i := x) (hi := hx)
          have hy_ge : ¬ y >= m := Nat.not_le_of_gt hy

          -- Name the exact graph produced by `r1Add`.
          let base : Nat := m
          let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 4 0
          let nbr1 : Array Nat := setPair! nbr0 (base + 0) (base + 1)
          let nbr2 : Array Nat := setPair! nbr1 x (base + 2)
          let nbr3 : Array Nat := setPair! nbr2 y (base + 3)
          let gAdd : PDGraph := { freeLoops := g.freeLoops, n := g.n + 1, arcNbr := nbr3 }

          -- Identify the successful output as `gAdd` and extract `validate gAdd = ok`.
          have hAdd :
              ((match PDGraph.validate gAdd with
                  | .error e => .error e
                  | .ok () => .ok gAdd) : Except String PDGraph) = .ok g' := by
            have hm : g.numHalfEdges = m := by rfl
            have hxy : g.arcNbr[x]! = y := by rfl
            have hmbase : m = base := by rfl
            have hx_ge_base : ¬ base ≤ x := by
              simpa [base] using hx_ge
            have hy_ge_base : ¬ base ≤ y := by
              simpa [base] using hy_ge
            have hnbr0 : g.arcNbr ++ Array.replicate 4 0 = nbr0 := by rfl
            have hnbr1 : setPair! nbr0 base (base + 1) = nbr1 := by
              simp [nbr1]
            have hnbr2 : setPair! nbr1 x (base + 2) = nbr2 := by rfl
            have hnbr3 : setPair! nbr2 y (base + 3) = nbr3 := by rfl
            have hgAdd :
                ({ freeLoops := g.freeLoops, n := g.n + 1, arcNbr := nbr3 } : PDGraph) = gAdd := by rfl
            have h' := h
            simp [r1Add, hvg, hm, hxy, hx_ge_base, hy_ge_base, hy_invol, hmbase, hnbr0, hnbr1, hnbr2, hnbr3, hgAdd] at h'
            exact h'

          have hvgAdd : PDGraph.validate gAdd = .ok () := by
            cases hva : PDGraph.validate gAdd with
            | error e =>
                have hcontra := hAdd
                simp [hva] at hcontra
            | ok u =>
                cases u
                rfl

          have hg' : g' = gAdd := by
            cases hva : PDGraph.validate gAdd with
            | error e =>
                have hcontra := hAdd
                simp [hva] at hcontra
            | ok u =>
                cases u
                have this := hAdd
                simp [hva] at this
                exact this.symm
          subst hg'

          -- Size facts.
          have hmSize : g.arcNbr.size = m := PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg
          have hnbr0Size : nbr0.size = m + 4 := by
            simp [nbr0, Array.size_append, hmSize, Array.size_replicate]
          have hnbr1Size : nbr1.size = m + 4 := by
            simp [nbr1, setPair!, Array.set!, Array.size_setIfInBounds, hnbr0Size]
          have hnbr2Size : nbr2.size = m + 4 := by
            simp [nbr2, setPair!, Array.set!, Array.size_setIfInBounds, hnbr1Size]
          have hnbr3Size : nbr3.size = m + 4 := by
            simp [nbr3, setPair!, Array.set!, Array.size_setIfInBounds, hnbr2Size]

          -- Convenience bounds.
          have hx_lt_nbr1 : x < nbr1.size := by
            have : x < m + 4 := Nat.lt_of_lt_of_le hx (Nat.le_add_right m 4)
            simpa [hnbr1Size] using this
          have hy_lt_nbr2 : y < nbr2.size := by
            have : y < m + 4 := Nat.lt_of_lt_of_le hy (Nat.le_add_right m 4)
            simpa [hnbr2Size] using this
          have hy_lt_nbr3 : y < nbr3.size := by
            have : y < m + 4 := Nat.lt_of_lt_of_le hy (Nat.le_add_right m 4)
            simpa [hnbr3Size] using this
          have hbase0_lt_nbr0 : base + 0 < nbr0.size := by
            simp [base, hnbr0Size]
          have hbase1_lt_nbr0 : base + 1 < nbr0.size := by
            simp [base, hnbr0Size]
          have hbase2_lt_nbr1 : base + 2 < nbr1.size := by
            simp [base, hnbr1Size]
          have hbase3_lt_nbr2 : base + 3 < nbr2.size := by
            simp [base, hnbr2Size]

          -- Key arc identities inside `gAdd.arcNbr = nbr3`.
          have h_int0 : nbr3[base + 0]! = base + 1 := by
            have h1 : nbr3[base + 0]! = nbr2[base + 0]! := by
              have hk : base + 0 < nbr2.size := by simp [hnbr2Size, base]
              have hki : base + 0 ≠ y := Nat.ne_of_gt hy
              have hkj : base + 0 ≠ base + 3 := by simp [base]
              simpa [nbr3] using setPair!_getBang_ne nbr2 y (base + 3) (base + 0) hy_lt_nbr2 hbase3_lt_nbr2 hk hki hkj
            have h2 : nbr2[base + 0]! = nbr1[base + 0]! := by
              have hk : base + 0 < nbr1.size := by simp [hnbr1Size, base]
              have hki : base + 0 ≠ x := Nat.ne_of_gt hx
              have hkj : base + 0 ≠ base + 2 := by simp [base]
              simpa [nbr2] using setPair!_getBang_ne nbr1 x (base + 2) (base + 0) hx_lt_nbr1 hbase2_lt_nbr1 hk hki hkj
            have h3 : nbr1[base + 0]! = base + 1 := by
              have hne : base + 0 ≠ base + 1 := by simp [base]
              simpa [nbr1] using setPair!_getBang_left nbr0 (base + 0) (base + 1) hbase0_lt_nbr0 hbase1_lt_nbr0 hne
            calc
              nbr3[base + 0]! = nbr2[base + 0]! := h1
              _ = nbr1[base + 0]! := h2
              _ = base + 1 := h3

          have h_int1 : nbr3[base + 1]! = base + 0 := by
            have h1 : nbr3[base + 1]! = nbr2[base + 1]! := by
              have hk : base + 1 < nbr2.size := by simp [hnbr2Size, base]
              have hki : base + 1 ≠ y := by
                have hy' : y < base := by simpa [base] using hy
                exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hy' (Nat.le_add_right base 1))
              have hkj : base + 1 ≠ base + 3 := by simp [base]
              simpa [nbr3] using setPair!_getBang_ne nbr2 y (base + 3) (base + 1) hy_lt_nbr2 hbase3_lt_nbr2 hk hki hkj
            have h2 : nbr2[base + 1]! = nbr1[base + 1]! := by
              have hk : base + 1 < nbr1.size := by simp [hnbr1Size, base]
              have hki : base + 1 ≠ x := by
                have hx' : x < base := by simpa [base] using hx
                exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hx' (Nat.le_add_right base 1))
              have hkj : base + 1 ≠ base + 2 := by simp [base]
              simpa [nbr2] using setPair!_getBang_ne nbr1 x (base + 2) (base + 1) hx_lt_nbr1 hbase2_lt_nbr1 hk hki hkj
            have h3 : nbr1[base + 1]! = base + 0 := by
              simpa [nbr1] using setPair!_getBang_right nbr0 (base + 0) (base + 1) hbase0_lt_nbr0 hbase1_lt_nbr0
            calc
              nbr3[base + 1]! = nbr2[base + 1]! := h1
              _ = nbr1[base + 1]! := h2
              _ = base + 0 := h3

          have h_ext1 : nbr3[base + 2]! = x := by
            have h1 : nbr3[base + 2]! = nbr2[base + 2]! := by
              have hk : base + 2 < nbr2.size := by simp [hnbr2Size, base]
              have hki : base + 2 ≠ y := by
                have hy' : y < base := by simpa [base] using hy
                exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hy' (Nat.le_add_right base 2))
              have hkj : base + 2 ≠ base + 3 := by simp [base]
              simpa [nbr3] using setPair!_getBang_ne nbr2 y (base + 3) (base + 2) hy_lt_nbr2 hbase3_lt_nbr2 hk hki hkj
            have h2 : nbr2[base + 2]! = x := by
              have hx_lt_nbr1' : x < nbr1.size := hx_lt_nbr1
              have hk : base + 2 < nbr1.size := hbase2_lt_nbr1
              simpa [nbr2] using setPair!_getBang_right nbr1 x (base + 2) hx_lt_nbr1' hk
            calc
              nbr3[base + 2]! = nbr2[base + 2]! := h1
              _ = x := h2

          have h_ext2 : nbr3[base + 3]! = y := by
            have hy_lt_nbr2' : y < nbr2.size := hy_lt_nbr2
            have hk : base + 3 < nbr2.size := hbase3_lt_nbr2
            simpa [nbr3] using setPair!_getBang_right nbr2 y (base + 3) hy_lt_nbr2' hk

          have h_x_to_ext1 : nbr3[x]! = base + 2 := by
            have h1 : nbr3[x]! = nbr2[x]! := by
              have hx_lt_nbr2 : x < nbr2.size := by
                have : x < m + 4 := Nat.lt_of_lt_of_le hx (Nat.le_add_right m 4)
                simpa [hnbr2Size] using this
              have hki : x ≠ y := hy_ne.symm
              have hkj : x ≠ base + 3 := by
                have : x < m + 3 := Nat.lt_of_lt_of_le hx (Nat.le_add_right m 3)
                exact (Nat.ne_of_lt this)
              simpa [nbr3] using setPair!_getBang_ne nbr2 y (base + 3) x hy_lt_nbr2 hbase3_lt_nbr2 hx_lt_nbr2 hki hkj
            have h2 : nbr2[x]! = base + 2 := by
              have hk : base + 2 < nbr1.size := hbase2_lt_nbr1
              have hne : x ≠ base + 2 := by
                have : x < m + 2 := Nat.lt_of_lt_of_le hx (Nat.le_add_right m 2)
                exact (Nat.ne_of_lt this)
              simpa [nbr2] using setPair!_getBang_left nbr1 x (base + 2) hx_lt_nbr1 hk hne
            calc
              nbr3[x]! = nbr2[x]! := h1
              _ = base + 2 := h2

          have h_y_to_ext2 : nbr3[y]! = base + 3 := by
            have hy_lt_nbr2' : y < nbr2.size := hy_lt_nbr2
            have hne : y ≠ base + 3 := by
              have : y < m + 3 := Nat.lt_of_lt_of_le hy (Nat.le_add_right m 3)
              exact (Nat.ne_of_lt this)
            simpa [nbr3] using setPair!_getBang_left nbr2 y (base + 3) hy_lt_nbr2' hbase3_lt_nbr2 hne

          -- The output arc array is exactly the original `g.arcNbr`.
          let outNbr : Array Nat := setPair! (nbr3.take m) x y
          have houtNbr : outNbr = g.arcNbr := by
            -- Sizes agree.
            have hnTake : m ≤ nbr3.size := by
              -- `nbr3.size = m+4`.
              simp [hnbr3Size]
            have htakeSize : (nbr3.take m).size = m := by
              simp [Array.take, Array.size_extract, Nat.min_eq_left hnTake]
            have houtSize : outNbr.size = g.arcNbr.size := by
              -- `setPair!` preserves size and `take` is exact under `m ≤ size`.
              simp [outNbr, setPair!, Array.set!, Array.size_setIfInBounds, htakeSize, hmSize]
            apply Array.ext houtSize
            intro k hkOut hkG
            have hk : k < m := by
              simpa [hmSize] using hkG
            have hkTake : k < (nbr3.take m).size := by
              simpa [htakeSize] using hk
            have hxTake : x < (nbr3.take m).size := by simpa [htakeSize] using hx
            have hyTake : y < (nbr3.take m).size := by simpa [htakeSize] using hy

            have hBang : outNbr[k]! = g.arcNbr[k]! := by
              by_cases hkx : k = x
              · subst hkx
                -- `outNbr[x] = y = g.arcNbr[x]`.
                have h1 : outNbr[k]! = y := by
                  simpa [outNbr] using setPair!_getBang_left (nbr3.take m) k y hxTake hyTake hy_ne.symm
                simp [y, h1]
              ·
                by_cases hky : k = y
                · subst hky
                  -- `outNbr[y] = x = g.arcNbr[y]` by involution.
                  have h1 : outNbr[y]! = x := by
                    simpa [outNbr] using setPair!_getBang_right (nbr3.take m) x y hxTake hyTake
                  simp [h1, hy_invol]
                ·
                  -- Unchanged indices: use the `setPair!_getBang_ne` lemma.
                  have h1 : outNbr[k]! = (nbr3.take m)[k]! := by
                    simpa [outNbr] using
                      setPair!_getBang_ne (nbr3.take m) x y k hxTake hyTake hkTake hkx hky
                  have h2 : (nbr3.take m)[k]! = nbr3[k]! := by
                    exact getBang_take_of_lt nbr3 m k hk hnTake
                  -- `nbr3` agrees with `g.arcNbr` away from the rewired endpoints.
                  have h3 : nbr3[k]! = g.arcNbr[k]! := by
                    -- Strip off the three `setPair!` calls at indices disjoint from `k`.
                    have hk0 : k < nbr2.size := by
                      have : k < m + 4 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 4)
                      simpa [hnbr2Size] using this
                    have hk1 : k < nbr1.size := by
                      have : k < m + 4 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 4)
                      simpa [hnbr1Size] using this
                    have hk2 : k < nbr0.size := by
                      have : k < m + 4 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 4)
                      simpa [hnbr0Size] using this
                    have hk_ne_base0 : k ≠ base + 0 := by
                      simpa [base] using Nat.ne_of_lt hk
                    have hk_ne_base1 : k ≠ base + 1 := by
                      have : k < m + 1 := Nat.lt_trans hk (Nat.lt_succ_self m)
                      simpa [base] using Nat.ne_of_lt this
                    have hk_ne_base2 : k ≠ base + 2 := by
                      have : k < m + 2 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 2)
                      simpa [base] using Nat.ne_of_lt this
                    have hk_ne_base3 : k ≠ base + 3 := by
                      have : k < m + 3 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 3)
                      simpa [base] using Nat.ne_of_lt this

                    have hA : nbr3[k]! = nbr2[k]! := by
                      simpa [nbr3] using setPair!_getBang_ne nbr2 y (base + 3) k hy_lt_nbr2 hbase3_lt_nbr2 hk0 hky hk_ne_base3
                    have hB : nbr2[k]! = nbr1[k]! := by
                      simpa [nbr2] using setPair!_getBang_ne nbr1 x (base + 2) k hx_lt_nbr1 hbase2_lt_nbr1 hk1 hkx hk_ne_base2
                    have hC : nbr1[k]! = nbr0[k]! := by
                      simpa [nbr1] using setPair!_getBang_ne nbr0 (base + 0) (base + 1) k hbase0_lt_nbr0 hbase1_lt_nbr0 hk2
                        hk_ne_base0 hk_ne_base1
                    -- `nbr0` is `g.arcNbr ++ replicate`, so `k < g.arcNbr.size` uses the left branch.
                    have hkG' : k < g.arcNbr.size := by simpa [hmSize] using hk
                    have hD : nbr0[k]! = g.arcNbr[k]! := by
                      simpa [nbr0] using getBang_append_left g.arcNbr (Array.replicate 4 0) k hkG'
                    exact hA.trans (hB.trans (hC.trans hD))
                  exact (h1.trans (h2.trans h3))

            -- Convert `!` indexing equality to the `GetElem` equality required by `Array.ext`.
            have hkOut' : outNbr[k]! = outNbr[k]'hkOut := getBang_eq_getElem outNbr k hkOut
            have hkG' : g.arcNbr[k]! = g.arcNbr[k]'hkG := getBang_eq_getElem g.arcNbr k hkG
            -- Use the same proofs `hkOut` and `hkG` for the `GetElem` terms.
            calc
              outNbr[k] = outNbr[k]'hkOut := rfl
              _ = outNbr[k]! := hkOut'.symm
              _ = g.arcNbr[k]! := hBang
              _ = g.arcNbr[k]'hkG := hkG'
              _ = g.arcNbr[k] := rfl

          let gOut : PDGraph := { freeLoops := gAdd.freeLoops, n := gAdd.n - 1, arcNbr := outNbr }
          have hgOut : gOut = g := by
            -- Reduce to field equality; `arcNbr` is handled by `houtNbr`.
            cases g with
            | mk fl n arc =>
                simp [gOut, gAdd, outNbr, houtNbr]

          have hvgOut : PDGraph.validate gOut = .ok () := by
            simpa [hgOut] using hvg

          -- Evaluate `r1RemoveLast` on this exact shape.
          have hn0 : gAdd.n ≠ 0 := by
            simp [gAdd]
          have hbaseEq : gAdd.numHalfEdges - 4 = base := by
            simp [PDGraph.numHalfEdges, gAdd, base, m, Nat.mul_add]

          have h_int0' : gAdd.arcNbr[base + 0]! = base + 1 := by
            simpa [gAdd] using h_int0
          have h_int1' : gAdd.arcNbr[base + 1]! = base + 0 := by
            simpa [gAdd] using h_int1
          have h_ext1' : gAdd.arcNbr[base + 2]! = x := by
            simpa [gAdd] using h_ext1
          have h_ext2' : gAdd.arcNbr[base + 3]! = y := by
            simpa [gAdd] using h_ext2
          have h_x_to_ext1' : gAdd.arcNbr[x]! = base + 2 := by
            simpa [gAdd] using h_x_to_ext1
          have h_y_to_ext2' : gAdd.arcNbr[y]! = base + 3 := by
            simpa [gAdd] using h_y_to_ext2

          -- Discharge the checks in `r1RemoveLast` using the computed arc equalities.
          have h_int0m : gAdd.arcNbr[m]! = m + 1 := by
            simpa [base] using h_int0'
          have h_remove :
              r1RemoveLast gAdd CurlKind.pos = .ok gOut := by
            simp [r1RemoveLast, hvgAdd, hbaseEq, base, gAdd, h_int0m, h_int1', h_ext1', h_ext2', h_x_to_ext1',
              h_y_to_ext2', hx_ge, hy_ge, outNbr, gOut]
            have hnTake : m ≤ nbr3.size := by
              simp [hnbr3Size]
            have hvgTmp :
                PDGraph.validate
                    ({ freeLoops := g.freeLoops, n := g.n, arcNbr := setPair! (nbr3.extract 0 m) x y } : PDGraph) =
                  .ok () := by
              simpa [gOut, gAdd, outNbr, Array.take, Nat.min_eq_left hnTake] using hvgOut
            simp [hvgTmp]

          -- Rewrite `gOut = g`.
          rw [← hgOut]
          exact h_remove
  | neg =>
      -- Extract `validate g = ok` from successful `r1Add`.
      cases hvg : PDGraph.validate g with
      | error e =>
          simp [r1Add, hvg] at h
      | ok u =>
          cases u
          let m : Nat := g.numHalfEdges
          have hgValid : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok (g := g) hvg

          have hx_ge : ¬ x >= m := by
            intro hx_ge
            have hx_ge' : x >= g.numHalfEdges := by
              simpa [m] using hx_ge
            have hcontra := h
            simp [r1Add, hvg, hx_ge'] at hcontra
          have hx : x < m := Nat.lt_of_not_ge hx_ge

          let y : Nat := g.arcNbr[x]!
          have hy : y < m := PDGraph.Valid.get_lt hgValid (i := x) (hi := hx)
          have hy_ne : y ≠ x := PDGraph.Valid.get_ne hgValid (i := x) (hi := hx)
          have hy_invol : g.arcNbr[y]! = x := PDGraph.Valid.invol hgValid (i := x) (hi := hx)
          have hy_ge : ¬ y >= m := Nat.not_le_of_gt hy

          -- Name the exact graph produced by `r1Add` (negative curl).
          let base : Nat := m
          let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 4 0
          let nbr1 : Array Nat := setPair! nbr0 (base + 1) (base + 2)
          let nbr2 : Array Nat := setPair! nbr1 x (base + 0)
          let nbr3 : Array Nat := setPair! nbr2 y (base + 3)
          let gAdd : PDGraph := { freeLoops := g.freeLoops, n := g.n + 1, arcNbr := nbr3 }

          have hAdd :
              ((match PDGraph.validate gAdd with
                  | .error e => .error e
                  | .ok () => .ok gAdd) : Except String PDGraph) = .ok g' := by
            have hm : g.numHalfEdges = m := by rfl
            have hxy : g.arcNbr[x]! = y := by rfl
            have hmbase : m = base := by rfl
            have hx_ge_base : ¬ base ≤ x := by
              simpa [base] using hx_ge
            have hy_ge_base : ¬ base ≤ y := by
              simpa [base] using hy_ge
            have hnbr0 : g.arcNbr ++ Array.replicate 4 0 = nbr0 := by rfl
            have hnbr1 : setPair! nbr0 (base + 1) (base + 2) = nbr1 := by rfl
            have hnbr2 : setPair! nbr1 x base = nbr2 := by
              simp [nbr2]
            have hnbr3 : setPair! nbr2 y (base + 3) = nbr3 := by rfl
            have hgAdd :
                ({ freeLoops := g.freeLoops, n := g.n + 1, arcNbr := nbr3 } : PDGraph) = gAdd := by rfl
            have h' := h
            simp [r1Add, hvg, hm, hxy, hx_ge_base, hy_ge_base, hy_invol, hmbase, hnbr0, hnbr1, hnbr2, hnbr3, hgAdd] at h'
            exact h'

          have hvgAdd : PDGraph.validate gAdd = .ok () := by
            cases hva : PDGraph.validate gAdd with
            | error e =>
                have hcontra := hAdd
                simp [hva] at hcontra
            | ok u =>
                cases u
                rfl

          have hg' : g' = gAdd := by
            cases hva : PDGraph.validate gAdd with
            | error e =>
                have hcontra := hAdd
                simp [hva] at hcontra
            | ok u =>
                cases u
                have this := hAdd
                simp [hva] at this
                exact this.symm
          subst hg'

          -- Size facts.
          have hmSize : g.arcNbr.size = m := PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg
          have hnbr0Size : nbr0.size = m + 4 := by
            simp [nbr0, Array.size_append, hmSize, Array.size_replicate]
          have hnbr1Size : nbr1.size = m + 4 := by
            simp [nbr1, setPair!, Array.set!, Array.size_setIfInBounds, hnbr0Size]
          have hnbr2Size : nbr2.size = m + 4 := by
            simp [nbr2, setPair!, Array.set!, Array.size_setIfInBounds, hnbr1Size]
          have hnbr3Size : nbr3.size = m + 4 := by
            simp [nbr3, setPair!, Array.set!, Array.size_setIfInBounds, hnbr2Size]

          have hx_lt_nbr1 : x < nbr1.size := by
            have : x < m + 4 := Nat.lt_of_lt_of_le hx (Nat.le_add_right m 4)
            simpa [hnbr1Size] using this
          have hy_lt_nbr2 : y < nbr2.size := by
            have : y < m + 4 := Nat.lt_of_lt_of_le hy (Nat.le_add_right m 4)
            simpa [hnbr2Size] using this
          have hbase0_lt_nbr1 : base + 0 < nbr1.size := by
            simp [base, hnbr1Size]
          have hbase1_lt_nbr0 : base + 1 < nbr0.size := by
            simp [base, hnbr0Size]
          have hbase2_lt_nbr0 : base + 2 < nbr0.size := by
            simp [base, hnbr0Size]
          have hbase3_lt_nbr2 : base + 3 < nbr2.size := by
            simp [base, hnbr2Size]

          -- Key arc identities inside `gAdd.arcNbr = nbr3` (neg curl shape).
          have h_intA : nbr3[base + 1]! = base + 2 := by
            have h1 : nbr3[base + 1]! = nbr2[base + 1]! := by
                have hk : base + 1 < nbr2.size := by
                  simp [hnbr2Size, base]
                have hki : base + 1 ≠ y := by
                  have hy' : y < base := by simpa [base] using hy
                  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hy' (Nat.le_add_right base 1))
                have hkj : base + 1 ≠ base + 3 := by simp [base]
                simpa [nbr3] using
                  setPair!_getBang_ne nbr2 y (base + 3) (base + 1) hy_lt_nbr2 hbase3_lt_nbr2 hk hki hkj
            have h2 : nbr2[base + 1]! = nbr1[base + 1]! := by
                have hk : base + 1 < nbr1.size := by
                  simp [hnbr1Size, base]
                have hki : base + 1 ≠ x := by
                  have hx' : x < base := by simpa [base] using hx
                  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hx' (Nat.le_add_right base 1))
                have hkj : base + 1 ≠ base + 0 := by simp [base]
                simpa [nbr2] using
                  setPair!_getBang_ne nbr1 x (base + 0) (base + 1) hx_lt_nbr1 hbase0_lt_nbr1 hk hki hkj
            have h3 : nbr1[base + 1]! = base + 2 := by
              have hne : base + 1 ≠ base + 2 := by simp [base]
              simpa [nbr1] using setPair!_getBang_left nbr0 (base + 1) (base + 2) hbase1_lt_nbr0 hbase2_lt_nbr0 hne
            calc
              nbr3[base + 1]! = nbr2[base + 1]! := h1
              _ = nbr1[base + 1]! := h2
              _ = base + 2 := h3

          have h_intB : nbr3[base + 2]! = base + 1 := by
            have h1 : nbr3[base + 2]! = nbr2[base + 2]! := by
                have hk : base + 2 < nbr2.size := by
                  simp [hnbr2Size, base]
                have hki : base + 2 ≠ y := by
                  have hy' : y < base := by simpa [base] using hy
                  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hy' (Nat.le_add_right base 2))
                have hkj : base + 2 ≠ base + 3 := by simp [base]
                simpa [nbr3] using
                  setPair!_getBang_ne nbr2 y (base + 3) (base + 2) hy_lt_nbr2 hbase3_lt_nbr2 hk hki hkj
            have h2 : nbr2[base + 2]! = nbr1[base + 2]! := by
                have hk : base + 2 < nbr1.size := by
                  simp [hnbr1Size, base]
                have hki : base + 2 ≠ x := by
                  have hx' : x < base := by simpa [base] using hx
                  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hx' (Nat.le_add_right base 2))
                have hkj : base + 2 ≠ base + 0 := by simp [base]
                simpa [nbr2] using
                  setPair!_getBang_ne nbr1 x (base + 0) (base + 2) hx_lt_nbr1 hbase0_lt_nbr1 hk hki hkj
            have h3 : nbr1[base + 2]! = base + 1 := by
              simpa [nbr1] using setPair!_getBang_right nbr0 (base + 1) (base + 2) hbase1_lt_nbr0 hbase2_lt_nbr0
            calc
              nbr3[base + 2]! = nbr2[base + 2]! := h1
              _ = nbr1[base + 2]! := h2
              _ = base + 1 := h3

          have h_ext1 : nbr3[base + 0]! = x := by
            have h1 : nbr3[base + 0]! = nbr2[base + 0]! := by
              have hk : base + 0 < nbr2.size := by simp [hnbr2Size, base]
              have hki : base + 0 ≠ y := Nat.ne_of_gt hy
              have hkj : base + 0 ≠ base + 3 := by simp [base]
              simpa [nbr3] using setPair!_getBang_ne nbr2 y (base + 3) (base + 0) hy_lt_nbr2 hbase3_lt_nbr2 hk hki hkj
            have h2 : nbr2[base + 0]! = x := by
              have hk : base + 0 < nbr1.size := by simp [hnbr1Size, base]
              simpa [nbr2] using setPair!_getBang_right nbr1 x (base + 0) hx_lt_nbr1 hk
            calc
              nbr3[base + 0]! = nbr2[base + 0]! := h1
              _ = x := h2

          have h_ext2 : nbr3[base + 3]! = y := by
            have hy_lt_nbr2' : y < nbr2.size := hy_lt_nbr2
            have hk : base + 3 < nbr2.size := hbase3_lt_nbr2
            simpa [nbr3] using setPair!_getBang_right nbr2 y (base + 3) hy_lt_nbr2' hk

          have h_x_to_ext1 : nbr3[x]! = base + 0 := by
            have h1 : nbr3[x]! = nbr2[x]! := by
              have hx_lt_nbr2 : x < nbr2.size := by
                have : x < m + 4 := Nat.lt_of_lt_of_le hx (Nat.le_add_right m 4)
                simpa [hnbr2Size] using this
              have hki : x ≠ y := hy_ne.symm
              have hkj : x ≠ base + 3 := by
                have : x < m + 3 := Nat.lt_of_lt_of_le hx (Nat.le_add_right m 3)
                exact (Nat.ne_of_lt this)
              simpa [nbr3] using setPair!_getBang_ne nbr2 y (base + 3) x hy_lt_nbr2 hbase3_lt_nbr2 hx_lt_nbr2 hki hkj
            have h2 : nbr2[x]! = base + 0 := by
              have hk : base + 0 < nbr1.size := hbase0_lt_nbr1
              have hne : x ≠ base + 0 := by
                simpa [base] using Nat.ne_of_lt hx
              simpa [nbr2] using setPair!_getBang_left nbr1 x (base + 0) hx_lt_nbr1 hk hne
            calc
              nbr3[x]! = nbr2[x]! := h1
              _ = base + 0 := h2

          have h_y_to_ext2 : nbr3[y]! = base + 3 := by
            have hy_lt_nbr2' : y < nbr2.size := hy_lt_nbr2
            have hne : y ≠ base + 3 := by
              have : y < m + 3 := Nat.lt_of_lt_of_le hy (Nat.le_add_right m 3)
              exact (Nat.ne_of_lt this)
            simpa [nbr3] using setPair!_getBang_left nbr2 y (base + 3) hy_lt_nbr2' hbase3_lt_nbr2 hne

          -- Output arc array.
          let outNbr : Array Nat := setPair! (nbr3.take m) x y
          have houtNbr : outNbr = g.arcNbr := by
            have hnTake : m ≤ nbr3.size := by
              simp [hnbr3Size]
            have htakeSize : (nbr3.take m).size = m := by
              simp [Array.take, Array.size_extract, Nat.min_eq_left hnTake]
            have houtSize : outNbr.size = g.arcNbr.size := by
              simp [outNbr, setPair!, Array.set!, Array.size_setIfInBounds, htakeSize, hmSize]
            apply Array.ext houtSize
            intro k hkOut hkG
            have hk : k < m := by
              simpa [hmSize] using hkG
            have hkTake : k < (nbr3.take m).size := by
              simpa [htakeSize] using hk
            have hxTake : x < (nbr3.take m).size := by simpa [htakeSize] using hx
            have hyTake : y < (nbr3.take m).size := by simpa [htakeSize] using hy

            have hBang : outNbr[k]! = g.arcNbr[k]! := by
              by_cases hkx : k = x
              · subst hkx
                have h1 : outNbr[k]! = y := by
                  simpa [outNbr] using setPair!_getBang_left (nbr3.take m) k y hxTake hyTake hy_ne.symm
                simp [y, h1]
              ·
                by_cases hky : k = y
                · subst hky
                  have h1 : outNbr[y]! = x := by
                    simpa [outNbr] using setPair!_getBang_right (nbr3.take m) x y hxTake hyTake
                  simp [h1, hy_invol]
                ·
                  have h1 : outNbr[k]! = (nbr3.take m)[k]! := by
                    simpa [outNbr] using
                      setPair!_getBang_ne (nbr3.take m) x y k hxTake hyTake hkTake hkx hky
                  have h2 : (nbr3.take m)[k]! = nbr3[k]! := by
                    exact getBang_take_of_lt nbr3 m k hk hnTake
                  -- Away from endpoints, `nbr3[k] = g.arcNbr[k]`.
                  have hkG' : k < g.arcNbr.size := by simpa [hmSize] using hk
                  have h3 : nbr3[k]! = g.arcNbr[k]! := by
                    -- `k` is disjoint from all appended indices and from `x` and `y`.
                    have hk2 : k < nbr2.size := by
                      have : k < m + 4 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 4)
                      simpa [hnbr2Size] using this
                    have hk1 : k < nbr1.size := by
                      have : k < m + 4 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 4)
                      simpa [hnbr1Size] using this
                    have hk0 : k < nbr0.size := by
                      have : k < m + 4 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 4)
                      simpa [hnbr0Size] using this
                    have hk_ne_base0 : k ≠ base + 0 := by simpa [base] using Nat.ne_of_lt hk
                    have hk_ne_base1 : k ≠ base + 1 := by
                      have : k < m + 1 := Nat.lt_trans hk (Nat.lt_succ_self m)
                      simpa [base] using Nat.ne_of_lt this
                    have hk_ne_base2 : k ≠ base + 2 := by
                      have : k < m + 2 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 2)
                      simpa [base] using Nat.ne_of_lt this
                    have hk_ne_base3 : k ≠ base + 3 := by
                      have : k < m + 3 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 3)
                      simpa [base] using Nat.ne_of_lt this
                    have hA : nbr3[k]! = nbr2[k]! := by
                      simpa [nbr3] using setPair!_getBang_ne nbr2 y (base + 3) k hy_lt_nbr2 hbase3_lt_nbr2 hk2 hky hk_ne_base3
                    have hB : nbr2[k]! = nbr1[k]! := by
                      simpa [nbr2] using
                        setPair!_getBang_ne nbr1 x (base + 0) k hx_lt_nbr1 hbase0_lt_nbr1 hk1 hkx hk_ne_base0
                    have hC : nbr1[k]! = nbr0[k]! := by
                      simpa [nbr1] using
                        setPair!_getBang_ne nbr0 (base + 1) (base + 2) k hbase1_lt_nbr0 hbase2_lt_nbr0 hk0 hk_ne_base1
                          hk_ne_base2
                    have hD : nbr0[k]! = g.arcNbr[k]! := by
                      simpa [nbr0] using getBang_append_left g.arcNbr (Array.replicate 4 0) k hkG'
                    exact hA.trans (hB.trans (hC.trans hD))
                  exact h1.trans (h2.trans h3)

            have hkOutBang : outNbr[k]! = outNbr[k]'hkOut := getBang_eq_getElem outNbr k hkOut
            have hkGBang : g.arcNbr[k]! = g.arcNbr[k]'hkG := getBang_eq_getElem g.arcNbr k hkG
            calc
              outNbr[k] = outNbr[k]'hkOut := rfl
              _ = outNbr[k]! := hkOutBang.symm
              _ = g.arcNbr[k]! := hBang
              _ = g.arcNbr[k]'hkG := hkGBang
              _ = g.arcNbr[k] := rfl

          let gOut : PDGraph := { freeLoops := gAdd.freeLoops, n := gAdd.n - 1, arcNbr := outNbr }
          have hgOut : gOut = g := by
            cases g with
            | mk fl n arc =>
                simp [gOut, gAdd, outNbr, houtNbr]

          have hvgOut : PDGraph.validate gOut = .ok () := by
            simpa [hgOut] using hvg

          have hn0 : gAdd.n ≠ 0 := by
            simp [gAdd]
          have hbaseEq : gAdd.numHalfEdges - 4 = base := by
            simp [PDGraph.numHalfEdges, gAdd, base, m, Nat.mul_add]

          have h_remove : r1RemoveLast gAdd CurlKind.neg = .ok gOut := by
            have h_intA' : gAdd.arcNbr[base + 1]! = base + 2 := by simpa [gAdd] using h_intA
            have h_intB' : gAdd.arcNbr[base + 2]! = base + 1 := by simpa [gAdd] using h_intB
            have h_ext1' : gAdd.arcNbr[base + 0]! = x := by simpa [gAdd] using h_ext1
            have h_ext2' : gAdd.arcNbr[base + 3]! = y := by simpa [gAdd] using h_ext2
            have h_x_to_ext1' : gAdd.arcNbr[x]! = base + 0 := by simpa [gAdd] using h_x_to_ext1
            have h_y_to_ext2' : gAdd.arcNbr[y]! = base + 3 := by simpa [gAdd] using h_y_to_ext2
            have h_ext1'' : gAdd.arcNbr[m]! = x := by
              simpa [base] using h_ext1'
            have h_x_to_ext1'' : gAdd.arcNbr[x]! = m := by
              simpa [base] using h_x_to_ext1'
            have hTmp :
                ({ freeLoops := gAdd.freeLoops, n := gAdd.n - 1, arcNbr := setPair! (gAdd.arcNbr.extract 0 m) x y } : PDGraph) =
                  gOut := by
              have hArc : setPair! (gAdd.arcNbr.extract 0 m) x y = outNbr := by
                dsimp [outNbr, Array.take, gAdd]
              simp [gOut, hArc]
            have hRhs :
                ({ freeLoops := gAdd.freeLoops, n := gAdd.n - 1, arcNbr := setPair! (nbr3.extract 0 m) x y } : PDGraph) =
                  gOut := by
              have hArc : setPair! (nbr3.extract 0 m) x y = outNbr := by
                dsimp [outNbr, Array.take]
              simp [gOut, hArc]
            simp [r1RemoveLast, hvgAdd, hn0, hbaseEq, base, h_intA', h_intB', h_ext1'', h_ext2', h_x_to_ext1'',
              h_y_to_ext2', hx_ge, hy_ge, outNbr, gOut, hTmp, hRhs, hvgOut]

          simpa [hgOut] using h_remove

set_option maxHeartbeats 2000000 in
theorem r2RemoveLast_of_r2Add_ok
    {g g' : PDGraph} {x u : Nat}
    (h : r2Add g x u = .ok g') :
    r2RemoveLast g' = .ok g := by
  classical
  -- Extract `validate g = ok` from successful `r2Add`.
  cases hvg : PDGraph.validate g with
  | error e =>
      simp [r2Add, hvg] at h
  | ok uValid =>
      cases uValid
      let m : Nat := g.numHalfEdges
      have hgValid : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok (g := g) hvg

      -- Range conditions: `x,u < m`.
      have hx_ge : ¬ x ≥ m := by
        intro hxge
        have hcontra := h
        simp [r2Add, hvg, m, hxge] at hcontra
      have hu_ge : ¬ u ≥ m := by
        intro huge
        have hcontra := h
        simp [r2Add, hvg, m, huge] at hcontra
      have hx : x < m := Nat.lt_of_not_ge hx_ge
      have hu : u < m := Nat.lt_of_not_ge hu_ge

      let y : Nat := g.arcNbr[x]!
      let v : Nat := g.arcNbr[u]!
      have hy : y < m := PDGraph.Valid.get_lt hgValid (i := x) (hi := hx)
      have hv : v < m := PDGraph.Valid.get_lt hgValid (i := u) (hi := hu)
      have hy_ne : y ≠ x := PDGraph.Valid.get_ne hgValid (i := x) (hi := hx)
      have hv_ne : v ≠ u := PDGraph.Valid.get_ne hgValid (i := u) (hi := hu)
      have hy_invol : g.arcNbr[y]! = x := PDGraph.Valid.invol hgValid (i := x) (hi := hx)
      have hv_invol : g.arcNbr[v]! = u := PDGraph.Valid.invol hgValid (i := u) (hi := hu)
      have hy_ge : ¬ y ≥ m := Nat.not_le_of_gt hy
      have hv_ge : ¬ v ≥ m := Nat.not_le_of_gt hv

      -- The disjointness check must be false.
      have hdisj : (x == u || x == v || y == u || y == v) = false := by
        cases hcond : (x == u || x == v || y == u || y == v) with
        | false =>
            rfl
        | true =>
            exfalso
            have hcontra := h
            simp [r2Add, hvg, m, y, v, hx_ge, hu_ge, hy_ge, hv_ge, hy_invol, hv_invol, hcond] at hcontra

      -- Extract Prop-level disjointness facts from the boolean check.
      have hx_ne_u : x ≠ u := by
        have h' := hdisj
        simp at h'
        exact h'.1.1.1
      have hx_ne_v : x ≠ v := by
        have h' := hdisj
        simp at h'
        exact h'.1.1.2
      have hy_ne_u : y ≠ u := by
        have h' := hdisj
        simp at h'
        exact h'.1.2
      have hy_ne_v : y ≠ v := by
        have h' := hdisj
        simp at h'
        exact h'.2

      -- Canonicalize endpoints exactly as `r2Add` does.
      let xy : Nat × Nat := if x < y then (x, y) else (y, x)
      let x1 : Nat := xy.1
      let y1 : Nat := xy.2
      let uv : Nat × Nat := if u < v then (u, v) else (v, u)
      let u1 : Nat := uv.1
      let v1 : Nat := uv.2
      let ord : Nat × Nat × Nat × Nat := if u1 < x1 then (u1, v1, x1, y1) else (x1, y1, u1, v1)
      let x0 : Nat := ord.1
      let y0 : Nat := ord.2.1
      let u0 : Nat := ord.2.2.1
      let v0 : Nat := ord.2.2.2

      -- Bounds for the canonical endpoints.
      have hx1_lt : x1 < m := by
        by_cases hxy : x < y <;> simp [x1, xy, hxy, hx, hy]
      have hy1_lt : y1 < m := by
        by_cases hxy : x < y <;> simp [y1, xy, hxy, hx, hy]
      have hu1_lt : u1 < m := by
        by_cases huv : u < v <;> simp [u1, uv, huv, hu, hv]
      have hv1_lt : v1 < m := by
        by_cases huv : u < v <;> simp [v1, uv, huv, hu, hv]

      have hx0_lt : x0 < m := by
        by_cases hswap : u1 < x1 <;> simp [x0, ord, hswap, hx1_lt, hu1_lt]
      have hy0_lt : y0 < m := by
        by_cases hswap : u1 < x1 <;> simp [y0, ord, hswap, hy1_lt, hv1_lt]
      have hu0_lt : u0 < m := by
        by_cases hswap : u1 < x1 <;> simp [u0, ord, hswap, hx1_lt, hu1_lt]
      have hv0_lt : v0 < m := by
        by_cases hswap : u1 < x1 <;> simp [v0, ord, hswap, hy1_lt, hv1_lt]

      -- Distinctness between canonical endpoints.
      have hx1_ne_y1 : x1 ≠ y1 := by
        by_cases hxy : x < y <;> simp [x1, y1, xy, hxy, hy_ne, hy_ne.symm]
      have hu1_ne_v1 : u1 ≠ v1 := by
        by_cases huv : u < v <;> simp [u1, v1, uv, huv, hv_ne, hv_ne.symm]

      have hx1_ne_u1 : x1 ≠ u1 := by
        by_cases hxy : x < y <;> by_cases huv : u < v <;>
          simp [x1, u1, xy, uv, hxy, huv, hx_ne_u, hx_ne_v, hy_ne_u, hy_ne_v]
      have hx1_ne_v1 : x1 ≠ v1 := by
        by_cases hxy : x < y <;> by_cases huv : u < v <;>
          simp [x1, v1, xy, uv, hxy, huv, hx_ne_u, hx_ne_v, hy_ne_u, hy_ne_v]
      have hy1_ne_u1 : y1 ≠ u1 := by
        by_cases hxy : x < y <;> by_cases huv : u < v <;>
          simp [y1, u1, xy, uv, hxy, huv, hx_ne_u, hx_ne_v, hy_ne_u, hy_ne_v]
      have hy1_ne_v1 : y1 ≠ v1 := by
        by_cases hxy : x < y <;> by_cases huv : u < v <;>
          simp [y1, v1, xy, uv, hxy, huv, hx_ne_u, hx_ne_v, hy_ne_u, hy_ne_v]

      have hx0_ne_y0 : x0 ≠ y0 := by
        by_cases hswap : u1 < x1 <;>
          simp [x0, y0, ord, hswap, hx1_ne_y1, hu1_ne_v1]
      have hu0_ne_v0 : u0 ≠ v0 := by
        by_cases hswap : u1 < x1 <;>
          simp [u0, v0, ord, hswap, hx1_ne_y1, hu1_ne_v1]

      have hx0_ne_u0 : x0 ≠ u0 := by
        by_cases hswap : u1 < x1
        · simp [x0, u0, ord, hswap, hx1_ne_u1.symm]
        · simp [x0, u0, ord, hswap, hx1_ne_u1]
      have hx0_ne_v0 : x0 ≠ v0 := by
        by_cases hswap : u1 < x1
        · simp [x0, v0, ord, hswap, hy1_ne_u1.symm]
        · simp [x0, v0, ord, hswap, hx1_ne_v1]
      have hy0_ne_u0 : y0 ≠ u0 := by
        by_cases hswap : u1 < x1
        · simp [y0, u0, ord, hswap, hx1_ne_v1.symm]
        · simp [y0, u0, ord, hswap, hy1_ne_u1]
      have hy0_ne_v0 : y0 ≠ v0 := by
        by_cases hswap : u1 < x1
        · simp [y0, v0, ord, hswap, hy1_ne_v1.symm]
        · simp [y0, v0, ord, hswap, hy1_ne_v1]

      -- The arc involution on canonical endpoints (back in the original graph `g`).
      have hx1_arc : g.arcNbr[x1]! = y1 := by
        by_cases hxy : x < y <;> simp [x1, y1, xy, hxy, y, hy_invol]
      have hy1_arc : g.arcNbr[y1]! = x1 := by
        by_cases hxy : x < y <;> simp [x1, y1, xy, hxy, y, hy_invol]
      have hu1_arc : g.arcNbr[u1]! = v1 := by
        by_cases huv : u < v <;> simp [u1, v1, uv, huv, v, hv_invol]
      have hv1_arc : g.arcNbr[v1]! = u1 := by
        by_cases huv : u < v <;> simp [u1, v1, uv, huv, v, hv_invol]

      have hx0_arc : g.arcNbr[x0]! = y0 := by
        by_cases hswap : u1 < x1 <;>
          simp [x0, y0, ord, hswap, hx1_arc, hu1_arc]
      have hy0_arc : g.arcNbr[y0]! = x0 := by
        by_cases hswap : u1 < x1 <;>
          simp [x0, y0, ord, hswap, hy1_arc, hv1_arc]
      have hu0_arc : g.arcNbr[u0]! = v0 := by
        by_cases hswap : u1 < x1 <;>
          simp [u0, v0, ord, hswap, hu1_arc, hx1_arc]
      have hv0_arc : g.arcNbr[v0]! = u0 := by
        by_cases hswap : u1 < x1 <;>
          simp [u0, v0, ord, hswap, hv1_arc, hy1_arc]

      -- Name the exact graph produced by `r2Add`.
      let base1 : Nat := m
      let base2 : Nat := m + 4
      let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 8 0
      let nbr1 : Array Nat := setPair! nbr0 x0 (base1 + 0)
      let nbr2 : Array Nat := setPair! nbr1 y0 (base2 + 1)
      let nbr3 : Array Nat := setPair! nbr2 u0 (base1 + 3)
      let nbr4 : Array Nat := setPair! nbr3 v0 (base2 + 2)
      let nbr5 : Array Nat := setPair! nbr4 (base1 + 1) (base2 + 0)
      let nbr6 : Array Nat := setPair! nbr5 (base1 + 2) (base2 + 3)
      let gAdd : PDGraph := { freeLoops := g.freeLoops, n := g.n + 2, arcNbr := nbr6 }

      -- Identify the successful output as `gAdd` and extract `validate gAdd = ok`.
      have hAdd :
          ((match PDGraph.validate gAdd with
                | .error e => .error e
                | .ok () => .ok gAdd) : Except String PDGraph) = .ok g' := by
        have h' := h
        simpa [r2Add, hvg, m, y, v, hx_ge, hu_ge, hy_ge, hv_ge, hy_invol, hv_invol, hdisj, x1, y1, u1, v1, x0,
          y0, u0, v0, base1, base2, nbr0, nbr1, nbr2, nbr3, nbr4, nbr5, nbr6, gAdd] using h'

      have hvgAdd : PDGraph.validate gAdd = .ok () := by
        cases hva : PDGraph.validate gAdd with
        | error e =>
            have hcontra := hAdd
            simp [hva] at hcontra
        | ok u =>
            cases u
            rfl

      have hg' : g' = gAdd := by
        cases hva : PDGraph.validate gAdd with
        | error e =>
            have hcontra := hAdd
            simp [hva] at hcontra
        | ok u =>
            cases u
            have this := hAdd
            simp [hva] at this
            exact this.symm
      subst hg'

      -- Size facts.
      have hmSize : g.arcNbr.size = m := PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg
      have hnbr0Size : nbr0.size = m + 8 := by
        simp [nbr0, Array.size_append, hmSize, Array.size_replicate]
      have hnbr1Size : nbr1.size = m + 8 := by
        simp [nbr1, setPair!, Array.set!, Array.size_setIfInBounds, hnbr0Size]
      have hnbr2Size : nbr2.size = m + 8 := by
        simp [nbr2, setPair!, Array.set!, Array.size_setIfInBounds, hnbr1Size]
      have hnbr3Size : nbr3.size = m + 8 := by
        simp [nbr3, setPair!, Array.set!, Array.size_setIfInBounds, hnbr2Size]
      have hnbr4Size : nbr4.size = m + 8 := by
        simp [nbr4, setPair!, Array.set!, Array.size_setIfInBounds, hnbr3Size]
      have hnbr5Size : nbr5.size = m + 8 := by
        simp [nbr5, setPair!, Array.set!, Array.size_setIfInBounds, hnbr4Size]
      have hnbr6Size : nbr6.size = m + 8 := by
        simp [nbr6, setPair!, Array.set!, Array.size_setIfInBounds, hnbr5Size]

      -- Convenience bounds in `nbr*` arrays.
      have hx0_lt_nbr0 : x0 < nbr0.size := by
        have : x0 < m + 8 := Nat.lt_of_lt_of_le hx0_lt (Nat.le_add_right m 8)
        simpa [hnbr0Size] using this
      have hy0_lt_nbr1 : y0 < nbr1.size := by
        have : y0 < m + 8 := Nat.lt_of_lt_of_le hy0_lt (Nat.le_add_right m 8)
        simpa [hnbr1Size] using this
      have hu0_lt_nbr2 : u0 < nbr2.size := by
        have : u0 < m + 8 := Nat.lt_of_lt_of_le hu0_lt (Nat.le_add_right m 8)
        simpa [hnbr2Size] using this
      have hv0_lt_nbr3 : v0 < nbr3.size := by
        have : v0 < m + 8 := Nat.lt_of_lt_of_le hv0_lt (Nat.le_add_right m 8)
        simpa [hnbr3Size] using this

      have hbase1_0_lt_nbr0 : base1 + 0 < nbr0.size := by
        simp [base1, hnbr0Size]
      have hbase1_1_lt_nbr4 : base1 + 1 < nbr4.size := by
        simp [base1, hnbr4Size]
      have hbase1_2_lt_nbr5 : base1 + 2 < nbr5.size := by
        simp [base1, hnbr5Size]
      have hbase1_3_lt_nbr2 : base1 + 3 < nbr2.size := by
        simp [base1, hnbr2Size]

      have hbase2_0_lt_nbr4 : base2 + 0 < nbr4.size := by
        simp [base2, hnbr4Size]
      have hbase2_1_lt_nbr1 : base2 + 1 < nbr1.size := by
        simp [base2, hnbr1Size]
      have hbase2_2_lt_nbr3 : base2 + 2 < nbr3.size := by
        simp [base2, hnbr3Size]
      have hbase2_3_lt_nbr5 : base2 + 3 < nbr5.size := by
        simp [base2, hnbr5Size]

      -- Key arc identities inside `gAdd.arcNbr = nbr6`.
      have h_int10 : nbr6[base1 + 1]! = base2 + 0 := by
        have h1 : nbr6[base1 + 1]! = nbr5[base1 + 1]! := by
          have hk : base1 + 1 < nbr5.size := by
            simp [hnbr5Size, base1]
          have hki : base1 + 1 ≠ base1 + 2 := by simp [base1]
          have hkj : base1 + 1 ≠ base2 + 3 := by simp [base1, base2]
          simpa [nbr6] using
            setPair!_getBang_ne nbr5 (base1 + 2) (base2 + 3) (base1 + 1) hbase1_2_lt_nbr5 hbase2_3_lt_nbr5 hk hki
              hkj
        have h2 : nbr5[base1 + 1]! = base2 + 0 := by
          have hk : base1 + 1 < nbr4.size := hbase1_1_lt_nbr4
          have hne : base1 + 1 ≠ base2 + 0 := by simp [base1, base2]
          simpa [nbr5] using setPair!_getBang_left nbr4 (base1 + 1) (base2 + 0) hk hbase2_0_lt_nbr4 hne
        exact h1.trans h2

      have h_int01 : nbr6[base2 + 0]! = base1 + 1 := by
        have h1 : nbr6[base2 + 0]! = nbr5[base2 + 0]! := by
          have hk : base2 + 0 < nbr5.size := by
            simp [base2, hnbr5Size]
          have hki : base2 + 0 ≠ base1 + 2 := by simp [base1, base2]
          have hkj : base2 + 0 ≠ base2 + 3 := by simp [base2]
          simpa [nbr6] using
            setPair!_getBang_ne nbr5 (base1 + 2) (base2 + 3) (base2 + 0) hbase1_2_lt_nbr5 hbase2_3_lt_nbr5 hk hki
              hkj
        have h2 : nbr5[base2 + 0]! = base1 + 1 := by
          have hk : base2 + 0 < nbr4.size := hbase2_0_lt_nbr4
          simpa [nbr5] using setPair!_getBang_right nbr4 (base1 + 1) (base2 + 0) hbase1_1_lt_nbr4 hk
        exact h1.trans h2

      have h_int23 : nbr6[base1 + 2]! = base2 + 3 := by
        have hk : base1 + 2 < nbr5.size := hbase1_2_lt_nbr5
        have hne : base1 + 2 ≠ base2 + 3 := by simp [base1, base2]
        simpa [nbr6] using setPair!_getBang_left nbr5 (base1 + 2) (base2 + 3) hk hbase2_3_lt_nbr5 hne

      have h_int32 : nbr6[base2 + 3]! = base1 + 2 := by
        have hk : base2 + 3 < nbr5.size := hbase2_3_lt_nbr5
        simpa [nbr6] using setPair!_getBang_right nbr5 (base1 + 2) (base2 + 3) hbase1_2_lt_nbr5 hk

      have h_base10 : nbr6[base1 + 0]! = x0 := by
        have h1 : nbr6[base1 + 0]! = nbr5[base1 + 0]! := by
          have hk : base1 + 0 < nbr5.size := by
            simp [hnbr5Size, base1]
          have hki : base1 + 0 ≠ base1 + 2 := by simp [base1]
          have hkj : base1 + 0 ≠ base2 + 3 := by
            apply Nat.ne_of_lt
            simp [base1, base2, Nat.add_assoc]
          simpa [nbr6] using
            setPair!_getBang_ne nbr5 (base1 + 2) (base2 + 3) (base1 + 0) hbase1_2_lt_nbr5 hbase2_3_lt_nbr5 hk hki
              hkj
        have h2 : nbr5[base1 + 0]! = nbr4[base1 + 0]! := by
          have hk : base1 + 0 < nbr4.size := by
            simp [hnbr4Size, base1]
          have hki : base1 + 0 ≠ base1 + 1 := by simp [base1]
          have hkj : base1 + 0 ≠ base2 + 0 := by
            apply Nat.ne_of_lt
            simp [base1, base2]
          simpa [nbr5] using
            setPair!_getBang_ne nbr4 (base1 + 1) (base2 + 0) (base1 + 0) hbase1_1_lt_nbr4 hbase2_0_lt_nbr4 hk hki
              hkj
        have h3 : nbr4[base1 + 0]! = nbr3[base1 + 0]! := by
          have hk : base1 + 0 < nbr3.size := by
            simp [hnbr3Size, base1]
          have hki : base1 + 0 ≠ v0 := by
            have : v0 < base1 := by simpa [base1] using hv0_lt
            exact Nat.ne_of_gt this
          have hkj : base1 + 0 ≠ base2 + 2 := by
            apply Nat.ne_of_lt
            simp [base1, base2, Nat.add_assoc]
          simpa [nbr4] using setPair!_getBang_ne nbr3 v0 (base2 + 2) (base1 + 0) hv0_lt_nbr3 hbase2_2_lt_nbr3 hk hki hkj
        have h4 : nbr3[base1 + 0]! = nbr2[base1 + 0]! := by
          have hk : base1 + 0 < nbr2.size := by
            simp [hnbr2Size, base1]
          have hki : base1 + 0 ≠ u0 := by
            have : u0 < base1 := by simpa [base1] using hu0_lt
            exact Nat.ne_of_gt this
          have hkj : base1 + 0 ≠ base1 + 3 := by simp [base1]
          simpa [nbr3] using setPair!_getBang_ne nbr2 u0 (base1 + 3) (base1 + 0) hu0_lt_nbr2 hbase1_3_lt_nbr2 hk hki hkj
        have h5 : nbr2[base1 + 0]! = nbr1[base1 + 0]! := by
          have hk : base1 + 0 < nbr1.size := by
            simp [hnbr1Size, base1]
          have hki : base1 + 0 ≠ y0 := by
            have : y0 < base1 := by simpa [base1] using hy0_lt
            exact Nat.ne_of_gt this
          have hkj : base1 + 0 ≠ base2 + 1 := by
            apply Nat.ne_of_lt
            simp [base1, base2, Nat.add_assoc]
          simpa [nbr2] using setPair!_getBang_ne nbr1 y0 (base2 + 1) (base1 + 0) hy0_lt_nbr1 hbase2_1_lt_nbr1 hk hki hkj
        have h6 : nbr1[base1 + 0]! = x0 := by
          have hk : base1 + 0 < nbr0.size := hbase1_0_lt_nbr0
          simpa [nbr1] using setPair!_getBang_right nbr0 x0 (base1 + 0) hx0_lt_nbr0 hk
        exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

      have h_x0_to_base10 : nbr6[x0]! = base1 + 0 := by
        have h1 : nbr6[x0]! = nbr5[x0]! := by
          have hk : x0 < nbr5.size := by
            have : x0 < m + 8 := Nat.lt_of_lt_of_le hx0_lt (Nat.le_add_right m 8)
            simpa [hnbr5Size] using this
          have hki : x0 ≠ base1 + 2 := by
            have : x0 < base1 := by simpa [base1] using hx0_lt
            exact Nat.ne_of_lt (Nat.lt_trans this (Nat.lt_add_of_pos_right (by decide : 0 < 2)))
          have hkj : x0 ≠ base2 + 3 := by
            have : x0 < base2 := by
              have : x0 < m + 4 := Nat.lt_of_lt_of_le hx0_lt (Nat.le_add_right m 4)
              simpa [base2] using this
            exact Nat.ne_of_lt (Nat.lt_trans this (Nat.lt_add_of_pos_right (by decide : 0 < 3)))
          simpa [nbr6] using setPair!_getBang_ne nbr5 (base1 + 2) (base2 + 3) x0 hbase1_2_lt_nbr5 hbase2_3_lt_nbr5 hk hki hkj
        have h2 : nbr5[x0]! = nbr4[x0]! := by
          have hk : x0 < nbr4.size := by
            have : x0 < m + 8 := Nat.lt_of_lt_of_le hx0_lt (Nat.le_add_right m 8)
            simpa [hnbr4Size] using this
          have hki : x0 ≠ base1 + 1 := by
            have : x0 < base1 := by simpa [base1] using hx0_lt
            exact Nat.ne_of_lt (Nat.lt_trans this (Nat.lt_add_of_pos_right (by decide : 0 < 1)))
          have hkj : x0 ≠ base2 + 0 := by
            have : x0 < base2 := by
              have : x0 < m + 4 := Nat.lt_of_lt_of_le hx0_lt (Nat.le_add_right m 4)
              simpa [base2] using this
            exact Nat.ne_of_lt this
          simpa [nbr5] using setPair!_getBang_ne nbr4 (base1 + 1) (base2 + 0) x0 hbase1_1_lt_nbr4 hbase2_0_lt_nbr4 hk hki hkj
        have h3 : nbr4[x0]! = nbr3[x0]! := by
          have hk : x0 < nbr3.size := by
            have : x0 < m + 8 := Nat.lt_of_lt_of_le hx0_lt (Nat.le_add_right m 8)
            simpa [hnbr3Size] using this
          have hki : x0 ≠ v0 := hx0_ne_v0
          have hkj : x0 ≠ base2 + 2 := by
            have : x0 < base2 := by
              have : x0 < m + 4 := Nat.lt_of_lt_of_le hx0_lt (Nat.le_add_right m 4)
              simpa [base2] using this
            exact Nat.ne_of_lt (Nat.lt_trans this (Nat.lt_add_of_pos_right (by decide : 0 < 2)))
          simpa [nbr4] using setPair!_getBang_ne nbr3 v0 (base2 + 2) x0 hv0_lt_nbr3 hbase2_2_lt_nbr3 hk hki hkj
        have h4 : nbr3[x0]! = nbr2[x0]! := by
          have hk : x0 < nbr2.size := by
            have : x0 < m + 8 := Nat.lt_of_lt_of_le hx0_lt (Nat.le_add_right m 8)
            simpa [hnbr2Size] using this
          have hki : x0 ≠ u0 := hx0_ne_u0
          have hkj : x0 ≠ base1 + 3 := by
            have : x0 < base1 := by simpa [base1] using hx0_lt
            exact Nat.ne_of_lt (Nat.lt_trans this (Nat.lt_add_of_pos_right (by decide : 0 < 3)))
          simpa [nbr3] using setPair!_getBang_ne nbr2 u0 (base1 + 3) x0 hu0_lt_nbr2 hbase1_3_lt_nbr2 hk hki hkj
        have h5 : nbr2[x0]! = nbr1[x0]! := by
          have hk : x0 < nbr1.size := by
            have : x0 < m + 8 := Nat.lt_of_lt_of_le hx0_lt (Nat.le_add_right m 8)
            simpa [hnbr1Size] using this
          have hki : x0 ≠ y0 := hx0_ne_y0
          have hkj : x0 ≠ base2 + 1 := by
            have : x0 < base2 := by
              have : x0 < m + 4 := Nat.lt_of_lt_of_le hx0_lt (Nat.le_add_right m 4)
              simpa [base2] using this
            exact Nat.ne_of_lt (Nat.lt_trans this (Nat.lt_add_of_pos_right (by decide : 0 < 1)))
          simpa [nbr2] using setPair!_getBang_ne nbr1 y0 (base2 + 1) x0 hy0_lt_nbr1 hbase2_1_lt_nbr1 hk hki hkj
        have h6 : nbr1[x0]! = base1 + 0 := by
          have hne : x0 ≠ base1 + 0 := by
            have : x0 < base1 := by simpa [base1] using hx0_lt
            exact Nat.ne_of_lt this
          simpa [nbr1] using setPair!_getBang_left nbr0 x0 (base1 + 0) hx0_lt_nbr0 hbase1_0_lt_nbr0 hne
        exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

      -- External endpoints on the right crossing.
      have h_base21 : nbr6[base2 + 1]! = y0 := by
        have hk : base2 + 1 < nbr5.size := by
          simp [base2, hnbr5Size]
        have h1 : nbr6[base2 + 1]! = nbr5[base2 + 1]! := by
          have hki : base2 + 1 ≠ base1 + 2 := by simp [base1, base2]
          have hkj : base2 + 1 ≠ base2 + 3 := by simp [base2]
          simpa [nbr6] using
            setPair!_getBang_ne nbr5 (base1 + 2) (base2 + 3) (base2 + 1) hbase1_2_lt_nbr5 hbase2_3_lt_nbr5 hk hki hkj
        have h2 : nbr5[base2 + 1]! = nbr4[base2 + 1]! := by
          have hk4 : base2 + 1 < nbr4.size := by
            simp [base2, hnbr4Size]
          have hki : base2 + 1 ≠ base1 + 1 := by simp [base1, base2]
          have hkj : base2 + 1 ≠ base2 + 0 := by simp [base2]
          simpa [nbr5] using
            setPair!_getBang_ne nbr4 (base1 + 1) (base2 + 0) (base2 + 1) hbase1_1_lt_nbr4 hbase2_0_lt_nbr4 hk4 hki hkj
        have h3 : nbr4[base2 + 1]! = nbr3[base2 + 1]! := by
          have hk3 : base2 + 1 < nbr3.size := by
            simp [base2, hnbr3Size]
          have hki : base2 + 1 ≠ v0 := by
            have hv0_lt_base2 : v0 < base2 + 1 := by
              have : v0 < m + 5 := Nat.lt_of_lt_of_le hv0_lt (Nat.le_add_right m 5)
              simpa [base2] using this
            exact Nat.ne_of_gt hv0_lt_base2
          have hkj : base2 + 1 ≠ base2 + 2 := by simp [base2]
          simpa [nbr4] using setPair!_getBang_ne nbr3 v0 (base2 + 2) (base2 + 1) hv0_lt_nbr3 hbase2_2_lt_nbr3 hk3 hki hkj
        have h4 : nbr3[base2 + 1]! = nbr2[base2 + 1]! := by
          have hk2 : base2 + 1 < nbr2.size := by
            simp [base2, hnbr2Size]
          have hki : base2 + 1 ≠ u0 := by
            have hu0_lt_base2 : u0 < base2 + 1 := by
              have : u0 < m + 5 := Nat.lt_of_lt_of_le hu0_lt (Nat.le_add_right m 5)
              simpa [base2] using this
            exact Nat.ne_of_gt hu0_lt_base2
          have hkj : base2 + 1 ≠ base1 + 3 := by simp [base1, base2]
          simpa [nbr3] using setPair!_getBang_ne nbr2 u0 (base1 + 3) (base2 + 1) hu0_lt_nbr2 hbase1_3_lt_nbr2 hk2 hki hkj
        have h5 : nbr2[base2 + 1]! = y0 := by
          have hk1 : base2 + 1 < nbr1.size := hbase2_1_lt_nbr1
          simpa [nbr2] using setPair!_getBang_right nbr1 y0 (base2 + 1) hy0_lt_nbr1 hk1
        exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

      have h_y0_to_base21 : nbr6[y0]! = base2 + 1 := by
        have h1 : nbr6[y0]! = nbr5[y0]! := by
          have hk : y0 < nbr5.size := by
            have : y0 < m + 8 := Nat.lt_of_lt_of_le hy0_lt (Nat.le_add_right m 8)
            simpa [hnbr5Size] using this
          have hki : y0 ≠ base1 + 2 := by
            have : y0 < base1 := by simpa [base1] using hy0_lt
            exact Nat.ne_of_lt (Nat.lt_trans this (Nat.lt_add_of_pos_right (by decide : 0 < 2)))
          have hkj : y0 ≠ base2 + 3 := by
            have : y0 < base2 := by
              have : y0 < m + 4 := Nat.lt_of_lt_of_le hy0_lt (Nat.le_add_right m 4)
              simpa [base2] using this
            exact Nat.ne_of_lt (Nat.lt_trans this (Nat.lt_add_of_pos_right (by decide : 0 < 3)))
          simpa [nbr6] using setPair!_getBang_ne nbr5 (base1 + 2) (base2 + 3) y0 hbase1_2_lt_nbr5 hbase2_3_lt_nbr5 hk hki hkj
        have h2 : nbr5[y0]! = nbr4[y0]! := by
          have hk : y0 < nbr4.size := by
            have : y0 < m + 8 := Nat.lt_of_lt_of_le hy0_lt (Nat.le_add_right m 8)
            simpa [hnbr4Size] using this
          have hki : y0 ≠ base1 + 1 := by
            have : y0 < base1 := by simpa [base1] using hy0_lt
            exact Nat.ne_of_lt (Nat.lt_trans this (Nat.lt_add_of_pos_right (by decide : 0 < 1)))
          have hkj : y0 ≠ base2 + 0 := by
            have : y0 < base2 := by
              have : y0 < m + 4 := Nat.lt_of_lt_of_le hy0_lt (Nat.le_add_right m 4)
              simpa [base2] using this
            exact Nat.ne_of_lt this
          simpa [nbr5] using setPair!_getBang_ne nbr4 (base1 + 1) (base2 + 0) y0 hbase1_1_lt_nbr4 hbase2_0_lt_nbr4 hk hki hkj
        have h3 : nbr4[y0]! = nbr3[y0]! := by
          have hk : y0 < nbr3.size := by
            have : y0 < m + 8 := Nat.lt_of_lt_of_le hy0_lt (Nat.le_add_right m 8)
            simpa [hnbr3Size] using this
          have hki : y0 ≠ v0 := by
            exact (hy0_ne_v0)
          have hkj : y0 ≠ base2 + 2 := by
            have : y0 < base2 := by
              have : y0 < m + 4 := Nat.lt_of_lt_of_le hy0_lt (Nat.le_add_right m 4)
              simpa [base2] using this
            exact Nat.ne_of_lt (Nat.lt_trans this (Nat.lt_add_of_pos_right (by decide : 0 < 2)))
          simpa [nbr4] using setPair!_getBang_ne nbr3 v0 (base2 + 2) y0 hv0_lt_nbr3 hbase2_2_lt_nbr3 hk hki hkj
        have h4 : nbr3[y0]! = nbr2[y0]! := by
          have hk : y0 < nbr2.size := by
            have : y0 < m + 8 := Nat.lt_of_lt_of_le hy0_lt (Nat.le_add_right m 8)
            simpa [hnbr2Size] using this
          have hki : y0 ≠ u0 := hy0_ne_u0
          have hkj : y0 ≠ base1 + 3 := by
            have : y0 < base1 := by simpa [base1] using hy0_lt
            exact Nat.ne_of_lt (Nat.lt_trans this (Nat.lt_add_of_pos_right (by decide : 0 < 3)))
          simpa [nbr3] using setPair!_getBang_ne nbr2 u0 (base1 + 3) y0 hu0_lt_nbr2 hbase1_3_lt_nbr2 hk hki hkj
        have h5 : nbr2[y0]! = base2 + 1 := by
          have hne : y0 ≠ base2 + 1 := by
            have : y0 < base2 := by
              have : y0 < m + 4 := Nat.lt_of_lt_of_le hy0_lt (Nat.le_add_right m 4)
              simpa [base2] using this
            exact Nat.ne_of_lt (Nat.lt_trans this (Nat.lt_add_of_pos_right (by decide : 0 < 1)))
          simpa [nbr2] using setPair!_getBang_left nbr1 y0 (base2 + 1) hy0_lt_nbr1 hbase2_1_lt_nbr1 hne
        exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

      have h_base13 : nbr6[base1 + 3]! = u0 := by
        have h1 : nbr6[base1 + 3]! = nbr5[base1 + 3]! := by
          have hk : base1 + 3 < nbr5.size := by
            simp [hnbr5Size, base1]
          have hki : base1 + 3 ≠ base1 + 2 := by simp [base1]
          have hkj : base1 + 3 ≠ base2 + 3 := by simp [base1, base2]
          simpa [nbr6] using
            setPair!_getBang_ne nbr5 (base1 + 2) (base2 + 3) (base1 + 3) hbase1_2_lt_nbr5 hbase2_3_lt_nbr5 hk hki hkj
        have h2 : nbr5[base1 + 3]! = nbr4[base1 + 3]! := by
          have hk : base1 + 3 < nbr4.size := by
            simp [hnbr4Size, base1]
          have hki : base1 + 3 ≠ base1 + 1 := by simp [base1]
          have hkj : base1 + 3 ≠ base2 + 0 := by simp [base1, base2]
          simpa [nbr5] using
            setPair!_getBang_ne nbr4 (base1 + 1) (base2 + 0) (base1 + 3) hbase1_1_lt_nbr4 hbase2_0_lt_nbr4 hk hki hkj
        have h3 : nbr4[base1 + 3]! = nbr3[base1 + 3]! := by
          have hk : base1 + 3 < nbr3.size := by
            simp [hnbr3Size, base1]
          have hki : base1 + 3 ≠ v0 := by
            have hv0_lt_base1_3 : v0 < base1 + 3 := by
              have : v0 < m + 3 := Nat.lt_of_lt_of_le hv0_lt (Nat.le_add_right m 3)
              simpa [base1] using this
            exact Nat.ne_of_gt hv0_lt_base1_3
          have hkj : base1 + 3 ≠ base2 + 2 := by simp [base1, base2]
          simpa [nbr4] using
            setPair!_getBang_ne nbr3 v0 (base2 + 2) (base1 + 3) hv0_lt_nbr3 hbase2_2_lt_nbr3 hk hki hkj
        have h4 : nbr3[base1 + 3]! = u0 := by
          have hk : base1 + 3 < nbr2.size := hbase1_3_lt_nbr2
          simpa [nbr3] using setPair!_getBang_right nbr2 u0 (base1 + 3) hu0_lt_nbr2 hk
        exact h1.trans (h2.trans (h3.trans h4))

      have h_u0_to_base13 : nbr6[u0]! = base1 + 3 := by
        have h1 : nbr6[u0]! = nbr5[u0]! := by
          have hk : u0 < nbr5.size := by
            have : u0 < m + 8 := Nat.lt_of_lt_of_le hu0_lt (Nat.le_add_right m 8)
            simpa [hnbr5Size] using this
          have hki : u0 ≠ base1 + 2 := by
            have : u0 < base1 := by simpa [base1] using hu0_lt
            exact Nat.ne_of_lt (Nat.lt_trans this (Nat.lt_add_of_pos_right (by decide : 0 < 2)))
          have hkj : u0 ≠ base2 + 3 := by
            have : u0 < m + 7 := Nat.lt_of_lt_of_le hu0_lt (Nat.le_add_right m 7)
            simpa [base2] using Nat.ne_of_lt this
          simpa [nbr6] using setPair!_getBang_ne nbr5 (base1 + 2) (base2 + 3) u0 hbase1_2_lt_nbr5 hbase2_3_lt_nbr5 hk hki hkj
        have h2 : nbr5[u0]! = nbr4[u0]! := by
          have hk : u0 < nbr4.size := by
            have : u0 < m + 8 := Nat.lt_of_lt_of_le hu0_lt (Nat.le_add_right m 8)
            simpa [hnbr4Size] using this
          have hki : u0 ≠ base1 + 1 := by
            have : u0 < base1 := by simpa [base1] using hu0_lt
            exact Nat.ne_of_lt (Nat.lt_trans this (Nat.lt_add_of_pos_right (by decide : 0 < 1)))
          have hkj : u0 ≠ base2 + 0 := by
            have : u0 < base2 := by
              have : u0 < m + 4 := Nat.lt_of_lt_of_le hu0_lt (Nat.le_add_right m 4)
              simpa [base2] using this
            exact Nat.ne_of_lt this
          simpa [nbr5] using setPair!_getBang_ne nbr4 (base1 + 1) (base2 + 0) u0 hbase1_1_lt_nbr4 hbase2_0_lt_nbr4 hk hki hkj
        have h3 : nbr4[u0]! = nbr3[u0]! := by
          have hk : u0 < nbr3.size := by
            have : u0 < m + 8 := Nat.lt_of_lt_of_le hu0_lt (Nat.le_add_right m 8)
            simpa [hnbr3Size] using this
          have hkj : u0 ≠ base2 + 2 := by
            have : u0 < m + 6 := Nat.lt_of_lt_of_le hu0_lt (Nat.le_add_right m 6)
            simpa [base2] using Nat.ne_of_lt this
          simpa [nbr4] using setPair!_getBang_ne nbr3 v0 (base2 + 2) u0 hv0_lt_nbr3 hbase2_2_lt_nbr3 hk hu0_ne_v0 hkj
        have h4 : nbr3[u0]! = base1 + 3 := by
          have hne : u0 ≠ base1 + 3 := by
            have : u0 < base1 := by simpa [base1] using hu0_lt
            exact Nat.ne_of_lt (Nat.lt_trans this (Nat.lt_add_of_pos_right (by decide : 0 < 3)))
          simpa [nbr3] using setPair!_getBang_left nbr2 u0 (base1 + 3) hu0_lt_nbr2 hbase1_3_lt_nbr2 hne
        exact h1.trans (h2.trans (h3.trans h4))

      have h_base22 : nbr6[base2 + 2]! = v0 := by
        have h1 : nbr6[base2 + 2]! = nbr5[base2 + 2]! := by
          have hk : base2 + 2 < nbr5.size := by
            simp [base2, hnbr5Size]
          have hki : base2 + 2 ≠ base1 + 2 := by simp [base1, base2]
          have hkj : base2 + 2 ≠ base2 + 3 := by simp [base2]
          simpa [nbr6] using setPair!_getBang_ne nbr5 (base1 + 2) (base2 + 3) (base2 + 2) hbase1_2_lt_nbr5 hbase2_3_lt_nbr5 hk hki hkj
        have h2 : nbr5[base2 + 2]! = nbr4[base2 + 2]! := by
          have hk : base2 + 2 < nbr4.size := by
            simp [base2, hnbr4Size]
          have hki : base2 + 2 ≠ base1 + 1 := by simp [base1, base2]
          have hkj : base2 + 2 ≠ base2 + 0 := by simp [base2]
          simpa [nbr5] using setPair!_getBang_ne nbr4 (base1 + 1) (base2 + 0) (base2 + 2) hbase1_1_lt_nbr4 hbase2_0_lt_nbr4 hk hki hkj
        have h3 : nbr4[base2 + 2]! = v0 := by
          have hk : base2 + 2 < nbr3.size := hbase2_2_lt_nbr3
          simpa [nbr4] using setPair!_getBang_right nbr3 v0 (base2 + 2) hv0_lt_nbr3 hk
        exact h1.trans (h2.trans h3)

      have h_v0_to_base22 : nbr6[v0]! = base2 + 2 := by
        have h1 : nbr6[v0]! = nbr5[v0]! := by
          have hk : v0 < nbr5.size := by
            have : v0 < m + 8 := Nat.lt_of_lt_of_le hv0_lt (Nat.le_add_right m 8)
            simpa [hnbr5Size] using this
          have hki : v0 ≠ base1 + 2 := by
            have : v0 < base1 := by simpa [base1] using hv0_lt
            exact Nat.ne_of_lt (Nat.lt_trans this (Nat.lt_add_of_pos_right (by decide : 0 < 2)))
          have hkj : v0 ≠ base2 + 3 := by
            have : v0 < m + 7 := Nat.lt_of_lt_of_le hv0_lt (Nat.le_add_right m 7)
            simpa [base2] using Nat.ne_of_lt this
          simpa [nbr6] using setPair!_getBang_ne nbr5 (base1 + 2) (base2 + 3) v0 hbase1_2_lt_nbr5 hbase2_3_lt_nbr5 hk hki hkj
        have h2 : nbr5[v0]! = nbr4[v0]! := by
          have hk : v0 < nbr4.size := by
            have : v0 < m + 8 := Nat.lt_of_lt_of_le hv0_lt (Nat.le_add_right m 8)
            simpa [hnbr4Size] using this
          have hki : v0 ≠ base1 + 1 := by
            have : v0 < base1 := by simpa [base1] using hv0_lt
            exact Nat.ne_of_lt (Nat.lt_trans this (Nat.lt_add_of_pos_right (by decide : 0 < 1)))
          have hkj : v0 ≠ base2 + 0 := by
            have : v0 < base2 := by
              have : v0 < m + 4 := Nat.lt_of_lt_of_le hv0_lt (Nat.le_add_right m 4)
              simpa [base2] using this
            exact Nat.ne_of_lt this
          simpa [nbr5] using setPair!_getBang_ne nbr4 (base1 + 1) (base2 + 0) v0 hbase1_1_lt_nbr4 hbase2_0_lt_nbr4 hk hki hkj
        have h3 : nbr4[v0]! = base2 + 2 := by
          have hne : v0 ≠ base2 + 2 := by
            have : v0 < m + 6 := Nat.lt_of_lt_of_le hv0_lt (Nat.le_add_right m 6)
            simpa [base2] using Nat.ne_of_lt this
          simpa [nbr4] using setPair!_getBang_left nbr3 v0 (base2 + 2) hv0_lt_nbr3 hbase2_2_lt_nbr3 hne
        exact h1.trans (h2.trans h3)

      let outNbr : Array Nat := setPair! (setPair! (nbr6.take base1) x0 y0) u0 v0
      have houtNbr : outNbr = g.arcNbr := by
        -- Sizes agree.
        have hnTake : base1 ≤ nbr6.size := by
          simp [base1, hnbr6Size]
        have htakeSize : (nbr6.take base1).size = base1 := by
          simp [Array.take, Array.size_extract, Nat.min_eq_left hnTake]
        let nbrXY : Array Nat := setPair! (nbr6.take base1) x0 y0
        have hnbrXYSize : nbrXY.size = base1 := by
          simp [nbrXY, setPair!, Array.set!, Array.size_setIfInBounds, htakeSize]
        have houtSize : outNbr.size = g.arcNbr.size := by
          simp [outNbr, setPair!, Array.set!, Array.size_setIfInBounds, htakeSize, hmSize, base1]
        apply Array.ext houtSize
        intro k hkOut hkG
        have hk : k < m := by
          simpa [hmSize] using hkG
        have hkTake : k < (nbr6.take base1).size := by
          simpa [htakeSize, base1] using hk
        have hx0Take : x0 < (nbr6.take base1).size := by simpa [htakeSize, base1] using hx0_lt
        have hy0Take : y0 < (nbr6.take base1).size := by simpa [htakeSize, base1] using hy0_lt
        have hu0Take : u0 < (nbr6.take base1).size := by simpa [htakeSize, base1] using hu0_lt
        have hv0Take : v0 < (nbr6.take base1).size := by simpa [htakeSize, base1] using hv0_lt
        have hkXY : k < nbrXY.size := by simpa [hnbrXYSize, base1] using hk
        have hx0XY : x0 < nbrXY.size := by simpa [hnbrXYSize, base1] using hx0_lt
        have hy0XY : y0 < nbrXY.size := by simpa [hnbrXYSize, base1] using hy0_lt
        have hu0XY : u0 < nbrXY.size := by simpa [hnbrXYSize, base1] using hu0_lt
        have hv0XY : v0 < nbrXY.size := by simpa [hnbrXYSize, base1] using hv0_lt

        have hBang : outNbr[k]! = g.arcNbr[k]! := by
          by_cases hkx0 : k = x0
          · subst hkx0
            have h1 : outNbr[x0]! = nbrXY[x0]! := by
              simpa [outNbr] using setPair!_getBang_ne nbrXY u0 v0 x0 hu0XY hv0XY hx0XY hx0_ne_u0 hx0_ne_v0
            have h2 : nbrXY[x0]! = y0 := by
              simpa [nbrXY] using setPair!_getBang_left (nbr6.take base1) x0 y0 hx0Take hy0Take hx0_ne_y0
            simp [h1.trans h2, hx0_arc]
          ·
            by_cases hky0 : k = y0
            · subst hky0
              have h1 : outNbr[y0]! = nbrXY[y0]! := by
                simpa [outNbr] using setPair!_getBang_ne nbrXY u0 v0 y0 hu0XY hv0XY hy0XY hy0_ne_u0 hy0_ne_v0
              have h2 : nbrXY[y0]! = x0 := by
                simpa [nbrXY] using setPair!_getBang_right (nbr6.take base1) x0 y0 hx0Take hy0Take
              simp [h1.trans h2, hy0_arc]
            ·
              by_cases hku0 : k = u0
              · subst hku0
                have h1 : outNbr[u0]! = v0 := by
                  simpa [outNbr] using setPair!_getBang_left nbrXY u0 v0 hu0XY hv0XY hu0_ne_v0
                simp [h1, hu0_arc]
              ·
                by_cases hkv0 : k = v0
                · subst hkv0
                  have h1 : outNbr[v0]! = u0 := by
                    simpa [outNbr] using setPair!_getBang_right nbrXY u0 v0 hu0XY hv0XY
                  simp [h1, hv0_arc]
                ·
                  have h1 : outNbr[k]! = nbrXY[k]! := by
                    simpa [outNbr] using setPair!_getBang_ne nbrXY u0 v0 k hu0XY hv0XY hkXY hku0 hkv0
                  have h2 : nbrXY[k]! = (nbr6.take base1)[k]! := by
                    simpa [nbrXY] using setPair!_getBang_ne (nbr6.take base1) x0 y0 k hx0Take hy0Take hkTake hkx0 hky0
                  have h3 : (nbr6.take base1)[k]! = nbr6[k]! := by
                    exact getBang_take_of_lt nbr6 base1 k (by simpa [base1] using hk) hnTake
                  have h4 : nbr6[k]! = g.arcNbr[k]! := by
                    have hk6 : k < nbr6.size := by
                      have : k < m + 8 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 8)
                      simpa [hnbr6Size] using this
                    have hk5 : k < nbr5.size := by
                      have : k < m + 8 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 8)
                      simpa [hnbr5Size] using this
                    have hk4 : k < nbr4.size := by
                      have : k < m + 8 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 8)
                      simpa [hnbr4Size] using this
                    have hk3 : k < nbr3.size := by
                      have : k < m + 8 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 8)
                      simpa [hnbr3Size] using this
                    have hk2 : k < nbr2.size := by
                      have : k < m + 8 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 8)
                      simpa [hnbr2Size] using this
                    have hk1 : k < nbr1.size := by
                      have : k < m + 8 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 8)
                      simpa [hnbr1Size] using this
                    have hk0 : k < nbr0.size := by
                      have : k < m + 8 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 8)
                      simpa [hnbr0Size] using this

                    have hk_ne_base1_2 : k ≠ base1 + 2 := by
                      have : k < m + 2 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 2)
                      simpa [base1] using Nat.ne_of_lt this
                    have hk_ne_base2_3 : k ≠ base2 + 3 := by
                      have : k < m + 7 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 7)
                      simpa [base2] using Nat.ne_of_lt this
                    have hk_ne_base1_1 : k ≠ base1 + 1 := by
                      have : k < m + 1 := Nat.lt_trans hk (Nat.lt_succ_self m)
                      simpa [base1] using Nat.ne_of_lt this
                    have hk_ne_base2_0 : k ≠ base2 + 0 := by
                      have : k < m + 4 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 4)
                      simpa [base2] using Nat.ne_of_lt this
                    have hk_ne_base2_2 : k ≠ base2 + 2 := by
                      have : k < m + 6 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 6)
                      simpa [base2] using Nat.ne_of_lt this
                    have hk_ne_base1_3 : k ≠ base1 + 3 := by
                      have : k < m + 3 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 3)
                      simpa [base1] using Nat.ne_of_lt this
                    have hk_ne_base2_1 : k ≠ base2 + 1 := by
                      have : k < m + 5 := Nat.lt_of_lt_of_le hk (Nat.le_add_right m 5)
                      simpa [base2] using Nat.ne_of_lt this
                    have hk_ne_base1_0 : k ≠ base1 + 0 := by
                      simpa [base1] using Nat.ne_of_lt hk

                    have hA : nbr6[k]! = nbr5[k]! := by
                      simpa [nbr6] using
                        setPair!_getBang_ne nbr5 (base1 + 2) (base2 + 3) k hbase1_2_lt_nbr5 hbase2_3_lt_nbr5 hk5 hk_ne_base1_2
                          hk_ne_base2_3
                    have hB : nbr5[k]! = nbr4[k]! := by
                      simpa [nbr5] using
                        setPair!_getBang_ne nbr4 (base1 + 1) (base2 + 0) k hbase1_1_lt_nbr4 hbase2_0_lt_nbr4 hk4 hk_ne_base1_1
                          hk_ne_base2_0
                    have hC : nbr4[k]! = nbr3[k]! := by
                      simpa [nbr4] using
                        setPair!_getBang_ne nbr3 v0 (base2 + 2) k hv0_lt_nbr3 hbase2_2_lt_nbr3 hk3 hkv0 hk_ne_base2_2
                    have hD : nbr3[k]! = nbr2[k]! := by
                      simpa [nbr3] using
                        setPair!_getBang_ne nbr2 u0 (base1 + 3) k hu0_lt_nbr2 hbase1_3_lt_nbr2 hk2 hku0 hk_ne_base1_3
                    have hE : nbr2[k]! = nbr1[k]! := by
                      simpa [nbr2] using
                        setPair!_getBang_ne nbr1 y0 (base2 + 1) k hy0_lt_nbr1 hbase2_1_lt_nbr1 hk1 hky0 hk_ne_base2_1
                    have hF : nbr1[k]! = nbr0[k]! := by
                      simpa [nbr1] using
                        setPair!_getBang_ne nbr0 x0 (base1 + 0) k hx0_lt_nbr0 hbase1_0_lt_nbr0 hk0 hkx0 hk_ne_base1_0
                    have hG : nbr0[k]! = g.arcNbr[k]! := by
                      simpa [nbr0] using getBang_append_left g.arcNbr (Array.replicate 8 0) k hkG
                    exact hA.trans (hB.trans (hC.trans (hD.trans (hE.trans (hF.trans hG)))))
                  exact h1.trans (h2.trans (h3.trans h4))

        have hkOutBang : outNbr[k]! = outNbr[k]'hkOut := getBang_eq_getElem outNbr k hkOut
        have hkGBang : g.arcNbr[k]! = g.arcNbr[k]'hkG := getBang_eq_getElem g.arcNbr k hkG
        calc
          outNbr[k] = outNbr[k]'hkOut := rfl
          _ = outNbr[k]! := hkOutBang.symm
          _ = g.arcNbr[k]! := hBang
          _ = g.arcNbr[k]'hkG := hkGBang
          _ = g.arcNbr[k] := rfl

      let gOut : PDGraph := { freeLoops := gAdd.freeLoops, n := gAdd.n - 2, arcNbr := outNbr }
      have hgOut : gOut = g := by
        cases g with
        | mk fl n arc =>
            simp [gOut, gAdd, outNbr, houtNbr]
      have hvgOut : PDGraph.validate gOut = .ok () := by
        simpa [hgOut] using hvg

      have hnlt : ¬ gAdd.n < 2 := by
        have hn_ge : 2 ≤ gAdd.n := by
          simp [gAdd]
        exact Nat.not_lt_of_ge hn_ge
      have hbase1Eq : gAdd.numHalfEdges - 8 = base1 := by
        simp [PDGraph.numHalfEdges, gAdd, base1, m, Nat.mul_add]
      have hbase2Eq : gAdd.numHalfEdges - 4 = base2 := by
        simp [PDGraph.numHalfEdges, gAdd, base2, m, Nat.mul_add]

      have hx0_ge_base1 : ¬ x0 ≥ base1 := Nat.not_le_of_gt (by simpa [base1] using hx0_lt)
      have hu0_ge_base1 : ¬ u0 ≥ base1 := Nat.not_le_of_gt (by simpa [base1] using hu0_lt)
      have hy0_ge_base1 : ¬ y0 ≥ base1 := Nat.not_le_of_gt (by simpa [base1] using hy0_lt)
      have hv0_ge_base1 : ¬ v0 ≥ base1 := Nat.not_le_of_gt (by simpa [base1] using hv0_lt)

      have h_remove : r2RemoveLast gAdd = .ok gOut := by
        have h_int10' : gAdd.arcNbr[base1 + 1]! = base2 + 0 := by simpa [gAdd] using h_int10
        have h_int01' : gAdd.arcNbr[base2 + 0]! = base1 + 1 := by simpa [gAdd] using h_int01
        have h_int23' : gAdd.arcNbr[base1 + 2]! = base2 + 3 := by simpa [gAdd] using h_int23
        have h_int32' : gAdd.arcNbr[base2 + 3]! = base1 + 2 := by simpa [gAdd] using h_int32
        have h_base10' : gAdd.arcNbr[base1 + 0]! = x0 := by simpa [gAdd] using h_base10
        have h_base13' : gAdd.arcNbr[base1 + 3]! = u0 := by simpa [gAdd] using h_base13
        have h_base21' : gAdd.arcNbr[base2 + 1]! = y0 := by simpa [gAdd] using h_base21
        have h_base22' : gAdd.arcNbr[base2 + 2]! = v0 := by simpa [gAdd] using h_base22
        have h_x0_back' : gAdd.arcNbr[x0]! = base1 + 0 := by simpa [gAdd] using h_x0_to_base10
        have h_u0_back' : gAdd.arcNbr[u0]! = base1 + 3 := by simpa [gAdd] using h_u0_to_base13
        have h_y0_back' : gAdd.arcNbr[y0]! = base2 + 1 := by simpa [gAdd] using h_y0_to_base21
        have h_v0_back' : gAdd.arcNbr[v0]! = base2 + 2 := by simpa [gAdd] using h_v0_to_base22
        have hnbr6_m : nbr6[m]! = x0 := by
          simpa [base1] using h_base10
        have hx0_not_ge : ¬m ≤ nbr6[m]! := by
          have : ¬m ≤ x0 := Nat.not_le_of_gt hx0_lt
          simpa [hnbr6_m] using this
        have hx0_back : nbr6[nbr6[m]!]! = m := by
          calc
            nbr6[nbr6[m]!]! = nbr6[x0]! := by simp [hnbr6_m]
            _ = m := by simpa [base1] using h_x0_to_base10

        simp [r2RemoveLast, gAdd, hvgAdd, hnlt, hbase1Eq, hbase2Eq, base1, base2, h_int10', h_int01', h_int23',
          h_int32', h_base13', h_base21', h_base22', hx0_ge_base1, hu0_ge_base1, hy0_ge_base1,
          hv0_ge_base1, h_x0_back', h_u0_back', h_y0_back', h_v0_back', hnbr6_m, outNbr, gOut, Array.take]

        have houtNbr_extract :
            outNbr = setPair! (setPair! (nbr6.extract 0 m) x0 y0) u0 v0 := by
          dsimp [outNbr, Array.take, base1]

        have hgTmp :
            ({ freeLoops := g.freeLoops, n := g.n, arcNbr := setPair! (setPair! (nbr6.extract 0 m) x0 y0) u0 v0 } :
                PDGraph) =
              gOut := by
          simp [gOut, gAdd, houtNbr_extract]

        have hvgTmp :
            ({ freeLoops := g.freeLoops, n := g.n, arcNbr := setPair! (setPair! (nbr6.extract 0 m) x0 y0) u0 v0 } :
                PDGraph).validate =
              .ok () := by
          simpa [hgTmp] using hvgOut

        simp [hvgTmp]

      simpa [hgOut] using h_remove

end InverseLaws
end Reidemeister

end Knot
end Topology
end HeytingLean
