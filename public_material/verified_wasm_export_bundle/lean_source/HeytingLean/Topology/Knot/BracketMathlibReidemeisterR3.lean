import HeytingLean.Topology.Knot.BracketMathlib
import HeytingLean.Topology.Knot.BracketMathlibAuxOk
import HeytingLean.Topology.Knot.BracketMathlibReidemeisterR2
import HeytingLean.Topology.Knot.BracketMathlibSmoothValid
import HeytingLean.Topology.Knot.BracketMathlibTemperleyLieb
import HeytingLean.Topology.Knot.Reidemeister

/-!
# Knot theory: Reidemeister-III invariance (Mathlib proof layer) — scaffolding

This file is the Phase‑1 entry point for the *theorem-level* Reidemeister‑III (R3) invariance proof
of the Mathlib-valued Kauffman bracket evaluator `Kauffman.bracketGraphML`.

In this iteration we add the foundational “constructor facts” needed to unfold the evaluator
deterministically on the braid-style R3 move (`r3BraidLeft` / `r3BraidRight`).

The full invariance theorem will build on these lemmas.
-/

namespace HeytingLean
namespace Topology
namespace Knot

namespace Kauffman

open scoped LaurentPolynomial
open Reidemeister

noncomputable section

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

attribute [local irreducible] PDGraph.validate

/-!
## Concrete braid gadget graphs (definition-level)

We name the explicit arc-neighbor arrays used by the braid-style R3 constructors. This lets later
proofs refer to the braid gadget deterministically without reintroducing large `let` blocks.
-/

private def r3BraidLeftNbr (g : PDGraph) (x u w : Nat) : Array Nat :=
  let m := g.numHalfEdges
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
  let nbr :=
    setPair!
      (setPair!
        (setPair!
          (setPair!
            (setPair!
              (setPair!
                (setPair!
                  (setPair!
                    (setPair! nbr0 x (baseA + 0)) u (baseA + 1))
                  w (baseB + 1))
                x2 (baseB + 3))
              w2 (baseC + 2))
            u2 (baseC + 3))
          (baseA + 2) (baseC + 0))
        (baseA + 3) (baseB + 0))
      (baseB + 2) (baseC + 1)
  nbr

private def r3BraidRightNbr (g : PDGraph) (x u w : Nat) : Array Nat :=
  let m := g.numHalfEdges
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
  let nbr :=
    setPair!
      (setPair!
        (setPair!
          (setPair!
            (setPair!
              (setPair!
                (setPair!
                  (setPair!
                    (setPair! nbr0 u (baseA + 0)) w (baseA + 1))
                  x (baseB + 0))
                w2 (baseB + 2))
              u2 (baseC + 2))
            x2 (baseC + 3))
          (baseA + 2) (baseB + 1))
        (baseB + 3) (baseC + 0))
      (baseA + 3) (baseC + 1)
  nbr

private def r3BraidLeftGraph (g : PDGraph) (x u w : Nat) : PDGraph :=
  { freeLoops := g.freeLoops, n := g.n + 3, arcNbr := r3BraidLeftNbr g x u w }

private def r3BraidRightGraph (g : PDGraph) (x u w : Nat) : PDGraph :=
  { freeLoops := g.freeLoops, n := g.n + 3, arcNbr := r3BraidRightNbr g x u w }

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
      have hkBang : nbr[k]! = nbr[k]'hk' := by
        exact getBang_eq_getElem nbr k hk'
      simpa [hkBang] using hkElem

private theorem setBang_size {α : Type} (a : Array α) (i : Nat) (v : α) : (a.set! i v).size = a.size := by
  by_cases hi : i < a.size <;> simp [Array.set!, Array.setIfInBounds, hi]

private theorem setBang_getBang_self
    (a : Array Nat) (i : Nat) (x : Nat) (hi : i < a.size) :
    (a.set! i x)[i]! = x := by
  have hi' : i < (a.set! i x).size := by
    simpa [setBang_size (a := a) (i := i) (v := x)] using hi
  have hEq : a.set! i x = a.set i x hi := by
    simp [Array.set!, Array.setIfInBounds, hi]
  calc
    (a.set! i x)[i]! = (a.set! i x)[i]'hi' := by
      simpa using (getBang_eq_getElem (a := a.set! i x) (i := i) hi')
    _ = (a.set i x hi)[i]'(by simpa [hEq, Array.size_set] using hi) := by
      simp [hEq]
    _ = x := by
      simp [Array.getElem_set_self]

private theorem setBang_getBang_ne
    (a : Array Nat) (i k : Nat) (x : Nat) (hi : i < a.size) (hk : k < a.size) (hik : k ≠ i) :
    (a.set! i x)[k]! = a[k]! := by
  have hk' : k < (a.set! i x).size := by
    simpa [setBang_size (a := a) (i := i) (v := x)] using hk
  calc
    (a.set! i x)[k]! = (a.set! i x)[k]'hk' := by
      simpa using (getBang_eq_getElem (a := a.set! i x) (i := k) hk')
    _ = (a.set i x hi)[k]'(by simpa [Array.size_set] using hk) := by
      -- Reduce `set!` to `set` using the in-bounds proof `hi`.
      simp [Array.set!, Array.setIfInBounds, hi]
    _ = a[k]'hk := by
      simpa [hik.symm] using
        (Array.getElem_set_ne (xs := a) (i := i) (h' := hi) (v := x) (j := k) (pj := hk) (h := hik.symm))
    _ = a[k]! := by
      symm
      exact getBang_eq_getElem a k hk

private theorem setPair!_size (nbr : Array Nat) (i j : Nat) : (setPair! nbr i j).size = nbr.size := by
  unfold setPair!
  calc
    ((nbr.set! i j).set! j i).size = (nbr.set! i j).size := setBang_size (a := nbr.set! i j) (i := j) (v := i)
    _ = nbr.size := setBang_size (a := nbr) (i := i) (v := j)

theorem r3BraidLeft_n_eq
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    gL.n = g.n + 3 := by
  classical
  cases hvg : PDGraph.validate g with
  | error e =>
      have hEq : (Except.error e : Except String PDGraph) = .ok gL := by
        simpa [Reidemeister.r3BraidLeft, hvg, Bind.bind, Except.bind] using h
      cases hEq
  | ok hv =>
      cases hv
      let m := g.numHalfEdges
      by_cases hx : x < m
      · by_cases hu : u < m
        · by_cases hw : w < m
          · have hx_ge : ¬ x >= m := Nat.not_le_of_gt hx
            have hu_ge : ¬ u >= m := Nat.not_le_of_gt hu
            have hw_ge : ¬ w >= m := Nat.not_le_of_gt hw
            let x2 := g.arcNbr[x]!
            let u2 := g.arcNbr[u]!
            let w2 := g.arcNbr[w]!
            let pts : List Nat := [x, x2, u, u2, w, w2]
            have hdisj : (pts.eraseDups.length != pts.length) = false := by
              cases hbad : (pts.eraseDups.length != pts.length) with
              | true =>
                  exfalso
                  have hneq : pts.eraseDups.length ≠ pts.length := by
                    intro hlen
                    have hfalse : (pts.eraseDups.length != pts.length) = false := by simp [hlen]
                    have ht : false = true := by
                      simpa [hfalse] using hbad
                    cases ht
                  have hne6 := hneq
                  simp [pts] at hne6
                  have : False := by
                    simpa [Reidemeister.r3BraidLeft, hvg, m, hx_ge, hu_ge, hw_ge, x2, u2, w2, pts, hne6,
                      Bind.bind, Except.bind, Pure.pure, Except.pure] using h
                  exact this
              | false =>
                  rfl
            let baseA := m
            let baseB := m + 4
            let baseC := m + 8
            let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
            let nbr :=
              setPair!
                (setPair!
                  (setPair!
                    (setPair!
                      (setPair!
                        (setPair!
                          (setPair!
                            (setPair!
                              (setPair! nbr0 x (baseA + 0)) u (baseA + 1))
                            w (baseB + 1))
                          x2 (baseB + 3))
                        w2 (baseC + 2))
                      u2 (baseC + 3))
                    (baseA + 2) (baseC + 0))
                  (baseA + 3) (baseB + 0))
                (baseB + 2) (baseC + 1)
            let gOut : PDGraph := { freeLoops := g.freeLoops, n := g.n + 3, arcNbr := nbr }
            have hlenEq : pts.eraseDups.length = pts.length := by
              classical
              by_contra hne
              have htrue : (pts.eraseDups.length != pts.length) = true := by
                simp [hne]
              have : false = true := by simpa [hdisj] using htrue
              cases this
            have hlenEq6 := hlenEq
            simp [pts] at hlenEq6
            have h' := h
            simp [Reidemeister.r3BraidLeft, hvg, m, hx_ge, hu_ge, hw_ge, x2, u2, w2, pts, hlenEq6,
              baseA, baseB, baseC, nbr0, nbr, gOut, Bind.bind, Except.bind, Pure.pure, Except.pure] at h'
            cases hvgOut : PDGraph.validate gOut with
            | error e =>
                exfalso
                have hvgOut' := hvgOut
                simp [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] at hvgOut'
                simpa [hvgOut'] using h'
            | ok hvOut =>
                cases hvOut
                have hvgOut' := hvgOut
                simp [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] at hvgOut'
                have hOk := h'
                simp [hvgOut'] at hOk
                have hOk' : (Except.ok gOut : Except String PDGraph) = .ok gL := by
                  simpa [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] using hOk
                have hg0 : gOut = gL := by
                  injection hOk' with hg0
                have hg : gL = gOut := hg0.symm
                simp [hg, gOut]
          · have hw_ge : w >= m := Nat.le_of_not_gt hw
            exfalso
            have hcontra := h
            simp [Reidemeister.r3BraidLeft, hvg, m, hw_ge] at hcontra
            cases hcontra
        · have hu_ge : u >= m := Nat.le_of_not_gt hu
          exfalso
          have hcontra := h
          simp [Reidemeister.r3BraidLeft, hvg, m, hu_ge] at hcontra
          cases hcontra
      · have hx_ge : x >= m := Nat.le_of_not_gt hx
        exfalso
        have hcontra := h
        simp [Reidemeister.r3BraidLeft, hvg, m, hx_ge] at hcontra
        cases hcontra

private theorem r3BraidLeft_eq_gOut
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    let x2 := g.arcNbr[x]!
    let u2 := g.arcNbr[u]!
    let w2 := g.arcNbr[w]!
    let baseA := m
    let baseB := m + 4
    let baseC := m + 8
    let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
    let nbr :=
      setPair!
        (setPair!
          (setPair!
            (setPair!
              (setPair!
                (setPair!
                  (setPair!
                    (setPair!
                      (setPair! nbr0 x (baseA + 0)) u (baseA + 1))
                    w (baseB + 1))
                  x2 (baseB + 3))
                w2 (baseC + 2))
              u2 (baseC + 3))
            (baseA + 2) (baseC + 0))
          (baseA + 3) (baseB + 0))
        (baseB + 2) (baseC + 1)
    let gOut : PDGraph := { freeLoops := g.freeLoops, n := g.n + 3, arcNbr := nbr }
    gL = gOut := by
  classical
  cases hvg : PDGraph.validate g with
  | error e =>
      have hEq : (Except.error e : Except String PDGraph) = .ok gL := by
        simpa [Reidemeister.r3BraidLeft, hvg, Bind.bind, Except.bind] using h
      cases hEq
  | ok hv =>
      cases hv
      let m := g.numHalfEdges
      by_cases hx : x < m
      · by_cases hu : u < m
        · by_cases hw : w < m
          · have hx_ge : ¬ x >= m := Nat.not_le_of_gt hx
            have hu_ge : ¬ u >= m := Nat.not_le_of_gt hu
            have hw_ge : ¬ w >= m := Nat.not_le_of_gt hw
            let x2 := g.arcNbr[x]!
            let u2 := g.arcNbr[u]!
            let w2 := g.arcNbr[w]!
            let pts : List Nat := [x, x2, u, u2, w, w2]
            have hdisj : (pts.eraseDups.length != pts.length) = false := by
              cases hbad : (pts.eraseDups.length != pts.length) with
              | true =>
                  exfalso
                  have hneq : pts.eraseDups.length ≠ pts.length := by
                    intro hlen
                    have hfalse : (pts.eraseDups.length != pts.length) = false := by simp [hlen]
                    have ht : false = true := by
                      simpa [hfalse] using hbad
                    cases ht
                  have hne6 := hneq
                  simp [pts] at hne6
                  have : False := by
                    simpa [Reidemeister.r3BraidLeft, hvg, m, hx_ge, hu_ge, hw_ge, x2, u2, w2, pts, hne6,
                      Bind.bind, Except.bind, Pure.pure, Except.pure] using h
                  exact this
              | false =>
                  rfl
            let baseA := m
            let baseB := m + 4
            let baseC := m + 8
            let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
            let nbr :=
              setPair!
                (setPair!
                  (setPair!
                    (setPair!
                      (setPair!
                        (setPair!
                          (setPair!
                            (setPair!
                              (setPair! nbr0 x (baseA + 0)) u (baseA + 1))
                            w (baseB + 1))
                          x2 (baseB + 3))
                        w2 (baseC + 2))
                      u2 (baseC + 3))
                    (baseA + 2) (baseC + 0))
                  (baseA + 3) (baseB + 0))
                (baseB + 2) (baseC + 1)
            let gOut : PDGraph := { freeLoops := g.freeLoops, n := g.n + 3, arcNbr := nbr }
            have hlenEq : pts.eraseDups.length = pts.length := by
              classical
              by_contra hne
              have htrue : (pts.eraseDups.length != pts.length) = true := by
                simp [hne]
              have : false = true := by simpa [hdisj] using htrue
              cases this
            have hlenEq6 := hlenEq
            simp [pts] at hlenEq6
            have h' := h
            simp [Reidemeister.r3BraidLeft, hvg, m, hx_ge, hu_ge, hw_ge, x2, u2, w2, pts, hlenEq6,
              baseA, baseB, baseC, nbr0, nbr, gOut, Bind.bind, Except.bind, Pure.pure, Except.pure] at h'
            cases hvgOut : PDGraph.validate gOut with
            | error e =>
                exfalso
                have hvgOut' := hvgOut
                simp [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] at hvgOut'
                simpa [hvgOut'] using h'
            | ok hvOut =>
                cases hvOut
                have hvgOut' := hvgOut
                simp [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] at hvgOut'
                have hOk := h'
                simp [hvgOut'] at hOk
                have hOk' : (Except.ok gOut : Except String PDGraph) = .ok gL := by
                  simpa [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] using hOk
                have hg0 : gOut = gL := by
                  injection hOk' with hg0
                exact hg0.symm
          · have hw_ge : w >= m := Nat.le_of_not_gt hw
            exfalso
            have hcontra := h
            simp [Reidemeister.r3BraidLeft, hvg, m, hw_ge] at hcontra
            cases hcontra
        · have hu_ge : u >= m := Nat.le_of_not_gt hu
          exfalso
          have hcontra := h
          simp [Reidemeister.r3BraidLeft, hvg, m, hu_ge] at hcontra
          cases hcontra
      · have hx_ge : x >= m := Nat.le_of_not_gt hx
        exfalso
        have hcontra := h
        simp [Reidemeister.r3BraidLeft, hvg, m, hx_ge] at hcontra
        cases hcontra

theorem r3BraidRight_n_eq
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    gR.n = g.n + 3 := by
  classical
  cases hvg : PDGraph.validate g with
  | error e =>
      have hEq : (Except.error e : Except String PDGraph) = .ok gR := by
        simpa [Reidemeister.r3BraidRight, hvg, Bind.bind, Except.bind] using h
      cases hEq
  | ok hv =>
      cases hv
      let m := g.numHalfEdges
      by_cases hx : x < m
      · by_cases hu : u < m
        · by_cases hw : w < m
          · have hx_ge : ¬ x >= m := Nat.not_le_of_gt hx
            have hu_ge : ¬ u >= m := Nat.not_le_of_gt hu
            have hw_ge : ¬ w >= m := Nat.not_le_of_gt hw
            let x2 := g.arcNbr[x]!
            let u2 := g.arcNbr[u]!
            let w2 := g.arcNbr[w]!
            let pts : List Nat := [x, x2, u, u2, w, w2]
            have hdisj : (pts.eraseDups.length != pts.length) = false := by
              cases hbad : (pts.eraseDups.length != pts.length) with
              | true =>
                  exfalso
                  have hneq : pts.eraseDups.length ≠ pts.length := by
                    intro hlen
                    have hfalse : (pts.eraseDups.length != pts.length) = false := by simp [hlen]
                    have ht : false = true := by
                      simpa [hfalse] using hbad
                    cases ht
                  have hne6 := hneq
                  simp [pts] at hne6
                  have : False := by
                    simpa [Reidemeister.r3BraidRight, hvg, m, hx_ge, hu_ge, hw_ge, x2, u2, w2, pts, hne6,
                      Bind.bind, Except.bind, Pure.pure, Except.pure] using h
                  exact this
              | false =>
                  rfl
            let baseA := m
            let baseB := m + 4
            let baseC := m + 8
            let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
            let nbr :=
              setPair!
                (setPair!
                  (setPair!
                    (setPair!
                      (setPair!
                        (setPair!
                          (setPair!
                            (setPair!
                              (setPair! nbr0 u (baseA + 0)) w (baseA + 1))
                            x (baseB + 0))
                          w2 (baseB + 2))
                        u2 (baseC + 2))
                      x2 (baseC + 3))
                    (baseA + 2) (baseB + 1))
                  (baseB + 3) (baseC + 0))
                (baseA + 3) (baseC + 1)
            let gOut : PDGraph := { freeLoops := g.freeLoops, n := g.n + 3, arcNbr := nbr }
            have hlenEq : pts.eraseDups.length = pts.length := by
              classical
              by_contra hne
              have htrue : (pts.eraseDups.length != pts.length) = true := by
                simp [hne]
              have : false = true := by simpa [hdisj] using htrue
              cases this
            have hlenEq6 := hlenEq
            simp [pts] at hlenEq6
            have h' := h
            simp [Reidemeister.r3BraidRight, hvg, m, hx_ge, hu_ge, hw_ge, x2, u2, w2, pts, hlenEq6,
              baseA, baseB, baseC, nbr0, nbr, gOut, Bind.bind, Except.bind, Pure.pure, Except.pure] at h'
            cases hvgOut : PDGraph.validate gOut with
            | error e =>
                exfalso
                have hvgOut' := hvgOut
                simp [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] at hvgOut'
                simpa [hvgOut'] using h'
            | ok hvOut =>
                cases hvOut
                have hvgOut' := hvgOut
                simp [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] at hvgOut'
                have hOk := h'
                simp [hvgOut'] at hOk
                have hOk' : (Except.ok gOut : Except String PDGraph) = .ok gR := by
                  simpa [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] using hOk
                have hg0 : gOut = gR := by
                  injection hOk' with hg0
                have hg : gR = gOut := hg0.symm
                simp [hg, gOut]
          · have hw_ge : w >= m := Nat.le_of_not_gt hw
            exfalso
            have hcontra := h
            simp [Reidemeister.r3BraidRight, hvg, m, hw_ge] at hcontra
            cases hcontra
        · have hu_ge : u >= m := Nat.le_of_not_gt hu
          exfalso
          have hcontra := h
          simp [Reidemeister.r3BraidRight, hvg, m, hu_ge] at hcontra
          cases hcontra
      · have hx_ge : x >= m := Nat.le_of_not_gt hx
        exfalso
        have hcontra := h
        simp [Reidemeister.r3BraidRight, hvg, m, hx_ge] at hcontra
        cases hcontra

private theorem r3BraidRight_eq_gOut
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    let x2 := g.arcNbr[x]!
    let u2 := g.arcNbr[u]!
    let w2 := g.arcNbr[w]!
    let baseA := m
    let baseB := m + 4
    let baseC := m + 8
    let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
    let nbr :=
      setPair!
        (setPair!
          (setPair!
            (setPair!
              (setPair!
                (setPair!
                  (setPair!
                    (setPair!
                      (setPair! nbr0 u (baseA + 0)) w (baseA + 1))
                    x (baseB + 0))
                  w2 (baseB + 2))
                u2 (baseC + 2))
              x2 (baseC + 3))
            (baseA + 2) (baseB + 1))
          (baseB + 3) (baseC + 0))
        (baseA + 3) (baseC + 1)
    let gOut : PDGraph := { freeLoops := g.freeLoops, n := g.n + 3, arcNbr := nbr }
    gR = gOut := by
  classical
  cases hvg : PDGraph.validate g with
  | error e =>
      have hEq : (Except.error e : Except String PDGraph) = .ok gR := by
        simpa [Reidemeister.r3BraidRight, hvg, Bind.bind, Except.bind] using h
      cases hEq
  | ok hv =>
      cases hv
      let m := g.numHalfEdges
      by_cases hx : x < m
      · by_cases hu : u < m
        · by_cases hw : w < m
          · have hx_ge : ¬ x >= m := Nat.not_le_of_gt hx
            have hu_ge : ¬ u >= m := Nat.not_le_of_gt hu
            have hw_ge : ¬ w >= m := Nat.not_le_of_gt hw
            let x2 := g.arcNbr[x]!
            let u2 := g.arcNbr[u]!
            let w2 := g.arcNbr[w]!
            let pts : List Nat := [x, x2, u, u2, w, w2]
            have hdisj : (pts.eraseDups.length != pts.length) = false := by
              cases hbad : (pts.eraseDups.length != pts.length) with
              | true =>
                  exfalso
                  have hneq : pts.eraseDups.length ≠ pts.length := by
                    intro hlen
                    have hfalse : (pts.eraseDups.length != pts.length) = false := by simp [hlen]
                    have ht : false = true := by
                      simpa [hfalse] using hbad
                    cases ht
                  have hne6 := hneq
                  simp [pts] at hne6
                  have : False := by
                    simpa [Reidemeister.r3BraidRight, hvg, m, hx_ge, hu_ge, hw_ge, x2, u2, w2, pts, hne6,
                      Bind.bind, Except.bind, Pure.pure, Except.pure] using h
                  exact this
              | false =>
                  rfl
            let baseA := m
            let baseB := m + 4
            let baseC := m + 8
            let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
            let nbr :=
              setPair!
                (setPair!
                  (setPair!
                    (setPair!
                      (setPair!
                        (setPair!
                          (setPair!
                            (setPair!
                              (setPair! nbr0 u (baseA + 0)) w (baseA + 1))
                            x (baseB + 0))
                          w2 (baseB + 2))
                        u2 (baseC + 2))
                      x2 (baseC + 3))
                    (baseA + 2) (baseB + 1))
                  (baseB + 3) (baseC + 0))
                (baseA + 3) (baseC + 1)
            let gOut : PDGraph := { freeLoops := g.freeLoops, n := g.n + 3, arcNbr := nbr }
            have hlenEq : pts.eraseDups.length = pts.length := by
              classical
              by_contra hne
              have htrue : (pts.eraseDups.length != pts.length) = true := by
                simp [hne]
              have : false = true := by simpa [hdisj] using htrue
              cases this
            have hlenEq6 := hlenEq
            simp [pts] at hlenEq6
            have h' := h
            simp [Reidemeister.r3BraidRight, hvg, m, hx_ge, hu_ge, hw_ge, x2, u2, w2, pts, hlenEq6,
              baseA, baseB, baseC, nbr0, nbr, gOut, Bind.bind, Except.bind, Pure.pure, Except.pure] at h'
            cases hvgOut : PDGraph.validate gOut with
            | error e =>
                exfalso
                have hvgOut' := hvgOut
                simp [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] at hvgOut'
                simpa [hvgOut'] using h'
            | ok hvOut =>
                cases hvOut
                have hvgOut' := hvgOut
                simp [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] at hvgOut'
                have hOk := h'
                simp [hvgOut'] at hOk
                have hOk' : (Except.ok gOut : Except String PDGraph) = .ok gR := by
                  simpa [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] using hOk
                have hg0 : gOut = gR := by
                  injection hOk' with hg0
                exact hg0.symm
          · have hw_ge : w >= m := Nat.le_of_not_gt hw
            exfalso
            have hcontra := h
            simp [Reidemeister.r3BraidRight, hvg, m, hw_ge] at hcontra
            cases hcontra
        · have hu_ge : u >= m := Nat.le_of_not_gt hu
          exfalso
          have hcontra := h
          simp [Reidemeister.r3BraidRight, hvg, m, hu_ge] at hcontra
          cases hcontra
      · have hx_ge : x >= m := Nat.le_of_not_gt hx
        exfalso
        have hcontra := h
        simp [Reidemeister.r3BraidRight, hvg, m, hx_ge] at hcontra
        cases hcontra

theorem r3BraidLeft_valid
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    PDGraph.Valid gL := by
  classical
  cases hvg : PDGraph.validate g with
  | error e =>
      have hEq : (Except.error e : Except String PDGraph) = .ok gL := by
        simpa [Reidemeister.r3BraidLeft, hvg, Bind.bind, Except.bind] using h
      cases hEq
  | ok hv =>
      cases hv
      let m := g.numHalfEdges
      by_cases hx : x < m
      · by_cases hu : u < m
        · by_cases hw : w < m
          · have hx_ge : ¬ x >= m := Nat.not_le_of_gt hx
            have hu_ge : ¬ u >= m := Nat.not_le_of_gt hu
            have hw_ge : ¬ w >= m := Nat.not_le_of_gt hw
            let x2 := g.arcNbr[x]!
            let u2 := g.arcNbr[u]!
            let w2 := g.arcNbr[w]!
            let pts : List Nat := [x, x2, u, u2, w, w2]
            have hdisj : (pts.eraseDups.length != pts.length) = false := by
              cases hbad : (pts.eraseDups.length != pts.length) with
              | true =>
                  exfalso
                  have hneq : pts.eraseDups.length ≠ pts.length := by
                    intro hlen
                    have hfalse : (pts.eraseDups.length != pts.length) = false := by simp [hlen]
                    have ht : false = true := by
                      simpa [hfalse] using hbad
                    cases ht
                  have hne6 := hneq
                  simp [pts] at hne6
                  have : False := by
                    simpa [Reidemeister.r3BraidLeft, hvg, m, hx_ge, hu_ge, hw_ge, x2, u2, w2, pts, hne6,
                      Bind.bind, Except.bind, Pure.pure, Except.pure] using h
                  exact this
              | false =>
                  rfl
            let baseA := m
            let baseB := m + 4
            let baseC := m + 8
            let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
            let nbr :=
              setPair!
                (setPair!
                  (setPair!
                    (setPair!
                      (setPair!
                        (setPair!
                          (setPair!
                            (setPair!
                              (setPair! nbr0 x (baseA + 0)) u (baseA + 1))
                            w (baseB + 1))
                          x2 (baseB + 3))
                        w2 (baseC + 2))
                      u2 (baseC + 3))
                    (baseA + 2) (baseC + 0))
                  (baseA + 3) (baseB + 0))
                (baseB + 2) (baseC + 1)
            let gOut : PDGraph := { freeLoops := g.freeLoops, n := g.n + 3, arcNbr := nbr }
            have hlenEq : pts.eraseDups.length = pts.length := by
              classical
              by_contra hne
              have htrue : (pts.eraseDups.length != pts.length) = true := by
                simp [hne]
              have : false = true := by simpa [hdisj] using htrue
              cases this
            have hlenEq6 := hlenEq
            simp [pts] at hlenEq6
            have h' := h
            simp [Reidemeister.r3BraidLeft, hvg, m, hx_ge, hu_ge, hw_ge, x2, u2, w2, pts, hlenEq6,
              baseA, baseB, baseC, nbr0, nbr, gOut, Bind.bind, Except.bind, Pure.pure, Except.pure] at h'
            cases hvgOut : PDGraph.validate gOut with
            | error e =>
                exfalso
                have hvgOut' := hvgOut
                simp [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] at hvgOut'
                simpa [hvgOut'] using h'
            | ok hvOut =>
                cases hvOut
                have hvgOut' := hvgOut
                simp [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] at hvgOut'
                have hOk := h'
                simp [hvgOut'] at hOk
                have hOk' : (Except.ok gOut : Except String PDGraph) = .ok gL := by
                  simpa [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] using hOk
                have hg0 : gOut = gL := by
                  injection hOk' with hg0
                have hg : gL = gOut := hg0.symm
                have hValidOut : PDGraph.Valid gOut :=
                  PDGraph.valid_of_validate_eq_ok (g := gOut) hvgOut
                simpa [hg] using hValidOut
          · have hw_ge : w >= m := Nat.le_of_not_gt hw
            exfalso
            have hcontra := h
            simp [Reidemeister.r3BraidLeft, hvg, m, hw_ge] at hcontra
            cases hcontra
        · have hu_ge : u >= m := Nat.le_of_not_gt hu
          exfalso
          have hcontra := h
          simp [Reidemeister.r3BraidLeft, hvg, m, hu_ge] at hcontra
          cases hcontra
      · have hx_ge : x >= m := Nat.le_of_not_gt hx
        exfalso
        have hcontra := h
        simp [Reidemeister.r3BraidLeft, hvg, m, hx_ge] at hcontra
        cases hcontra

theorem r3BraidRight_valid
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    PDGraph.Valid gR := by
  classical
  cases hvg : PDGraph.validate g with
  | error e =>
      have hEq : (Except.error e : Except String PDGraph) = .ok gR := by
        simpa [Reidemeister.r3BraidRight, hvg, Bind.bind, Except.bind] using h
      cases hEq
  | ok hv =>
      cases hv
      let m := g.numHalfEdges
      by_cases hx : x < m
      · by_cases hu : u < m
        · by_cases hw : w < m
          · have hx_ge : ¬ x >= m := Nat.not_le_of_gt hx
            have hu_ge : ¬ u >= m := Nat.not_le_of_gt hu
            have hw_ge : ¬ w >= m := Nat.not_le_of_gt hw
            let x2 := g.arcNbr[x]!
            let u2 := g.arcNbr[u]!
            let w2 := g.arcNbr[w]!
            let pts : List Nat := [x, x2, u, u2, w, w2]
            have hdisj : (pts.eraseDups.length != pts.length) = false := by
              cases hbad : (pts.eraseDups.length != pts.length) with
              | true =>
                  exfalso
                  have hneq : pts.eraseDups.length ≠ pts.length := by
                    intro hlen
                    have hfalse : (pts.eraseDups.length != pts.length) = false := by simp [hlen]
                    have ht : false = true := by
                      simpa [hfalse] using hbad
                    cases ht
                  have hne6 := hneq
                  simp [pts] at hne6
                  have : False := by
                    simpa [Reidemeister.r3BraidRight, hvg, m, hx_ge, hu_ge, hw_ge, x2, u2, w2, pts, hne6,
                      Bind.bind, Except.bind, Pure.pure, Except.pure] using h
                  exact this
              | false =>
                  rfl
            let baseA := m
            let baseB := m + 4
            let baseC := m + 8
            let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
            let nbr :=
              setPair!
                (setPair!
                  (setPair!
                    (setPair!
                      (setPair!
                        (setPair!
                          (setPair!
                            (setPair!
                              (setPair! nbr0 u (baseA + 0)) w (baseA + 1))
                            x (baseB + 0))
                          w2 (baseB + 2))
                        u2 (baseC + 2))
                      x2 (baseC + 3))
                    (baseA + 2) (baseB + 1))
                  (baseB + 3) (baseC + 0))
                (baseA + 3) (baseC + 1)
            let gOut : PDGraph := { freeLoops := g.freeLoops, n := g.n + 3, arcNbr := nbr }
            have hlenEq : pts.eraseDups.length = pts.length := by
              classical
              by_contra hne
              have htrue : (pts.eraseDups.length != pts.length) = true := by
                simp [hne]
              have : false = true := by simpa [hdisj] using htrue
              cases this
            have hlenEq6 := hlenEq
            simp [pts] at hlenEq6
            have h' := h
            simp [Reidemeister.r3BraidRight, hvg, m, hx_ge, hu_ge, hw_ge, x2, u2, w2, pts, hlenEq6,
              baseA, baseB, baseC, nbr0, nbr, gOut, Bind.bind, Except.bind, Pure.pure, Except.pure] at h'
            cases hvgOut : PDGraph.validate gOut with
            | error e =>
                exfalso
                have hvgOut' := hvgOut
                simp [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] at hvgOut'
                simpa [hvgOut'] using h'
            | ok hvOut =>
                cases hvOut
                have hvgOut' := hvgOut
                simp [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] at hvgOut'
                have hOk := h'
                simp [hvgOut'] at hOk
                have hOk' : (Except.ok gOut : Except String PDGraph) = .ok gR := by
                  simpa [gOut, nbr, nbr0, baseA, baseB, baseC, m, x2, u2, w2] using hOk
                have hg0 : gOut = gR := by
                  injection hOk' with hg0
                have hg : gR = gOut := hg0.symm
                have hValidOut : PDGraph.Valid gOut :=
                  PDGraph.valid_of_validate_eq_ok (g := gOut) hvgOut
                simpa [hg] using hValidOut
          · have hw_ge : w >= m := Nat.le_of_not_gt hw
            exfalso
            have hcontra := h
            simp [Reidemeister.r3BraidRight, hvg, m, hw_ge] at hcontra
            cases hcontra
        · have hu_ge : u >= m := Nat.le_of_not_gt hu
          exfalso
          have hcontra := h
          simp [Reidemeister.r3BraidRight, hvg, m, hu_ge] at hcontra
          cases hcontra
      · have hx_ge : x >= m := Nat.le_of_not_gt hx
        exfalso
        have hcontra := h
        simp [Reidemeister.r3BraidRight, hvg, m, hx_ge] at hcontra
        cases hcontra

/-!
## First-step evaluator shape facts for the braid gadgets

To unfold `bracketGraphMLAux` deterministically on the braid gadgets, we show that the evaluator
does **not** take the Reidemeister-I or Reidemeister-II short-circuit branches at the end of the
gadget (the last crossing is not a curl; the last two crossings are not an R2 pair).
-/

private theorem validate_of_r3BraidLeft_ok
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    PDGraph.validate g = .ok () := by
  cases hvg : PDGraph.validate g with
  | error e =>
      have h' : Reidemeister.r3BraidLeft g x u w = .error e := by
        simp [Reidemeister.r3BraidLeft, hvg, Bind.bind, Except.bind]  -- first action is validation
      simpa [h'] using h
  | ok hv =>
      cases hv
      simpa using hvg

private theorem validate_of_r3BraidRight_ok
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    PDGraph.validate g = .ok () := by
  cases hvg : PDGraph.validate g with
  | error e =>
      have h' : Reidemeister.r3BraidRight g x u w = .error e := by
        simp [Reidemeister.r3BraidRight, hvg, Bind.bind, Except.bind]
      simpa [h'] using h
  | ok hv =>
      cases hv
      simpa using hvg

private theorem lt_numHalfEdges_of_r3BraidLeft_ok
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    x < g.numHalfEdges ∧ u < g.numHalfEdges ∧ w < g.numHalfEdges := by
  classical
  have hvg : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  let m := g.numHalfEdges
  by_cases hx : x < m
  · by_cases hu : u < m
    · by_cases hw : w < m
      · exact ⟨hx, hu, hw⟩
      · have hw_ge : w >= m := Nat.le_of_not_gt hw
        exfalso
        have hcontra := h
        simp [Reidemeister.r3BraidLeft, hvg, m, hw_ge] at hcontra
        cases hcontra
    · have hu_ge : u >= m := Nat.le_of_not_gt hu
      exfalso
      have hcontra := h
      simp [Reidemeister.r3BraidLeft, hvg, m, hu_ge] at hcontra
      cases hcontra
  · have hx_ge : x >= m := Nat.le_of_not_gt hx
    exfalso
    have hcontra := h
    simp [Reidemeister.r3BraidLeft, hvg, m, hx_ge] at hcontra
    cases hcontra

private theorem lt_numHalfEdges_of_r3BraidRight_ok
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    x < g.numHalfEdges ∧ u < g.numHalfEdges ∧ w < g.numHalfEdges := by
  classical
  have hvg : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  let m := g.numHalfEdges
  by_cases hx : x < m
  · by_cases hu : u < m
    · by_cases hw : w < m
      · exact ⟨hx, hu, hw⟩
      · have hw_ge : w >= m := Nat.le_of_not_gt hw
        exfalso
        have hcontra := h
        simp [Reidemeister.r3BraidRight, hvg, m, hw_ge] at hcontra
        cases hcontra
    · have hu_ge : u >= m := Nat.le_of_not_gt hu
      exfalso
      have hcontra := h
      simp [Reidemeister.r3BraidRight, hvg, m, hu_ge] at hcontra
      cases hcontra
  · have hx_ge : x >= m := Nat.le_of_not_gt hx
    exfalso
    have hcontra := h
    simp [Reidemeister.r3BraidRight, hvg, m, hx_ge] at hcontra
    cases hcontra

private lemma four_mul_add_three_sub_four (n : Nat) :
    4 * (n + 3) - 4 = 4 * n + 8 := by
  have h : (4 : Nat) ≤ 12 := by decide
  calc
    4 * (n + 3) - 4 = (4 * n + 12) - 4 := by
      simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = 4 * n + (12 - 4) := by
      simpa using (Nat.add_sub_assoc (n := 4 * n) (m := 12) (k := 4) h)
    _ = 4 * n + 8 := by simp

private theorem r1RemoveLast_pos_err_of_r3BraidLeft_ok
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    Reidemeister.r1RemoveLast gL .pos = .error "r1RemoveLast: internal loop arc mismatch" := by
  classical
  have hg : gL = r3BraidLeftGraph g x u w := by
    simpa [r3BraidLeftGraph, r3BraidLeftNbr] using
      (r3BraidLeft_eq_gOut (g := g) (gL := gL) (x := x) (u := u) (w := w) h)
  subst hg
  have hvg : PDGraph.validate g = .ok () := by
    cases hvg : PDGraph.validate g with
    | error e =>
        have h' : Reidemeister.r3BraidLeft g x u w = .error e := by
          simp [Reidemeister.r3BraidLeft, hvg, Bind.bind, Except.bind]
        simpa [h'] using h
    | ok hv =>
        cases hv
        simpa using hvg
  have hsizeG : g.arcNbr.size = g.numHalfEdges :=
    PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg
  have hValid : PDGraph.Valid (r3BraidLeftGraph g x u w) := by
    simpa using (r3BraidLeft_valid (g := g) (gL := r3BraidLeftGraph g x u w) (x := x) (u := u) (w := w) h)
  have hvgL : PDGraph.validate (r3BraidLeftGraph g x u w) = .ok () :=
    PDGraph.validate_eq_ok_of_valid hValid
  have hn0 : ¬(r3BraidLeftGraph g x u w).n = 0 := by
    -- `n` is increased by `3` by the constructor.
    simp [r3BraidLeftGraph]
  -- The `.pos` curl check expects `(base+0) ↔ (base+1)`, but in the braid gadget
  -- `baseC+0` is wired to `baseA+2`.
  let m : Nat := g.numHalfEdges
  let baseL : Nat := (r3BraidLeftGraph g x u w).numHalfEdges - 4
  have hbaseL : baseL = m + 8 := by
    dsimp [baseL, r3BraidLeftGraph, m, PDGraph.numHalfEdges]
    simpa using four_mul_add_three_sub_four g.n
  -- Compute the neighbor at `baseC+0 = m+8` by reading only the relevant `setPair!` updates.
  have h0m : (r3BraidLeftGraph g x u w).arcNbr[m + 8]! = m + 2 := by
    -- Expand the braid neighbor array and strip off the updates that don't touch `m+8`.
    let x2 := g.arcNbr[x]!
    let u2 := g.arcNbr[u]!
    let w2 := g.arcNbr[w]!
    let baseA := m
    let baseB := m + 4
    let baseC := m + 8
    let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
    let nbr6 :=
      setPair!
        (setPair!
          (setPair!
            (setPair!
              (setPair!
                (setPair! nbr0 x (baseA + 0)) u (baseA + 1))
              w (baseB + 1))
            x2 (baseB + 3))
          w2 (baseC + 2))
        u2 (baseC + 3)
    let nbr7 := setPair! nbr6 (baseA + 2) (baseC + 0)
    let nbr8 := setPair! nbr7 (baseA + 3) (baseB + 0)
    let nbr := setPair! nbr8 (baseB + 2) (baseC + 1)
    have hm : g.numHalfEdges = m := by rfl
    have hsizeGm : g.arcNbr.size = m := by simpa [hm] using hsizeG
    have hnbr0_size : nbr0.size = m + 12 := by
      -- `g.arcNbr.size = m` from validation.
      simp [nbr0, hsizeGm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    have hi7 : baseA + 2 < nbr6.size := by
      have : m + 2 < m + 12 := Nat.add_lt_add_left (by decide : (2 : Nat) < 12) m
      simpa [nbr6, baseA, baseB, baseC, setPair!, Array.set!,
        Array.size_setIfInBounds, hnbr0_size] using this
    have hj7 : baseC + 0 < nbr6.size := by
      have : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
      simpa [nbr6, baseA, baseB, baseC, setPair!, Array.set!,
        Array.size_setIfInBounds, hnbr0_size] using this
    have hk8 : baseC + 0 < nbr7.size := by
      have : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
      simpa [nbr7, nbr6, baseA, baseB, baseC, setPair!, Array.set!,
        Array.size_setIfInBounds, hnbr0_size] using this
    have hk9 : baseC + 0 < nbr8.size := by
      have : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
      simpa [nbr8, nbr7, nbr6, baseA, baseB, baseC, setPair!, Array.set!,
        Array.size_setIfInBounds, hnbr0_size] using this
    have hi8 : baseA + 3 < nbr7.size := by
      have : m + 3 < m + 12 := Nat.add_lt_add_left (by decide : (3 : Nat) < 12) m
      simpa [nbr7, nbr6, baseA, baseB, baseC, setPair!, Array.set!,
        Array.size_setIfInBounds, hnbr0_size] using this
    have hj8 : baseB + 0 < nbr7.size := by
      have : m + 4 < m + 12 := Nat.add_lt_add_left (by decide : (4 : Nat) < 12) m
      simpa [nbr7, nbr6, baseA, baseB, baseC, setPair!, Array.set!,
        Array.size_setIfInBounds, hnbr0_size] using this
    have hi9 : baseB + 2 < nbr8.size := by
      have : m + 6 < m + 12 := Nat.add_lt_add_left (by decide : (6 : Nat) < 12) m
      simpa [nbr8, nbr7, nbr6, baseA, baseB, baseC, setPair!, Array.set!,
        Array.size_setIfInBounds, hnbr0_size] using this
    have hj9 : baseC + 1 < nbr8.size := by
      have : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
      simpa [nbr8, nbr7, nbr6, baseA, baseB, baseC, setPair!, Array.set!,
        Array.size_setIfInBounds, hnbr0_size] using this
    have h78 : nbr7[baseC + 0]! = baseA + 2 := by
      simpa [nbr7] using (setPair!_getBang_right nbr6 (baseA + 2) (baseC + 0) hi7 hj7)
    have h8ne : (setPair! nbr7 (baseA + 3) (baseB + 0))[baseC + 0]! = nbr7[baseC + 0]! := by
      have hki : baseC + 0 ≠ baseA + 3 := by
        have : m + 3 < m + 8 := Nat.add_lt_add_left (by decide : (3 : Nat) < 8) m
        exact Nat.ne_of_gt (by simpa [baseA, baseC, Nat.add_assoc] using this)
      have hkj : baseC + 0 ≠ baseB + 0 := by
        have : m + 4 < m + 8 := Nat.add_lt_add_left (by decide : (4 : Nat) < 8) m
        exact Nat.ne_of_gt (by simpa [baseB, baseC, Nat.add_assoc] using this)
      simpa using (setPair!_getBang_ne nbr7 (baseA + 3) (baseB + 0) (baseC + 0) hi8 hj8 hk8 hki hkj)
    have h89 : (setPair! nbr8 (baseB + 2) (baseC + 1))[baseC + 0]! = nbr8[baseC + 0]! := by
      have hki : baseC + 0 ≠ baseB + 2 := by
        have : m + 6 < m + 8 := Nat.add_lt_add_left (by decide : (6 : Nat) < 8) m
        exact Nat.ne_of_gt (by simpa [baseB, baseC, Nat.add_assoc] using this)
      have hkj : baseC + 0 ≠ baseC + 1 := by
        have : baseC + 0 < baseC + 1 := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.lt_succ_self baseC
        exact Nat.ne_of_lt this
      simpa using (setPair!_getBang_ne nbr8 (baseB + 2) (baseC + 1) (baseC + 0) hi9 hj9 hk9 hki hkj)
    have hFinal : nbr[baseC + 0]! = baseA + 2 := by
      -- `nbr8` is the `setPair!` result at the previous step.
      have h8 : nbr8[baseC + 0]! = nbr7[baseC + 0]! := by
        -- `h8ne` computes the updated array at `baseC+0`.
        simpa [nbr8] using h8ne
      have h9 : nbr[baseC + 0]! = nbr8[baseC + 0]! := by
        simpa [nbr] using h89
      -- Combine.
      calc
        nbr[baseC + 0]! = nbr8[baseC + 0]! := h9
        _ = nbr7[baseC + 0]! := h8
        _ = baseA + 2 := h78
    have hnbr : r3BraidLeftNbr g x u w = nbr := by rfl
    -- Conclude.
    simpa [r3BraidLeftGraph, hnbr, baseC, baseA] using hFinal
  have h0 : (r3BraidLeftGraph g x u w).arcNbr[baseL]! = m + 2 := by
    simpa [hbaseL] using h0m
  have hne : (r3BraidLeftGraph g x u w).arcNbr[baseL]! ≠ baseL + 1 := by
    intro hEq
    have hbase1 : baseL + 1 = m + 9 := by
      -- `baseL = m+8`.
      calc
        baseL + 1 = (m + 8) + 1 := by simpa [hbaseL]
        _ = m + (8 + 1) := by simp [Nat.add_assoc]
        _ = m + 9 := by simp
    have hEq' : (m + 2 : Nat) = m + 9 := by
      simpa [h0, hbase1] using hEq
    exact (Nat.ne_of_lt (Nat.add_lt_add_left (by decide : (2 : Nat) < 9) m)) hEq'
  -- Reduce `r1RemoveLast` to the internal-loop check.
  -- `simp` turns the final `if` into the `¬mismatch` branch; discharge it by contradiction.
  simp [Reidemeister.r1RemoveLast, hvgL, hn0, m, baseL, hbaseL]
  intro hIntA hIntB
  have hbase0 : g.numHalfEdges + 8 = baseL := by
    simpa [m] using hbaseL.symm
  have hIntA' : (r3BraidLeftGraph g x u w).arcNbr[baseL]! = baseL + 1 := by
    simpa [hbase0] using hIntA
  cases (hne hIntA')

private theorem r1RemoveLast_neg_err_of_r3BraidLeft_ok
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    Reidemeister.r1RemoveLast gL .neg = .error "r1RemoveLast: internal loop arc mismatch" := by
  classical
  have hg : gL = r3BraidLeftGraph g x u w := by
    simpa [r3BraidLeftGraph, r3BraidLeftNbr] using
      (r3BraidLeft_eq_gOut (g := g) (gL := gL) (x := x) (u := u) (w := w) h)
  subst hg
  have hvg : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := r3BraidLeftGraph g x u w) (x := x) (u := u) (w := w) h
  have hgValid : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok (g := g) hvg
  have hsizeG : g.arcNbr.size = g.numHalfEdges :=
    PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg
  have hValid : PDGraph.Valid (r3BraidLeftGraph g x u w) := by
    simpa using (r3BraidLeft_valid (g := g) (gL := r3BraidLeftGraph g x u w) (x := x) (u := u) (w := w) h)
  have hvgL : PDGraph.validate (r3BraidLeftGraph g x u w) = .ok () :=
    PDGraph.validate_eq_ok_of_valid hValid
  have hn0 : (r3BraidLeftGraph g x u w).n ≠ 0 := by
    simp [r3BraidLeftGraph]
  have hxuwh : x < g.numHalfEdges ∧ u < g.numHalfEdges ∧ w < g.numHalfEdges :=
    lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := r3BraidLeftGraph g x u w) (x := x) (u := u) (w := w) h
  let m : Nat := g.numHalfEdges
  let u2 : Nat := g.arcNbr[u]!
  let w2 : Nat := g.arcNbr[w]!
  have hu2 : u2 < m := by
    have hu : u < m := hxuwh.2.1
    simpa [m, u2] using (PDGraph.Valid.get_lt hgValid (i := u) (hi := hu))
  have hw2 : w2 < m := by
    have hw : w < m := hxuwh.2.2
    simpa [m, w2] using (PDGraph.Valid.get_lt hgValid (i := w) (hi := hw))
  let baseL : Nat := (r3BraidLeftGraph g x u w).numHalfEdges - 4
  have hbaseL : baseL = m + 8 := by
    dsimp [baseL, r3BraidLeftGraph, m, PDGraph.numHalfEdges]
    simpa using four_mul_add_three_sub_four g.n
  -- Compute `arcNbr[baseC+2] = w2`; this makes the neg-curl internal loop check fail.
  have hC2 : (r3BraidLeftGraph g x u w).arcNbr[m + 10]! = w2 := by
    -- Expand the braid neighbor array and track only the updates that could affect `baseC+2`.
    let x2 := g.arcNbr[x]!
    let baseA := m
    let baseB := m + 4
    let baseC := m + 8
    let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
    let nbr1 := setPair! nbr0 x (baseA + 0)
    let nbr2 := setPair! nbr1 u (baseA + 1)
    let nbr3 := setPair! nbr2 w (baseB + 1)
    let nbr4 := setPair! nbr3 x2 (baseB + 3)
    let nbr5 := setPair! nbr4 w2 (baseC + 2)
    let nbr6 := setPair! nbr5 u2 (baseC + 3)
    let nbr7 := setPair! nbr6 (baseA + 2) (baseC + 0)
    let nbr8 := setPair! nbr7 (baseA + 3) (baseB + 0)
    let nbr := setPair! nbr8 (baseB + 2) (baseC + 1)
    have hsizeGm : g.arcNbr.size = m := by simpa [m] using hsizeG
    have hnbr0_size : nbr0.size = m + 12 := by
      simp [nbr0, hsizeGm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    -- `setPair!` does not change array sizes; record the common size once.
    have hnbr1_size : nbr1.size = m + 12 := by
      calc
        nbr1.size = nbr0.size := by
          simp [nbr1, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr0_size
    have hnbr2_size : nbr2.size = m + 12 := by
      calc
        nbr2.size = nbr1.size := by
          simp [nbr2, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr1_size
    have hnbr3_size : nbr3.size = m + 12 := by
      calc
        nbr3.size = nbr2.size := by
          simp [nbr3, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr2_size
    have hnbr4_size : nbr4.size = m + 12 := by
      calc
        nbr4.size = nbr3.size := by
          simp [nbr4, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr3_size
    have hnbr5_size : nbr5.size = m + 12 := by
      calc
        nbr5.size = nbr4.size := by
          simp [nbr5, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr4_size
    have hnbr6_size : nbr6.size = m + 12 := by
      calc
        nbr6.size = nbr5.size := by
          simp [nbr6, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr5_size
    have hnbr7_size : nbr7.size = m + 12 := by
      calc
        nbr7.size = nbr6.size := by
          simp [nbr7, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr6_size
    have hnbr8_size : nbr8.size = m + 12 := by
      calc
        nbr8.size = nbr7.size := by
          simp [nbr8, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr7_size
    have hnbr_size : nbr.size = m + 12 := by
      calc
        nbr.size = nbr8.size := by
          simp [nbr, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr8_size
    have hk : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
    have hk4 : baseC + 2 < nbr4.size := by
      -- `baseC = m+8` so `baseC+2 = m+10`.
      have : baseC + 2 = m + 10 := by
        simp [baseC, Nat.add_assoc]
      simpa [this, hnbr4_size] using hk
    have hw2_lt_nbr4 : w2 < nbr4.size := by
      have : w2 < m + 12 := Nat.lt_of_lt_of_le hw2 (Nat.le_add_right m 12)
      simpa [hnbr4_size] using this
    have hk5 : baseC + 2 < nbr5.size := by
      have : baseC + 2 = m + 10 := by
        simp [baseC, Nat.add_assoc]
      simpa [this, hnbr5_size] using hk
    have hk6 : baseC + 2 < nbr6.size := by
      have : baseC + 2 = m + 10 := by
        simp [baseC, Nat.add_assoc]
      simpa [this, hnbr6_size] using hk
    have hk7 : baseC + 2 < nbr7.size := by
      have : baseC + 2 = m + 10 := by
        simp [baseC, Nat.add_assoc]
      simpa [this, hnbr7_size] using hk
    have hk8 : baseC + 2 < nbr8.size := by
      have : baseC + 2 = m + 10 := by
        simp [baseC, Nat.add_assoc]
      simpa [this, hnbr8_size] using hk
    have hk9 : baseC + 2 < nbr.size := by
      have : baseC + 2 = m + 10 := by
        simp [baseC, Nat.add_assoc]
      simpa [this, hnbr_size] using hk
    have h5 : nbr5[baseC + 2]! = w2 := by
      simpa [nbr5] using (setPair!_getBang_right nbr4 w2 (baseC + 2) hw2_lt_nbr4 hk4)
    have h6 : nbr6[baseC + 2]! = nbr5[baseC + 2]! := by
      have hki : baseC + 2 ≠ u2 := by
        -- `u2 < m` while `baseC+2 = m+10`.
        have hu2_lt_base : u2 < baseC + 2 := by
          have hm_le : m ≤ baseC + 2 := by
            simp [baseC, Nat.add_assoc]
          exact Nat.lt_of_lt_of_le hu2 hm_le
        exact (Nat.ne_of_lt hu2_lt_base).symm
      have hkj : baseC + 2 ≠ baseC + 3 := Nat.ne_of_lt (Nat.lt_succ_self (baseC + 2))
      have hu2_lt_nbr5 : u2 < nbr5.size := by
        have : u2 < m + 12 := Nat.lt_of_lt_of_le hu2 (Nat.le_add_right m 12)
        simpa [hnbr5_size] using this
      have hbaseC3_lt_nbr5 : baseC + 3 < nbr5.size := by
        have : m + 11 < m + 12 := Nat.add_lt_add_left (by decide : (11 : Nat) < 12) m
        have : baseC + 3 = m + 11 := by
          simp [baseC, Nat.add_assoc]
        simpa [this, hnbr5_size] using this_1
      simpa [nbr6] using (setPair!_getBang_ne nbr5 u2 (baseC + 3) (baseC + 2) hu2_lt_nbr5 hbaseC3_lt_nbr5 hk5 hki hkj)
    have h7 : nbr7[baseC + 2]! = nbr6[baseC + 2]! := by
      have hki : baseC + 2 ≠ baseA + 2 := by
        have hlt : baseA + 2 < baseC + 2 := by
          have : m + 2 < m + 10 := Nat.add_lt_add_left (by decide : (2 : Nat) < 10) m
          simpa [baseA, baseC, Nat.add_assoc] using this
        exact (Nat.ne_of_lt hlt).symm
      have hkj : baseC + 2 ≠ baseC + 0 := by
        have hlt : baseC + 0 < baseC + 2 := by
          -- `baseC + 0 = baseC` and `0 < 2`.
          have : baseC < baseC + 2 :=
            Nat.lt_add_of_pos_right (n := baseC) (k := 2) (by decide : 0 < 2)
          simpa using this
        exact (Nat.ne_of_lt hlt).symm
      have hi7 : baseA + 2 < nbr6.size := by
        have : m + 2 < m + 12 := Nat.add_lt_add_left (by decide : (2 : Nat) < 12) m
        have : baseA + 2 = m + 2 := by simp [baseA, Nat.add_assoc]
        simpa [this, hnbr6_size] using this_1
      have hj7 : baseC + 0 < nbr6.size := by
        have : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
        have : baseC + 0 = m + 8 := by simp [baseC, Nat.add_assoc]
        simpa [this, hnbr6_size] using this_1
      simpa [nbr7] using (setPair!_getBang_ne nbr6 (baseA + 2) (baseC + 0) (baseC + 2) hi7 hj7 hk6 hki hkj)
    have h8 : nbr8[baseC + 2]! = nbr7[baseC + 2]! := by
      have hki : baseC + 2 ≠ baseA + 3 := by
        have hlt : baseA + 3 < baseC + 2 := by
          have : m + 3 < m + 10 := Nat.add_lt_add_left (by decide : (3 : Nat) < 10) m
          simpa [baseA, baseC, Nat.add_assoc] using this
        exact (Nat.ne_of_lt hlt).symm
      have hkj : baseC + 2 ≠ baseB + 0 := by
        have hlt : baseB + 0 < baseC + 2 := by
          have : m + 4 < m + 10 := Nat.add_lt_add_left (by decide : (4 : Nat) < 10) m
          simpa [baseB, baseC, Nat.add_assoc] using this
        exact (Nat.ne_of_lt hlt).symm
      have hi8 : baseA + 3 < nbr7.size := by
        have : m + 3 < m + 12 := Nat.add_lt_add_left (by decide : (3 : Nat) < 12) m
        have : baseA + 3 = m + 3 := by simp [baseA, Nat.add_assoc]
        simpa [this, hnbr7_size] using this_1
      have hj8 : baseB + 0 < nbr7.size := by
        have : m + 4 < m + 12 := Nat.add_lt_add_left (by decide : (4 : Nat) < 12) m
        have : baseB + 0 = m + 4 := by simp [baseB, Nat.add_assoc]
        simpa [this, hnbr7_size] using this_1
      simpa [nbr8] using (setPair!_getBang_ne nbr7 (baseA + 3) (baseB + 0) (baseC + 2) hi8 hj8 hk7 hki hkj)
    have h9 : nbr[baseC + 2]! = nbr8[baseC + 2]! := by
      have hki : baseC + 2 ≠ baseB + 2 := by
        have hlt : baseB + 2 < baseC + 2 := by
          have : m + 6 < m + 10 := Nat.add_lt_add_left (by decide : (6 : Nat) < 10) m
          simpa [baseB, baseC, Nat.add_assoc] using this
        exact (Nat.ne_of_lt hlt).symm
      have hkj : baseC + 2 ≠ baseC + 1 := by
        have hlt : baseC + 1 < baseC + 2 := by
          simpa [Nat.add_assoc] using Nat.lt_succ_self (baseC + 1)
        exact (Nat.ne_of_lt hlt).symm
      have hi9 : baseB + 2 < nbr8.size := by
        have : m + 6 < m + 12 := Nat.add_lt_add_left (by decide : (6 : Nat) < 12) m
        have : baseB + 2 = m + 6 := by simp [baseB, Nat.add_assoc]
        simpa [this, hnbr8_size] using this_1
      have hj9 : baseC + 1 < nbr8.size := by
        have : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
        have : baseC + 1 = m + 9 := by simp [baseC, Nat.add_assoc]
        simpa [this, hnbr8_size] using this_1
      simpa [nbr] using (setPair!_getBang_ne nbr8 (baseB + 2) (baseC + 1) (baseC + 2) hi9 hj9 hk8 hki hkj)
    have hFinal : nbr[baseC + 2]! = w2 := by
      calc
        nbr[baseC + 2]! = nbr8[baseC + 2]! := h9
        _ = nbr7[baseC + 2]! := h8
        _ = nbr6[baseC + 2]! := h7
        _ = nbr5[baseC + 2]! := h6
        _ = w2 := h5
    have hnbr : r3BraidLeftNbr g x u w = nbr := by rfl
    simpa [r3BraidLeftGraph, hnbr, baseC] using hFinal
  have hC2' : (r3BraidLeftGraph g x u w).arcNbr[baseL + 2]! = w2 := by
    -- `baseL = m+8`.
    have : baseL + 2 = m + 10 := by
      calc
        baseL + 2 = (m + 8) + 2 := by simpa [hbaseL]
        _ = m + 10 := by simp [Nat.add_assoc]
    simpa [this] using hC2
  have hne : (r3BraidLeftGraph g x u w).arcNbr[baseL + 2]! ≠ baseL + 1 := by
    intro hEq
    have hw2_lt_base : w2 < baseL + 1 := by
      -- `w2 < m` and `m ≤ baseL+1`.
      have : w2 < m := hw2
      have hm_le : m ≤ baseL + 1 := by
        -- `baseL = m+8`.
        simpa [hbaseL, Nat.add_assoc] using Nat.le_add_right m 9
      exact Nat.lt_of_lt_of_le this hm_le
    have : w2 = baseL + 1 := by simpa [hC2'] using hEq
    exact (Nat.ne_of_lt hw2_lt_base) this
  have hbne : ((r3BraidLeftGraph g x u w).arcNbr[baseL + 2]! != baseL + 1) = true :=
    (bne_iff_ne).2 hne
  -- The neg curl expects `(base+1) ↔ (base+2)`; here `(base+2)` points to `w2`.
  simp [Reidemeister.r1RemoveLast, hvgL, hn0, baseL, hbne]

private theorem r1RemoveLast_pos_err_of_r3BraidRight_ok
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    Reidemeister.r1RemoveLast gR .pos = .error "r1RemoveLast: internal loop arc mismatch" := by
  classical
  have hg : gR = r3BraidRightGraph g x u w := by
    simpa [r3BraidRightGraph, r3BraidRightNbr] using
      (r3BraidRight_eq_gOut (g := g) (gR := gR) (x := x) (u := u) (w := w) h)
  subst hg
  have hvg : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := r3BraidRightGraph g x u w) (x := x) (u := u) (w := w) h
  have hsizeG : g.arcNbr.size = g.numHalfEdges :=
    PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg
  have hValid : PDGraph.Valid (r3BraidRightGraph g x u w) := by
    simpa using (r3BraidRight_valid (g := g) (gR := r3BraidRightGraph g x u w) (x := x) (u := u) (w := w) h)
  have hvgR : PDGraph.validate (r3BraidRightGraph g x u w) = .ok () :=
    PDGraph.validate_eq_ok_of_valid hValid
  have hn0 : (r3BraidRightGraph g x u w).n ≠ 0 := by
    simp [r3BraidRightGraph]
  let m : Nat := g.numHalfEdges
  let baseL : Nat := (r3BraidRightGraph g x u w).numHalfEdges - 4
  have hbaseL : baseL = m + 8 := by
    dsimp [baseL, r3BraidRightGraph, m, PDGraph.numHalfEdges]
    simpa using four_mul_add_three_sub_four g.n
  -- `baseC+0` is wired to `baseB+3`, so the positive-curl internal loop check fails.
  have hC0 : (r3BraidRightGraph g x u w).arcNbr[m + 8]! = m + 7 := by
    let x2 := g.arcNbr[x]!
    let u2 := g.arcNbr[u]!
    let w2 := g.arcNbr[w]!
    let baseA := m
    let baseB := m + 4
    let baseC := m + 8
    let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
    let nbr1 := setPair! nbr0 u (baseA + 0)
    let nbr2 := setPair! nbr1 w (baseA + 1)
    let nbr3 := setPair! nbr2 x (baseB + 0)
    let nbr4 := setPair! nbr3 w2 (baseB + 2)
    let nbr5 := setPair! nbr4 u2 (baseC + 2)
    let nbr6 := setPair! nbr5 x2 (baseC + 3)
    let nbr7 := setPair! nbr6 (baseA + 2) (baseB + 1)
    let nbr8 := setPair! nbr7 (baseB + 3) (baseC + 0)
    let nbr := setPair! nbr8 (baseA + 3) (baseC + 1)
    have hsizeGm : g.arcNbr.size = m := by simpa [m] using hsizeG
    have hnbr0_size : nbr0.size = m + 12 := by
      simp [nbr0, hsizeGm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    -- sizes are stable under `setPair!`
    have hnbr7_size : nbr7.size = m + 12 := by
      calc
        nbr7.size = nbr0.size := by
          simp [nbr7, nbr6, nbr5, nbr4, nbr3, nbr2, nbr1, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr0_size
    have hnbr8_size : nbr8.size = m + 12 := by
      calc
        nbr8.size = nbr7.size := by
          simp [nbr8, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr7_size
    have hnbr_size : nbr.size = m + 12 := by
      calc
        nbr.size = nbr8.size := by
          simp [nbr, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr8_size
    have hbaseB3_lt_nbr7 : baseB + 3 < nbr7.size := by
      have : m + 7 < m + 12 := Nat.add_lt_add_left (by decide : (7 : Nat) < 12) m
      have : baseB + 3 = m + 7 := by simp [baseB, Nat.add_assoc]
      simpa [this, hnbr7_size] using this_1
    have hbaseC0_lt_nbr7 : baseC + 0 < nbr7.size := by
      have : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
      have : baseC + 0 = m + 8 := by simp [baseC, Nat.add_assoc]
      simpa [this, hnbr7_size] using this_1
    have h8 : nbr8[baseC + 0]! = baseB + 3 := by
      simpa [nbr8] using
        (setPair!_getBang_right nbr7 (baseB + 3) (baseC + 0) hbaseB3_lt_nbr7 hbaseC0_lt_nbr7)
    have h9 : nbr[baseC + 0]! = nbr8[baseC + 0]! := by
      have hki : baseC + 0 ≠ baseA + 3 := by
        have : m + 3 < m + 8 := Nat.add_lt_add_left (by decide : (3 : Nat) < 8) m
        exact (Nat.ne_of_lt (by simpa [baseA, baseC, Nat.add_assoc] using this)).symm
      have hkj : baseC + 0 ≠ baseC + 1 := by
        exact Nat.ne_of_lt (Nat.lt_succ_self (baseC + 0))
      have hi9 : baseA + 3 < nbr8.size := by
        have : m + 3 < m + 12 := Nat.add_lt_add_left (by decide : (3 : Nat) < 12) m
        have : baseA + 3 = m + 3 := by simp [baseA, Nat.add_assoc]
        simpa [this, hnbr8_size] using this_1
      have hj9 : baseC + 1 < nbr8.size := by
        have : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
        have : baseC + 1 = m + 9 := by simp [baseC, Nat.add_assoc]
        simpa [this, hnbr8_size] using this_1
      have hk9 : baseC + 0 < nbr8.size := by
        have : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
        have : baseC + 0 = m + 8 := by simp [baseC, Nat.add_assoc]
        simpa [this, hnbr8_size] using this_1
      simpa [nbr] using (setPair!_getBang_ne nbr8 (baseA + 3) (baseC + 1) (baseC + 0) hi9 hj9 hk9 hki hkj)
    have hFinal : nbr[baseC + 0]! = baseB + 3 := by
      calc
        nbr[baseC + 0]! = nbr8[baseC + 0]! := h9
        _ = baseB + 3 := h8
    have hnbr : r3BraidRightNbr g x u w = nbr := by rfl
    simpa [r3BraidRightGraph, hnbr, baseC, baseB, Nat.add_assoc] using hFinal
  have hC0' : (r3BraidRightGraph g x u w).arcNbr[baseL]! = m + 7 := by
    have : baseL = m + 8 := hbaseL
    simpa [this] using hC0
  have hne : (r3BraidRightGraph g x u w).arcNbr[baseL]! ≠ baseL + 1 := by
    intro hEq
    have : (m + 7 : Nat) = m + 9 := by
      have hbase1 : baseL + 1 = m + 9 := by
        simpa [hbaseL, Nat.add_assoc] using rfl
      simpa [hC0', hbase1] using hEq
    exact (Nat.ne_of_lt (Nat.add_lt_add_left (by decide : (7 : Nat) < 9) m)) this
  have hbne : ((r3BraidRightGraph g x u w).arcNbr[baseL]! != baseL + 1) = true :=
    (bne_iff_ne).2 hne
  simp [Reidemeister.r1RemoveLast, hvgR, hn0, baseL, hbne]

private theorem r1RemoveLast_neg_err_of_r3BraidRight_ok
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    Reidemeister.r1RemoveLast gR .neg = .error "r1RemoveLast: internal loop arc mismatch" := by
  classical
  have hg : gR = r3BraidRightGraph g x u w := by
    simpa [r3BraidRightGraph, r3BraidRightNbr] using
      (r3BraidRight_eq_gOut (g := g) (gR := gR) (x := x) (u := u) (w := w) h)
  subst hg
  have hvg : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := r3BraidRightGraph g x u w) (x := x) (u := u) (w := w) h
  have hgValid : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok (g := g) hvg
  have hsizeG : g.arcNbr.size = g.numHalfEdges :=
    PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg
  have hValid : PDGraph.Valid (r3BraidRightGraph g x u w) := by
    simpa using (r3BraidRight_valid (g := g) (gR := r3BraidRightGraph g x u w) (x := x) (u := u) (w := w) h)
  have hvgR : PDGraph.validate (r3BraidRightGraph g x u w) = .ok () :=
    PDGraph.validate_eq_ok_of_valid hValid
  have hn0 : (r3BraidRightGraph g x u w).n ≠ 0 := by
    simp [r3BraidRightGraph]
  have hxuwh : x < g.numHalfEdges ∧ u < g.numHalfEdges ∧ w < g.numHalfEdges :=
    lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := r3BraidRightGraph g x u w) (x := x) (u := u) (w := w) h
  let m : Nat := g.numHalfEdges
  let u2 : Nat := g.arcNbr[u]!
  have hu2 : u2 < m := by
    have hu : u < m := hxuwh.2.1
    simpa [m, u2] using (PDGraph.Valid.get_lt hgValid (i := u) (hi := hu))
  let baseL : Nat := (r3BraidRightGraph g x u w).numHalfEdges - 4
  have hbaseL : baseL = m + 8 := by
    dsimp [baseL, r3BraidRightGraph, m, PDGraph.numHalfEdges]
    simpa using four_mul_add_three_sub_four g.n
  -- `baseC+2` is wired to `u2`, hence the neg internal loop check fails.
  have hC2 : (r3BraidRightGraph g x u w).arcNbr[m + 10]! = u2 := by
    let x2 := g.arcNbr[x]!
    let w2 := g.arcNbr[w]!
    let baseA := m
    let baseB := m + 4
    let baseC := m + 8
    let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
    let nbr1 := setPair! nbr0 u (baseA + 0)
    let nbr2 := setPair! nbr1 w (baseA + 1)
    let nbr3 := setPair! nbr2 x (baseB + 0)
    let nbr4 := setPair! nbr3 w2 (baseB + 2)
    let nbr5 := setPair! nbr4 u2 (baseC + 2)
    let nbr6 := setPair! nbr5 x2 (baseC + 3)
    let nbr7 := setPair! nbr6 (baseA + 2) (baseB + 1)
    let nbr8 := setPair! nbr7 (baseB + 3) (baseC + 0)
    let nbr := setPair! nbr8 (baseA + 3) (baseC + 1)
    have hsizeGm : g.arcNbr.size = m := by simpa [m] using hsizeG
    have hnbr0_size : nbr0.size = m + 12 := by
      simp [nbr0, hsizeGm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    have hnbr4_size : nbr4.size = m + 12 := by
      calc
        nbr4.size = nbr0.size := by
          simp [nbr4, nbr3, nbr2, nbr1, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr0_size
    have hnbr5_size : nbr5.size = m + 12 := by
      calc
        nbr5.size = nbr4.size := by
          simp [nbr5, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr4_size
    have hu2_lt_nbr4 : u2 < nbr4.size := by
      have : u2 < m + 12 := Nat.lt_of_lt_of_le hu2 (Nat.le_add_right m 12)
      simpa [hnbr4_size] using this
    have hbaseC2_lt_nbr4 : baseC + 2 < nbr4.size := by
      have : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
      have : baseC + 2 = m + 10 := by simp [baseC, Nat.add_assoc]
      simpa [this, hnbr4_size] using this_1
    have h5 : nbr5[baseC + 2]! = u2 := by
      simpa [nbr5] using (setPair!_getBang_right nbr4 u2 (baseC + 2) hu2_lt_nbr4 hbaseC2_lt_nbr4)
    -- Later updates never touch `baseC+2`.
    have hnbr6 : nbr6[baseC + 2]! = nbr5[baseC + 2]! := by
      have hnbr6_size : nbr6.size = m + 12 := by
        calc
          nbr6.size = nbr5.size := by simp [nbr6, setPair!, Array.size_setIfInBounds]
          _ = m + 12 := hnbr5_size
      have hk6 : baseC + 2 < nbr5.size := by
        have : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
        have : baseC + 2 = m + 10 := by simp [baseC, Nat.add_assoc]
        simpa [this, hnbr5_size] using this_1
      have hu2_lt_nbr5 : x2 < nbr5.size := by
        -- `x2 < m` by validity and thus `< m+12`.
        have hx : x < m := hxuwh.1
        have hx2 : x2 < m := by
          simpa [m, x2] using (PDGraph.Valid.get_lt hgValid (i := x) (hi := hx))
        have : x2 < m + 12 := Nat.lt_of_lt_of_le hx2 (Nat.le_add_right m 12)
        simpa [hnbr5_size] using this
      have hbaseC3_lt_nbr5 : baseC + 3 < nbr5.size := by
        have : m + 11 < m + 12 := Nat.add_lt_add_left (by decide : (11 : Nat) < 12) m
        have : baseC + 3 = m + 11 := by simp [baseC, Nat.add_assoc]
        simpa [this, hnbr5_size] using this_1
      have hki : baseC + 2 ≠ x2 := by
        have : x2 < baseC + 2 := by
          have hx : x < m := hxuwh.1
          have hx2 : x2 < m := by
            simpa [m, x2] using (PDGraph.Valid.get_lt hgValid (i := x) (hi := hx))
          have hm_le : m ≤ baseC + 2 := by simp [baseC, Nat.add_assoc]
          exact Nat.lt_of_lt_of_le hx2 hm_le
        exact (Nat.ne_of_lt this).symm
      have hkj : baseC + 2 ≠ baseC + 3 := Nat.ne_of_lt (Nat.lt_succ_self (baseC + 2))
      simpa [nbr6] using (setPair!_getBang_ne nbr5 x2 (baseC + 3) (baseC + 2) hu2_lt_nbr5 hbaseC3_lt_nbr5 hk6 hki hkj)
    have hnbr6_size : nbr6.size = m + 12 := by
      calc
        nbr6.size = nbr5.size := by simp [nbr6, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr5_size
    have hnbr7_size : nbr7.size = m + 12 := by
      calc
        nbr7.size = nbr6.size := by simp [nbr7, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr6_size
    have hnbr8_size : nbr8.size = m + 12 := by
      calc
        nbr8.size = nbr7.size := by simp [nbr8, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr7_size
    have hnbr_size : nbr.size = m + 12 := by
      calc
        nbr.size = nbr8.size := by simp [nbr, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr8_size
    have hnbr7 : nbr7[baseC + 2]! = nbr6[baseC + 2]! := by
      have hi : baseA + 2 < nbr6.size := by
        have h' : m + 2 < m + 12 := Nat.add_lt_add_left (by decide : (2 : Nat) < 12) m
        have hEq : baseA + 2 = m + 2 := by simp [baseA, Nat.add_assoc]
        simpa [hEq, hnbr6_size] using h'
      have hj : baseB + 1 < nbr6.size := by
        have h' : m + 5 < m + 12 := Nat.add_lt_add_left (by decide : (5 : Nat) < 12) m
        have hEq : baseB + 1 = m + 5 := by simp [baseB, Nat.add_assoc]
        simpa [hEq, hnbr6_size] using h'
      have hk : baseC + 2 < nbr6.size := by
        have h' : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
        have hEq : baseC + 2 = m + 10 := by simp [baseC, Nat.add_assoc]
        simpa [hEq, hnbr6_size] using h'
      have hki : baseC + 2 ≠ baseA + 2 := by
        have hlt : baseA + 2 < baseC + 2 := by
          have h' : m + 2 < m + 10 := Nat.add_lt_add_left (by decide : (2 : Nat) < 10) m
          simpa [baseA, baseC, Nat.add_assoc] using h'
        exact (Nat.ne_of_lt hlt).symm
      have hkj : baseC + 2 ≠ baseB + 1 := by
        have hlt : baseB + 1 < baseC + 2 := by
          have h' : m + 5 < m + 10 := Nat.add_lt_add_left (by decide : (5 : Nat) < 10) m
          simpa [baseB, baseC, Nat.add_assoc] using h'
        exact (Nat.ne_of_lt hlt).symm
      simpa [nbr7] using (setPair!_getBang_ne nbr6 (baseA + 2) (baseB + 1) (baseC + 2) hi hj hk hki hkj)
    have hnbr8 : nbr8[baseC + 2]! = nbr7[baseC + 2]! := by
      have hi : baseB + 3 < nbr7.size := by
        have h' : m + 7 < m + 12 := Nat.add_lt_add_left (by decide : (7 : Nat) < 12) m
        have hEq : baseB + 3 = m + 7 := by simp [baseB, Nat.add_assoc]
        simpa [hEq, hnbr7_size] using h'
      have hj : baseC + 0 < nbr7.size := by
        have h' : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
        have hEq : baseC + 0 = m + 8 := by simp [baseC, Nat.add_assoc]
        simpa [hEq, hnbr7_size] using h'
      have hk : baseC + 2 < nbr7.size := by
        have h' : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
        have hEq : baseC + 2 = m + 10 := by simp [baseC, Nat.add_assoc]
        simpa [hEq, hnbr7_size] using h'
      have hki : baseC + 2 ≠ baseB + 3 := by
        have hlt : baseB + 3 < baseC + 2 := by
          have h' : m + 7 < m + 10 := Nat.add_lt_add_left (by decide : (7 : Nat) < 10) m
          simpa [baseB, baseC, Nat.add_assoc] using h'
        exact (Nat.ne_of_lt hlt).symm
      have hkj : baseC + 2 ≠ baseC + 0 := by
        have hlt : baseC + 0 < baseC + 2 := by
          have h' : (0 : Nat) < 2 := by decide
          simpa [Nat.add_assoc] using Nat.add_lt_add_left h' baseC
        exact (Nat.ne_of_lt hlt).symm
      simpa [nbr8] using (setPair!_getBang_ne nbr7 (baseB + 3) (baseC + 0) (baseC + 2) hi hj hk hki hkj)
    have hnbr9 : nbr[baseC + 2]! = nbr8[baseC + 2]! := by
      have hi : baseA + 3 < nbr8.size := by
        have h' : m + 3 < m + 12 := Nat.add_lt_add_left (by decide : (3 : Nat) < 12) m
        have hEq : baseA + 3 = m + 3 := by simp [baseA, Nat.add_assoc]
        simpa [hEq, hnbr8_size] using h'
      have hj : baseC + 1 < nbr8.size := by
        have h' : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
        have hEq : baseC + 1 = m + 9 := by simp [baseC, Nat.add_assoc]
        simpa [hEq, hnbr8_size] using h'
      have hk : baseC + 2 < nbr8.size := by
        have h' : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
        have hEq : baseC + 2 = m + 10 := by simp [baseC, Nat.add_assoc]
        simpa [hEq, hnbr8_size] using h'
      have hki : baseC + 2 ≠ baseA + 3 := by
        have hlt : baseA + 3 < baseC + 2 := by
          have h' : m + 3 < m + 10 := Nat.add_lt_add_left (by decide : (3 : Nat) < 10) m
          simpa [baseA, baseC, Nat.add_assoc] using h'
        exact Nat.ne_of_lt hlt |>.symm
      have hkj : baseC + 2 ≠ baseC + 1 := by
        have hlt : baseC + 1 < baseC + 2 := Nat.lt_succ_self (baseC + 1)
        exact (Nat.ne_of_lt hlt).symm
      simpa [nbr] using (setPair!_getBang_ne nbr8 (baseA + 3) (baseC + 1) (baseC + 2) hi hj hk hki hkj)
    have hFinal : nbr[baseC + 2]! = u2 := by
      have hEq : nbr[baseC + 2]! = nbr5[baseC + 2]! := by
        calc
          nbr[baseC + 2]! = nbr8[baseC + 2]! := hnbr9
          _ = nbr7[baseC + 2]! := hnbr8
          _ = nbr6[baseC + 2]! := hnbr7
          _ = nbr5[baseC + 2]! := hnbr6
      calc
        nbr[baseC + 2]! = nbr5[baseC + 2]! := hEq
        _ = u2 := h5
    have hIdx : m + 10 = baseC + 2 := by simp [baseC, Nat.add_assoc]
    have hFinal' : nbr[m + 10]! = u2 := by simpa [hIdx] using hFinal
    have hnbr : r3BraidRightNbr g x u w = nbr := by rfl
    simpa [r3BraidRightGraph, hnbr] using hFinal'
  have hne : (r3BraidRightGraph g x u w).arcNbr[baseL + 2]! ≠ baseL + 1 := by
    -- `u2 < m` while `baseL+1 = m+9`.
    intro hEq
    have hm_le : m ≤ baseL + 1 := by
      simpa [hbaseL, Nat.add_assoc] using Nat.le_add_right m 9
    have hu2_lt_base : u2 < baseL + 1 := Nat.lt_of_lt_of_le hu2 hm_le
    have : u2 = baseL + 1 := by
      have hIdx : baseL + 2 = m + 10 := by
        calc
          baseL + 2 = (m + 8) + 2 := by simpa [hbaseL]
          _ = m + 10 := by simp [Nat.add_assoc]
      have hArc : (r3BraidRightGraph g x u w).arcNbr[baseL + 2]! = u2 := by
        simpa [hIdx] using hC2
      simpa [hArc] using hEq
    exact (Nat.ne_of_lt hu2_lt_base) this
  have hbne : ((r3BraidRightGraph g x u w).arcNbr[baseL + 2]! != baseL + 1) = true :=
    (bne_iff_ne).2 hne
  simp [Reidemeister.r1RemoveLast, hvgR, hn0, baseL, hbne]

private theorem r2RemoveLast_err_of_r3BraidLeft_ok
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    Reidemeister.r2RemoveLast gL = .error "r2RemoveLast: internal arc (1↔0) mismatch" := by
  classical
  have hg : gL = r3BraidLeftGraph g x u w := by
    simpa [r3BraidLeftGraph, r3BraidLeftNbr] using
      (r3BraidLeft_eq_gOut (g := g) (gL := gL) (x := x) (u := u) (w := w) h)
  subst hg
  have hValid : PDGraph.Valid (r3BraidLeftGraph g x u w) := by
    simpa using (r3BraidLeft_valid (g := g) (gL := r3BraidLeftGraph g x u w) (x := x) (u := u) (w := w) h)
  have hvgL : PDGraph.validate (r3BraidLeftGraph g x u w) = .ok () :=
    PDGraph.validate_eq_ok_of_valid hValid
  have hnlt : ¬ (r3BraidLeftGraph g x u w).n < 2 := by
    have : 2 ≤ (r3BraidLeftGraph g x u w).n := by
      -- `n = g.n + 3 ≥ 3`.
      have : 2 ≤ 3 := by decide
      have : 3 ≤ g.n + 3 := Nat.le_add_left 3 g.n
      simpa [r3BraidLeftGraph] using Nat.le_trans this this_1
    exact Nat.not_lt_of_ge this
  -- The first internal-arc check fails because `baseB+1` is paired to the external `w`.
  have hwu : x < g.numHalfEdges ∧ u < g.numHalfEdges ∧ w < g.numHalfEdges :=
    lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := r3BraidLeftGraph g x u w) (x := x) (u := u) (w := w) h
  let m : Nat := g.numHalfEdges
  have hw_lt : w < m := hwu.2.2
  have hne : w ≠ m + 8 := by
    have : w < m + 8 := Nat.lt_of_lt_of_le hw_lt (Nat.le_add_right m 8)
    exact Nat.ne_of_lt this
  have hB1 : (r3BraidLeftGraph g x u w).arcNbr[m + 5]! = w := by
    -- `baseB+1 = m+5` is set by the boundary update `w ↔ baseB+1` and never overwritten.
    have hvg : PDGraph.validate g = .ok () :=
      validate_of_r3BraidLeft_ok (g := g) (gL := r3BraidLeftGraph g x u w) (x := x) (u := u) (w := w) h
    have hgValid : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok (g := g) hvg
    have hsizeG : g.arcNbr.size = m := by
      simpa [m] using PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg
    let x2 := g.arcNbr[x]!
    let u2 := g.arcNbr[u]!
    let w2 := g.arcNbr[w]!
    have hx2m : x2 < m := by
      have hx : x < m := hwu.1
      simpa [m, x2] using (PDGraph.Valid.get_lt hgValid (i := x) (hi := hx))
    have hu2m : u2 < m := by
      have hu : u < m := hwu.2.1
      simpa [m, u2] using (PDGraph.Valid.get_lt hgValid (i := u) (hi := hu))
    have hw2m : w2 < m := by
      have hw : w < m := hwu.2.2
      simpa [m, w2] using (PDGraph.Valid.get_lt hgValid (i := w) (hi := hw))
    let baseA := m
    let baseB := m + 4
    let baseC := m + 8
    let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
    let nbr1 := setPair! nbr0 x (baseA + 0)
    let nbr2 := setPair! nbr1 u (baseA + 1)
    let nbr3 := setPair! nbr2 w (baseB + 1)
    let nbr4 := setPair! nbr3 x2 (baseB + 3)
    let nbr5 := setPair! nbr4 w2 (baseC + 2)
    let nbr6 := setPair! nbr5 u2 (baseC + 3)
    let nbr7 := setPair! nbr6 (baseA + 2) (baseC + 0)
    let nbr8 := setPair! nbr7 (baseA + 3) (baseB + 0)
    let nbr := setPair! nbr8 (baseB + 2) (baseC + 1)
    have hnbr0_size : nbr0.size = m + 12 := by
      simp [nbr0, hsizeG, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    have hnbr2_size : nbr2.size = m + 12 := by
      calc
        nbr2.size = nbr0.size := by
          simp [nbr2, nbr1, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr0_size
    have hnbr3_size : nbr3.size = m + 12 := by
      calc
        nbr3.size = nbr2.size := by simp [nbr3, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr2_size
    have hnbr4_size : nbr4.size = m + 12 := by
      calc
        nbr4.size = nbr3.size := by simp [nbr4, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr3_size
    have hnbr5_size : nbr5.size = m + 12 := by
      calc
        nbr5.size = nbr4.size := by simp [nbr5, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr4_size
    have hnbr6_size : nbr6.size = m + 12 := by
      calc
        nbr6.size = nbr5.size := by simp [nbr6, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr5_size
    have hnbr7_size : nbr7.size = m + 12 := by
      calc
        nbr7.size = nbr6.size := by simp [nbr7, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr6_size
    have hnbr8_size : nbr8.size = m + 12 := by
      calc
        nbr8.size = nbr7.size := by simp [nbr8, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr7_size
    have hnbr_size : nbr.size = m + 12 := by
      calc
        nbr.size = nbr8.size := by simp [nbr, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr8_size
    have hbaseB1_lt : baseB + 1 < m + 12 := by
      have h' : m + 5 < m + 12 := Nat.add_lt_add_left (by decide : (5 : Nat) < 12) m
      simpa [baseB, Nat.add_assoc] using h'
    have hk2 : baseB + 1 < nbr2.size := by simpa [hnbr2_size] using hbaseB1_lt
    have hw_lt_nbr2 : w < nbr2.size := by
      have : w < m + 12 := Nat.lt_of_lt_of_le hw_lt (Nat.le_add_right m 12)
      simpa [hnbr2_size] using this
    have h3 : nbr3[baseB + 1]! = w := by
      simpa [nbr3] using (setPair!_getBang_right nbr2 w (baseB + 1) hw_lt_nbr2 hk2)
    have hk3 : baseB + 1 < nbr3.size := by simpa [hnbr3_size] using hbaseB1_lt
    have hk4 : baseB + 1 < nbr4.size := by simpa [hnbr4_size] using hbaseB1_lt
    have hk5 : baseB + 1 < nbr5.size := by simpa [hnbr5_size] using hbaseB1_lt
    have hk6 : baseB + 1 < nbr6.size := by simpa [hnbr6_size] using hbaseB1_lt
    have hk7 : baseB + 1 < nbr7.size := by simpa [hnbr7_size] using hbaseB1_lt
    have hk8 : baseB + 1 < nbr8.size := by simpa [hnbr8_size] using hbaseB1_lt
    have hk : baseB + 1 < nbr.size := by simpa [hnbr_size] using hbaseB1_lt
    have hx2_lt_nbr3 : x2 < nbr3.size := by
      have : x2 < m + 12 := Nat.lt_of_lt_of_le hx2m (Nat.le_add_right m 12)
      simpa [hnbr3_size] using this
    have hbaseB3_lt_nbr3 : baseB + 3 < nbr3.size := by
      have h' : m + 7 < m + 12 := Nat.add_lt_add_left (by decide : (7 : Nat) < 12) m
      have hEq : baseB + 3 = m + 7 := by simp [baseB, Nat.add_assoc]
      simpa [hEq, hnbr3_size] using h'
    have hki4 : baseB + 1 ≠ x2 := by
      have hm_le : m ≤ baseB + 1 := by simp [baseB, Nat.add_assoc]
      have : x2 < baseB + 1 := Nat.lt_of_lt_of_le hx2m hm_le
      exact (Nat.ne_of_lt this).symm
    have hkj4 : baseB + 1 ≠ baseB + 3 := by
      have hlt : baseB + 1 < baseB + 3 := by
        have : (1 : Nat) < 3 := by decide
        simpa [Nat.add_assoc] using Nat.add_lt_add_left this baseB
      exact Nat.ne_of_lt hlt
    have h4 : nbr4[baseB + 1]! = nbr3[baseB + 1]! := by
      simpa [nbr4] using
        (setPair!_getBang_ne nbr3 x2 (baseB + 3) (baseB + 1) hx2_lt_nbr3 hbaseB3_lt_nbr3 hk3 hki4 hkj4)
    have hw2_lt_nbr4 : w2 < nbr4.size := by
      have : w2 < m + 12 := Nat.lt_of_lt_of_le hw2m (Nat.le_add_right m 12)
      simpa [hnbr4_size] using this
    have hbaseC2_lt_nbr4 : baseC + 2 < nbr4.size := by
      have h' : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
      have hEq : baseC + 2 = m + 10 := by simp [baseC, Nat.add_assoc]
      simpa [hEq, hnbr4_size] using h'
    have hki5 : baseB + 1 ≠ w2 := by
      have hm_le : m ≤ baseB + 1 := by simp [baseB, Nat.add_assoc]
      have : w2 < baseB + 1 := Nat.lt_of_lt_of_le hw2m hm_le
      exact (Nat.ne_of_lt this).symm
    have hkj5 : baseB + 1 ≠ baseC + 2 := by
      have hlt : baseB + 1 < baseC + 2 := by
        have : (m + 5 : Nat) < m + 10 := Nat.add_lt_add_left (by decide : (5 : Nat) < 10) m
        simpa [baseB, baseC, Nat.add_assoc] using this
      exact Nat.ne_of_lt hlt
    have h5 : nbr5[baseB + 1]! = nbr4[baseB + 1]! := by
      simpa [nbr5] using (setPair!_getBang_ne nbr4 w2 (baseC + 2) (baseB + 1) hw2_lt_nbr4 hbaseC2_lt_nbr4 hk4 hki5 hkj5)
    have hu2_lt_nbr5 : u2 < nbr5.size := by
      have : u2 < m + 12 := Nat.lt_of_lt_of_le hu2m (Nat.le_add_right m 12)
      simpa [hnbr5_size] using this
    have hbaseC3_lt_nbr5 : baseC + 3 < nbr5.size := by
      have h' : m + 11 < m + 12 := Nat.add_lt_add_left (by decide : (11 : Nat) < 12) m
      have hEq : baseC + 3 = m + 11 := by simp [baseC, Nat.add_assoc]
      simpa [hEq, hnbr5_size] using h'
    have hki6 : baseB + 1 ≠ u2 := by
      have hm_le : m ≤ baseB + 1 := by simp [baseB, Nat.add_assoc]
      have : u2 < baseB + 1 := Nat.lt_of_lt_of_le hu2m hm_le
      exact (Nat.ne_of_lt this).symm
    have hkj6 : baseB + 1 ≠ baseC + 3 := by
      have hlt : baseB + 1 < baseC + 3 := by
        have : (m + 5 : Nat) < m + 11 := Nat.add_lt_add_left (by decide : (5 : Nat) < 11) m
        simpa [baseB, baseC, Nat.add_assoc] using this
      exact Nat.ne_of_lt hlt
    have h6 : nbr6[baseB + 1]! = nbr5[baseB + 1]! := by
      simpa [nbr6] using (setPair!_getBang_ne nbr5 u2 (baseC + 3) (baseB + 1) hu2_lt_nbr5 hbaseC3_lt_nbr5 hk5 hki6 hkj6)
    have hi7 : baseA + 2 < nbr6.size := by
      have h' : m + 2 < m + 12 := Nat.add_lt_add_left (by decide : (2 : Nat) < 12) m
      have hEq : baseA + 2 = m + 2 := by simp [baseA, Nat.add_assoc]
      simpa [hEq, hnbr6_size] using h'
    have hj7 : baseC + 0 < nbr6.size := by
      have h' : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
      have hEq : baseC + 0 = m + 8 := by simp [baseC, Nat.add_assoc]
      simpa [hEq, hnbr6_size] using h'
    have hki7 : baseB + 1 ≠ baseA + 2 := by
      have hlt : baseA + 2 < baseB + 1 := by
        have : (m + 2 : Nat) < m + 5 := Nat.add_lt_add_left (by decide : (2 : Nat) < 5) m
        simpa [baseA, baseB, Nat.add_assoc] using this
      exact (Nat.ne_of_lt hlt).symm
    have hkj7 : baseB + 1 ≠ baseC + 0 := by
      have hlt : baseB + 1 < baseC + 0 := by
        have : (m + 5 : Nat) < m + 8 := Nat.add_lt_add_left (by decide : (5 : Nat) < 8) m
        simpa [baseB, baseC, Nat.add_assoc] using this
      exact Nat.ne_of_lt hlt
    have h7 : nbr7[baseB + 1]! = nbr6[baseB + 1]! := by
      simpa [nbr7] using (setPair!_getBang_ne nbr6 (baseA + 2) (baseC + 0) (baseB + 1) hi7 hj7 hk6 hki7 hkj7)
    have hi8 : baseA + 3 < nbr7.size := by
      have h' : m + 3 < m + 12 := Nat.add_lt_add_left (by decide : (3 : Nat) < 12) m
      have hEq : baseA + 3 = m + 3 := by simp [baseA, Nat.add_assoc]
      simpa [hEq, hnbr7_size] using h'
    have hj8 : baseB + 0 < nbr7.size := by
      have h' : m + 4 < m + 12 := Nat.add_lt_add_left (by decide : (4 : Nat) < 12) m
      have hEq : baseB + 0 = m + 4 := by simp [baseB, Nat.add_assoc]
      simpa [hEq, hnbr7_size] using h'
    have hki8 : baseB + 1 ≠ baseA + 3 := by
      have hlt : baseA + 3 < baseB + 1 := by
        have : (m + 3 : Nat) < m + 5 := Nat.add_lt_add_left (by decide : (3 : Nat) < 5) m
        simpa [baseA, baseB, Nat.add_assoc] using this
      exact (Nat.ne_of_lt hlt).symm
    have hkj8 : baseB + 1 ≠ baseB + 0 := by
      have hlt : baseB + 0 < baseB + 1 := Nat.lt_succ_self (baseB + 0)
      exact (Nat.ne_of_lt hlt).symm
    have h8 : nbr8[baseB + 1]! = nbr7[baseB + 1]! := by
      simpa [nbr8] using (setPair!_getBang_ne nbr7 (baseA + 3) (baseB + 0) (baseB + 1) hi8 hj8 hk7 hki8 hkj8)
    have hi9 : baseB + 2 < nbr8.size := by
      have h' : m + 6 < m + 12 := Nat.add_lt_add_left (by decide : (6 : Nat) < 12) m
      have hEq : baseB + 2 = m + 6 := by simp [baseB, Nat.add_assoc]
      simpa [hEq, hnbr8_size] using h'
    have hj9 : baseC + 1 < nbr8.size := by
      have h' : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
      have hEq : baseC + 1 = m + 9 := by simp [baseC, Nat.add_assoc]
      simpa [hEq, hnbr8_size] using h'
    have hki9 : baseB + 1 ≠ baseB + 2 := by
      exact Nat.ne_of_lt (Nat.lt_succ_self (baseB + 1))
    have hkj9 : baseB + 1 ≠ baseC + 1 := by
      have hlt : baseB + 1 < baseC + 1 := by
        have : (m + 5 : Nat) < m + 9 := Nat.add_lt_add_left (by decide : (5 : Nat) < 9) m
        simpa [baseB, baseC, Nat.add_assoc] using this
      exact Nat.ne_of_lt hlt
    have h9 : nbr[baseB + 1]! = nbr8[baseB + 1]! := by
      simpa [nbr] using (setPair!_getBang_ne nbr8 (baseB + 2) (baseC + 1) (baseB + 1) hi9 hj9 hk8 hki9 hkj9)
    have hFinal : nbr[baseB + 1]! = w := by
      calc
        nbr[baseB + 1]! = nbr8[baseB + 1]! := h9
        _ = nbr7[baseB + 1]! := h8
        _ = nbr6[baseB + 1]! := h7
        _ = nbr5[baseB + 1]! := h6
        _ = nbr4[baseB + 1]! := h5
        _ = nbr3[baseB + 1]! := h4
        _ = w := h3
    have hIdx : m + 5 = baseB + 1 := by simp [baseB, Nat.add_assoc]
    have hFinal' : nbr[m + 5]! = w := by simpa [hIdx] using hFinal
    have hnbr : r3BraidLeftNbr g x u w = nbr := by rfl
    simpa [r3BraidLeftGraph, hnbr] using hFinal'
  have hne' : (r3BraidLeftGraph g x u w).arcNbr[m + 5]! ≠ m + 8 := by
    simpa [hB1] using hne
  have hnum : (r3BraidLeftGraph g x u w).numHalfEdges = m + 12 := by
    dsimp [r3BraidLeftGraph, m, PDGraph.numHalfEdges]
    simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hbase1 : (r3BraidLeftGraph g x u w).numHalfEdges - 8 + 1 = m + 5 := by
    have h8 : (8 : Nat) ≤ 12 := by decide
    have hsub : (m + 12) - 8 = m + 4 := by
      calc
        (m + 12) - 8 = m + (12 - 8) := by
          simpa using (Nat.add_sub_assoc (n := m) (m := 12) (k := 8) h8)
        _ = m + 4 := by simp
    calc
      (r3BraidLeftGraph g x u w).numHalfEdges - 8 + 1 = (m + 12) - 8 + 1 := by simpa [hnum]
      _ = (m + 4) + 1 := by simpa [hsub]
      _ = m + 5 := by simp [Nat.add_assoc]
  have hbase2 : (r3BraidLeftGraph g x u w).numHalfEdges - 4 = m + 8 := by
    have h4 : (4 : Nat) ≤ 12 := by decide
    calc
      (r3BraidLeftGraph g x u w).numHalfEdges - 4 = (m + 12) - 4 := by simpa [hnum]
      _ = m + (12 - 4) := by
        simpa using (Nat.add_sub_assoc (n := m) (m := 12) (k := 4) h4)
      _ = m + 8 := by simp
  have hMismatch :
      (¬(r3BraidLeftGraph g x u w).arcNbr[(r3BraidLeftGraph g x u w).numHalfEdges - 8 + 1]! =
            (r3BraidLeftGraph g x u w).numHalfEdges - 4 ∨
        ¬(r3BraidLeftGraph g x u w).arcNbr[(r3BraidLeftGraph g x u w).numHalfEdges - 4]! =
            (r3BraidLeftGraph g x u w).numHalfEdges - 8 + 1) := by
    refine Or.inl ?_
    simpa [hbase1, hbase2] using hne'
  simp [Reidemeister.r2RemoveLast, hvgL, hnlt, hMismatch]

private theorem r2RemoveLast_err_of_r3BraidRight_ok
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    Reidemeister.r2RemoveLast gR = .error "r2RemoveLast: internal arc (1↔0) mismatch" := by
  classical
  have hg : gR = r3BraidRightGraph g x u w := by
    simpa [r3BraidRightGraph, r3BraidRightNbr] using
      (r3BraidRight_eq_gOut (g := g) (gR := gR) (x := x) (u := u) (w := w) h)
  subst hg
  have hValid : PDGraph.Valid (r3BraidRightGraph g x u w) := by
    simpa using (r3BraidRight_valid (g := g) (gR := r3BraidRightGraph g x u w) (x := x) (u := u) (w := w) h)
  have hvgR : PDGraph.validate (r3BraidRightGraph g x u w) = .ok () :=
    PDGraph.validate_eq_ok_of_valid hValid
  have hnlt : ¬ (r3BraidRightGraph g x u w).n < 2 := by
    have : 2 ≤ (r3BraidRightGraph g x u w).n := by
      have : 2 ≤ 3 := by decide
      have : 3 ≤ g.n + 3 := Nat.le_add_left 3 g.n
      simpa [r3BraidRightGraph] using Nat.le_trans this this_1
    exact Nat.not_lt_of_ge this
  -- `baseB+1` is paired with `baseA+2`, so the first internal-arc check fails.
  let m : Nat := g.numHalfEdges
  have hne : (m + 2 : Nat) ≠ m + 8 := by
    exact Nat.ne_of_lt (Nat.add_lt_add_left (by decide : (2 : Nat) < 8) m)
  have hB1 : (r3BraidRightGraph g x u w).arcNbr[m + 5]! = m + 2 := by
    have hvg : PDGraph.validate g = .ok () :=
      validate_of_r3BraidRight_ok (g := g) (gR := r3BraidRightGraph g x u w) (x := x) (u := u) (w := w) h
    have hsizeG : g.arcNbr.size = m := by
      simpa [m] using PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg
    -- Expand the neighbor array and read only the `baseA+2 ↔ baseB+1` update.
    let x2 := g.arcNbr[x]!
    let u2 := g.arcNbr[u]!
    let w2 := g.arcNbr[w]!
    let baseA := m
    let baseB := m + 4
    let baseC := m + 8
    let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
    let nbr1 := setPair! nbr0 u (baseA + 0)
    let nbr2 := setPair! nbr1 w (baseA + 1)
    let nbr3 := setPair! nbr2 x (baseB + 0)
    let nbr4 := setPair! nbr3 w2 (baseB + 2)
    let nbr5 := setPair! nbr4 u2 (baseC + 2)
    let nbr6 := setPair! nbr5 x2 (baseC + 3)
    let nbr7 := setPair! nbr6 (baseA + 2) (baseB + 1)
    let nbr8 := setPair! nbr7 (baseB + 3) (baseC + 0)
    let nbr := setPair! nbr8 (baseA + 3) (baseC + 1)
    have hnbr0_size : nbr0.size = m + 12 := by
      simp [nbr0, hsizeG, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    have hnbr6_size : nbr6.size = m + 12 := by
      calc
        nbr6.size = nbr0.size := by
          simp [nbr6, nbr5, nbr4, nbr3, nbr2, nbr1, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr0_size
    have hnbr7_size : nbr7.size = m + 12 := by
      calc
        nbr7.size = nbr6.size := by simp [nbr7, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr6_size
    have hnbr8_size : nbr8.size = m + 12 := by
      calc
        nbr8.size = nbr7.size := by simp [nbr8, setPair!, Array.size_setIfInBounds]
        _ = m + 12 := hnbr7_size
    have hi7 : baseA + 2 < nbr6.size := by
      have h' : m + 2 < m + 12 := Nat.add_lt_add_left (by decide : (2 : Nat) < 12) m
      have hEq : baseA + 2 = m + 2 := by simp [baseA, Nat.add_assoc]
      simpa [hEq, hnbr6_size] using h'
    have hj7 : baseB + 1 < nbr6.size := by
      have h' : m + 5 < m + 12 := Nat.add_lt_add_left (by decide : (5 : Nat) < 12) m
      have hEq : baseB + 1 = m + 5 := by simp [baseB, Nat.add_assoc]
      simpa [hEq, hnbr6_size] using h'
    have h7 : nbr7[baseB + 1]! = baseA + 2 := by
      simpa [nbr7] using (setPair!_getBang_right nbr6 (baseA + 2) (baseB + 1) hi7 hj7)
    have hi8 : baseB + 3 < nbr7.size := by
      have h' : m + 7 < m + 12 := Nat.add_lt_add_left (by decide : (7 : Nat) < 12) m
      have hEq : baseB + 3 = m + 7 := by simp [baseB, Nat.add_assoc]
      simpa [hEq, hnbr7_size] using h'
    have hj8 : baseC + 0 < nbr7.size := by
      have h' : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
      have hEq : baseC + 0 = m + 8 := by simp [baseC, Nat.add_assoc]
      simpa [hEq, hnbr7_size] using h'
    have hk8 : baseB + 1 < nbr7.size := by
      have h' : m + 5 < m + 12 := Nat.add_lt_add_left (by decide : (5 : Nat) < 12) m
      have hEq : baseB + 1 = m + 5 := by simp [baseB, Nat.add_assoc]
      simpa [hEq, hnbr7_size] using h'
    have hki8 : baseB + 1 ≠ baseB + 3 := by
      have hlt : baseB + 1 < baseB + 3 := by
        have : (1 : Nat) < 3 := by decide
        simpa [Nat.add_assoc] using Nat.add_lt_add_left this baseB
      exact Nat.ne_of_lt hlt
    have hkj8 : baseB + 1 ≠ baseC + 0 := by
      have hlt : baseB + 1 < baseC + 0 := by
        have : (m + 5 : Nat) < m + 8 := Nat.add_lt_add_left (by decide : (5 : Nat) < 8) m
        simpa [baseB, baseC, Nat.add_assoc] using this
      exact Nat.ne_of_lt hlt
    have h8 : nbr8[baseB + 1]! = nbr7[baseB + 1]! := by
      simpa [nbr8] using (setPair!_getBang_ne nbr7 (baseB + 3) (baseC + 0) (baseB + 1) hi8 hj8 hk8 hki8 hkj8)
    have hi9 : baseA + 3 < nbr8.size := by
      have h' : m + 3 < m + 12 := Nat.add_lt_add_left (by decide : (3 : Nat) < 12) m
      have hEq : baseA + 3 = m + 3 := by simp [baseA, Nat.add_assoc]
      simpa [hEq, hnbr8_size] using h'
    have hj9 : baseC + 1 < nbr8.size := by
      have h' : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
      have hEq : baseC + 1 = m + 9 := by simp [baseC, Nat.add_assoc]
      simpa [hEq, hnbr8_size] using h'
    have hk9 : baseB + 1 < nbr8.size := by
      have h' : m + 5 < m + 12 := Nat.add_lt_add_left (by decide : (5 : Nat) < 12) m
      have hEq : baseB + 1 = m + 5 := by simp [baseB, Nat.add_assoc]
      simpa [hEq, hnbr8_size] using h'
    have hki9 : baseB + 1 ≠ baseA + 3 := by
      have hlt : baseA + 3 < baseB + 1 := by
        have : (m + 3 : Nat) < m + 5 := Nat.add_lt_add_left (by decide : (3 : Nat) < 5) m
        simpa [baseA, baseB, Nat.add_assoc] using this
      exact (Nat.ne_of_lt hlt).symm
    have hkj9 : baseB + 1 ≠ baseC + 1 := by
      have hlt : baseB + 1 < baseC + 1 := by
        have : (m + 5 : Nat) < m + 9 := Nat.add_lt_add_left (by decide : (5 : Nat) < 9) m
        simpa [baseB, baseC, Nat.add_assoc] using this
      exact Nat.ne_of_lt hlt
    have h9 : nbr[baseB + 1]! = nbr8[baseB + 1]! := by
      simpa [nbr] using (setPair!_getBang_ne nbr8 (baseA + 3) (baseC + 1) (baseB + 1) hi9 hj9 hk9 hki9 hkj9)
    have hFinal : nbr[baseB + 1]! = m + 2 := by
      have hEq : nbr[baseB + 1]! = baseA + 2 := by
        calc
          nbr[baseB + 1]! = nbr8[baseB + 1]! := h9
          _ = nbr7[baseB + 1]! := h8
          _ = baseA + 2 := h7
      simpa [baseA, Nat.add_assoc] using hEq
    have hIdx : m + 5 = baseB + 1 := by simp [baseB, Nat.add_assoc]
    have hFinal' : nbr[m + 5]! = m + 2 := by simpa [hIdx] using hFinal
    have hnbr : r3BraidRightNbr g x u w = nbr := by rfl
    simpa [r3BraidRightGraph, hnbr] using hFinal'
  have hne' : (r3BraidRightGraph g x u w).arcNbr[m + 5]! ≠ m + 8 := by
    simpa [hB1] using hne
  have hnum : (r3BraidRightGraph g x u w).numHalfEdges = m + 12 := by
    dsimp [r3BraidRightGraph, m, PDGraph.numHalfEdges]
    simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hbase1 : (r3BraidRightGraph g x u w).numHalfEdges - 8 + 1 = m + 5 := by
    have h8 : (8 : Nat) ≤ 12 := by decide
    have hsub : (m + 12) - 8 = m + 4 := by
      calc
        (m + 12) - 8 = m + (12 - 8) := by
          simpa using (Nat.add_sub_assoc (n := m) (m := 12) (k := 8) h8)
        _ = m + 4 := by simp
    calc
      (r3BraidRightGraph g x u w).numHalfEdges - 8 + 1 = (m + 12) - 8 + 1 := by simpa [hnum]
      _ = (m + 4) + 1 := by simpa [hsub]
      _ = m + 5 := by simp [Nat.add_assoc]
  have hbase2 : (r3BraidRightGraph g x u w).numHalfEdges - 4 = m + 8 := by
    have h4 : (4 : Nat) ≤ 12 := by decide
    calc
      (r3BraidRightGraph g x u w).numHalfEdges - 4 = (m + 12) - 4 := by simpa [hnum]
      _ = m + (12 - 4) := by
        simpa using (Nat.add_sub_assoc (n := m) (m := 12) (k := 4) h4)
      _ = m + 8 := by simp
  have hMismatch :
      (¬(r3BraidRightGraph g x u w).arcNbr[(r3BraidRightGraph g x u w).numHalfEdges - 8 + 1]! =
            (r3BraidRightGraph g x u w).numHalfEdges - 4 ∨
        ¬(r3BraidRightGraph g x u w).arcNbr[(r3BraidRightGraph g x u w).numHalfEdges - 4]! =
            (r3BraidRightGraph g x u w).numHalfEdges - 8 + 1) := by
    refine Or.inl ?_
    simpa [hbase1, hbase2] using hne'
  simp [Reidemeister.r2RemoveLast, hvgR, hnlt, hMismatch]

/-!
## TL₃ context functional (bridge infrastructure)

This section defines the “plug a 3‑strand TL basis diagram into a PDGraph context” operation.

It is the algebraic interface used to connect the evaluator’s 3-step skein expansion on the
braid gadget to the already-proved TL₃ braid relation `TL3Expr.braid_relation`.
-/

namespace TL3Context

open TL3Expr

private def endpoints (g : PDGraph) (x u w : Nat) : Array Nat :=
  #[x, u, w, g.arcNbr[x]!, g.arcNbr[u]!, g.arcNbr[w]!]

private def rewireBasis (nbr : Array Nat) (x u w x2 u2 w2 : Nat) : TL3Expr.Basis → Array Nat
  | .id =>
      setPair! (setPair! (setPair! nbr x x2) u u2) w w2
  | .e1 =>
      setPair! (setPair! (setPair! nbr x u) x2 u2) w w2
  | .e2 =>
      setPair! (setPair! (setPair! nbr x x2) u w) u2 w2
  | .e1e2 =>
      setPair! (setPair! (setPair! nbr x u) w x2) u2 w2
  | .e2e1 =>
      setPair! (setPair! (setPair! nbr u w) x2 u2) x w2

private def plugBasisGraph (g : PDGraph) (x u w : Nat) (b : TL3Expr.Basis) : PDGraph :=
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  { freeLoops := g.freeLoops
    n := g.n
    arcNbr := rewireBasis g.arcNbr x u w x2 u2 w2 b }

private def evalBasis (fuel : Nat) (g : PDGraph) (x u w : Nat) (b : TL3Expr.Basis) :
    Except String PolyML :=
  bracketGraphMLAux fuel (plugBasisGraph g x u w b)

def evalTL3Expr (fuel : Nat) (g : PDGraph) (x u w : Nat) (a : TL3Expr) :
    Except String PolyML := do
  let pid ← evalBasis fuel g x u w .id
  let pe1 ← evalBasis fuel g x u w .e1
  let pe2 ← evalBasis fuel g x u w .e2
  let pe1e2 ← evalBasis fuel g x u w .e1e2
  let pe2e1 ← evalBasis fuel g x u w .e2e1
  return (a.coeff .id) * pid
    + (a.coeff .e1) * pe1
    + (a.coeff .e2) * pe2
    + (a.coeff .e1e2) * pe1e2
    + (a.coeff .e2e1) * pe2e1

end TL3Context

/-!
## Bridge step 1: explicit smoothing rewires on the last crossing of the braid gadget

To connect the 3-crossing braid gadget computation to the TL₃ context functional, we need
deterministic control over the **first** `smoothLastCoreML` rewire (removing the last crossing).

We record the rewire effect on the only four external endpoints incident to the removed crossing.
-/

section BridgeStep1

private lemma baseC_eq (n : Nat) :
    4 * (n + 3) - 4 = 4 * n + 8 := four_mul_add_three_sub_four n

private theorem arcNbr_r3BraidLeft_baseB2
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    (r3BraidLeftGraph g x u w).arcNbr[m + 6]! = m + 9 := by
  classical
  let m := g.numHalfEdges
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
  let nbr6 :=
    setPair!
      (setPair!
        (setPair!
          (setPair!
            (setPair!
              (setPair! nbr0 x (baseA + 0)) u (baseA + 1))
            w (baseB + 1))
          x2 (baseB + 3))
        w2 (baseC + 2))
      u2 (baseC + 3)
  let nbr7 := setPair! nbr6 (baseA + 2) (baseC + 0)
  let nbr8 := setPair! nbr7 (baseA + 3) (baseB + 0)
  let nbr := setPair! nbr8 (baseB + 2) (baseC + 1)
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hsizeG : g.arcNbr.size = m := by
    simpa [m] using PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg0
  have hnbr0_size : nbr0.size = m + 12 := by
    simp [nbr0, hsizeG, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hnbr8_size : nbr8.size = m + 12 := by
    simp [nbr8, nbr7, nbr6, setPair!_size, hnbr0_size]
  have hi : baseB + 2 < nbr8.size := by
    have : m + 6 < m + 12 := Nat.add_lt_add_left (by decide : (6 : Nat) < 12) m
    simpa [hnbr8_size, baseB, Nat.add_assoc] using this
  have hj : baseC + 1 < nbr8.size := by
    have : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
    simpa [hnbr8_size, baseC, Nat.add_assoc] using this
  have hij : baseB + 2 ≠ baseC + 1 := by
    have : (m + 6 : Nat) < m + 9 := Nat.add_lt_add_left (by decide : (6 : Nat) < 9) m
    exact Nat.ne_of_lt (by simpa [baseB, baseC, Nat.add_assoc] using this)
  have hval : nbr[baseB + 2]! = baseC + 1 := by
    simpa [nbr] using (setPair!_getBang_left nbr8 (baseB + 2) (baseC + 1) hi hj hij)
  have hnbr : r3BraidLeftNbr g x u w = nbr := by rfl
  -- `baseB+2 = m+6` and `baseC+1 = m+9`.
  simpa [r3BraidLeftGraph, hnbr, baseB, baseC, Nat.add_assoc] using hval

private theorem arcNbr_r3BraidLeft_baseB0
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    (r3BraidLeftGraph g x u w).arcNbr[m + 4]! = m + 3 := by
  classical
  let m := g.numHalfEdges
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
  let nbr6 :=
    setPair!
      (setPair!
        (setPair!
          (setPair!
            (setPair!
              (setPair! nbr0 x (baseA + 0)) u (baseA + 1))
            w (baseB + 1))
          x2 (baseB + 3))
        w2 (baseC + 2))
      u2 (baseC + 3)
  let nbr7 := setPair! nbr6 (baseA + 2) (baseC + 0)
  let nbr8 := setPair! nbr7 (baseA + 3) (baseB + 0)
  let nbr := setPair! nbr8 (baseB + 2) (baseC + 1)
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hsizeG : g.arcNbr.size = m := by
    simpa [m] using PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg0
  have hnbr0_size : nbr0.size = m + 12 := by
    simp [nbr0, hsizeG, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hnbr6_size : nbr6.size = m + 12 := by
    simp [nbr6, setPair!_size, hnbr0_size]
  have hnbr7_size : nbr7.size = m + 12 := by
    simp [nbr7, setPair!_size, hnbr6_size]
  have hnbr8_size : nbr8.size = m + 12 := by
    simp [nbr8, setPair!_size, hnbr7_size]
  have hi8 : baseA + 3 < nbr7.size := by
    have : m + 3 < m + 12 := Nat.add_lt_add_left (by decide : (3 : Nat) < 12) m
    simpa [baseA, hnbr7_size, Nat.add_assoc] using this
  have hj8 : baseB + 0 < nbr7.size := by
    have : m + 4 < m + 12 := Nat.add_lt_add_left (by decide : (4 : Nat) < 12) m
    simpa [baseB, hnbr7_size, Nat.add_assoc] using this
  have hval8 : nbr8[baseB + 0]! = baseA + 3 := by
    simpa [nbr8] using (setPair!_getBang_right nbr7 (baseA + 3) (baseB + 0) hi8 hj8)
  have hi9 : baseB + 2 < nbr8.size := by
    have : m + 6 < m + 12 := Nat.add_lt_add_left (by decide : (6 : Nat) < 12) m
    simpa [baseB, hnbr8_size, Nat.add_assoc] using this
  have hj9 : baseC + 1 < nbr8.size := by
    have : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
    simpa [baseC, hnbr8_size, Nat.add_assoc] using this
  have hk9 : baseB + 0 < nbr8.size := by
    have : m + 4 < m + 12 := Nat.add_lt_add_left (by decide : (4 : Nat) < 12) m
    simpa [baseB, hnbr8_size, Nat.add_assoc] using this
  have hki9 : baseB + 0 ≠ baseB + 2 := by
    exact Nat.ne_of_lt (Nat.lt_add_of_pos_right (n := baseB + 0) (by decide : 0 < 2))
  have hkj9 : baseB + 0 ≠ baseC + 1 := by
    exact Nat.ne_of_lt (by
      have : (m + 4 : Nat) < m + 9 := Nat.add_lt_add_left (by decide : (4 : Nat) < 9) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have hval : nbr[baseB + 0]! = nbr8[baseB + 0]! := by
    simpa [nbr] using (setPair!_getBang_ne nbr8 (baseB + 2) (baseC + 1) (baseB + 0) hi9 hj9 hk9 hki9 hkj9)
  have hFinal : nbr[baseB + 0]! = baseA + 3 := by
    calc
      nbr[baseB + 0]! = nbr8[baseB + 0]! := hval
      _ = baseA + 3 := hval8
  have hnbr : r3BraidLeftNbr g x u w = nbr := by rfl
  -- `baseB+0 = m+4` and `baseA+3 = m+3`.
  simpa [r3BraidLeftGraph, hnbr, baseA, baseB, Nat.add_assoc] using hFinal

private theorem arcNbr_r3BraidLeft_baseB1
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    (r3BraidLeftGraph g x u w).arcNbr[m + 5]! = w := by
  classical
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  let m := g.numHalfEdges
  have hsizeG : g.arcNbr.size = m := by
    simpa [m] using PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg0
  have hx : x < m :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).1
  have hw : w < m :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.2
  have hu : u < m :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.1
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  have hx2_lt_m : x2 < m := PDGraph.Valid.get_lt hValidG (i := x) hx
  have hu2_lt_m : u2 < m := PDGraph.Valid.get_lt hValidG (i := u) hu
  have hw2_lt_m : w2 < m := PDGraph.Valid.get_lt hValidG (i := w) hw
  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
  let nbr1 := setPair! nbr0 x (baseA + 0)
  let nbr2 := setPair! nbr1 u (baseA + 1)
  let nbr3 := setPair! nbr2 w (baseB + 1)
  let nbr4 := setPair! nbr3 x2 (baseB + 3)
  let nbr5 := setPair! nbr4 w2 (baseC + 2)
  let nbr6 := setPair! nbr5 u2 (baseC + 3)
  let nbr7 := setPair! nbr6 (baseA + 2) (baseC + 0)
  let nbr8 := setPair! nbr7 (baseA + 3) (baseB + 0)
  let nbr := setPair! nbr8 (baseB + 2) (baseC + 1)
  have hnbr0_size : nbr0.size = m + 12 := by
    simp [nbr0, hsizeG, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hnbr1_size : nbr1.size = m + 12 := by
    simp [nbr1, setPair!_size, hnbr0_size]
  have hnbr2_size : nbr2.size = m + 12 := by
    simp [nbr2, setPair!_size, hnbr1_size]
  have hnbr3_size : nbr3.size = m + 12 := by
    simp [nbr3, setPair!_size, hnbr2_size]
  have hnbr4_size : nbr4.size = m + 12 := by
    simp [nbr4, setPair!_size, hnbr3_size]
  have hnbr5_size : nbr5.size = m + 12 := by
    simp [nbr5, setPair!_size, hnbr4_size]
  have hnbr6_size : nbr6.size = m + 12 := by
    simp [nbr6, setPair!_size, hnbr5_size]
  have hnbr7_size : nbr7.size = m + 12 := by
    simp [nbr7, setPair!_size, hnbr6_size]
  have hnbr8_size : nbr8.size = m + 12 := by
    simp [nbr8, setPair!_size, hnbr7_size]
  have hw_lt_2 : w < nbr2.size := by
    have : w < m + 12 := Nat.lt_of_lt_of_le hw (Nat.le_add_right m 12)
    simpa [hnbr2_size] using this
  have hB1_lt_2 : baseB + 1 < nbr2.size := by
    have : m + 5 < m + 12 := Nat.add_lt_add_left (by decide : (5 : Nat) < 12) m
    simpa [baseB, hnbr2_size, Nat.add_assoc] using this
  have hB1 : nbr3[baseB + 1]! = w := by
    simpa [nbr3] using (setPair!_getBang_right nbr2 w (baseB + 1) hw_lt_2 hB1_lt_2)
  -- Propagate the lookup through later, disjoint `setPair!` updates.
  have hB3_lt_3 : baseB + 3 < nbr3.size := by
    have : m + 7 < m + 12 := Nat.add_lt_add_left (by decide : (7 : Nat) < 12) m
    simpa [baseB, hnbr3_size, Nat.add_assoc] using this
  have hx2_lt_3 : x2 < nbr3.size := by
    have : x2 < m + 12 := Nat.lt_of_lt_of_le hx2_lt_m (Nat.le_add_right m 12)
    simpa [hnbr3_size] using this
  have hB1_lt_3 : baseB + 1 < nbr3.size := by
    simpa [hnbr3_size, hnbr2_size] using hB1_lt_2
  have hB1_ne_x2 : baseB + 1 ≠ x2 := by
    have : x2 < baseB + 1 := by
      have : x2 < m + 5 := Nat.lt_of_lt_of_le hx2_lt_m (Nat.le_add_right m 5)
      simpa [baseB, Nat.add_assoc] using this
    exact Nat.ne_of_gt this
  have hB1_ne_B3 : baseB + 1 ≠ baseB + 3 := by
    exact Nat.ne_of_lt (Nat.lt_add_of_pos_right (n := baseB + 1) (by decide : 0 < 2))
  have hkeep4 : nbr4[baseB + 1]! = nbr3[baseB + 1]! := by
    simpa [nbr4] using
      (setPair!_getBang_ne nbr3 x2 (baseB + 3) (baseB + 1) hx2_lt_3 hB3_lt_3 hB1_lt_3 hB1_ne_x2 hB1_ne_B3)
  have hw2_lt_4 : w2 < nbr4.size := by
    have : w2 < m + 12 := Nat.lt_of_lt_of_le hw2_lt_m (Nat.le_add_right m 12)
    simpa [hnbr4_size] using this
  have hC2_lt_4 : baseC + 2 < nbr4.size := by
    have : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
    simpa [baseC, hnbr4_size, Nat.add_assoc] using this
  have hB1_lt_4 : baseB + 1 < nbr4.size := by
    simpa [hnbr4_size, hnbr3_size] using hB1_lt_3
  have hB1_ne_w2 : baseB + 1 ≠ w2 := by
    have : w2 < baseB + 1 := by
      have : w2 < m + 5 := Nat.lt_of_lt_of_le hw2_lt_m (Nat.le_add_right m 5)
      simpa [baseB, Nat.add_assoc] using this
    exact Nat.ne_of_gt this
  have hB1_ne_C2 : baseB + 1 ≠ baseC + 2 := by
    exact Nat.ne_of_lt (by
      have : (m + 5 : Nat) < m + 10 := Nat.add_lt_add_left (by decide : (5 : Nat) < 10) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have hkeep5 : nbr5[baseB + 1]! = nbr4[baseB + 1]! := by
    simpa [nbr5] using
      (setPair!_getBang_ne nbr4 w2 (baseC + 2) (baseB + 1) hw2_lt_4 hC2_lt_4 hB1_lt_4 hB1_ne_w2 hB1_ne_C2)
  have hu2_lt_5 : u2 < nbr5.size := by
    have : u2 < m + 12 := Nat.lt_of_lt_of_le hu2_lt_m (Nat.le_add_right m 12)
    simpa [hnbr5_size] using this
  have hC3_lt_5 : baseC + 3 < nbr5.size := by
    have : m + 11 < m + 12 := Nat.add_lt_add_left (by decide : (11 : Nat) < 12) m
    simpa [baseC, hnbr5_size, Nat.add_assoc] using this
  have hB1_lt_5 : baseB + 1 < nbr5.size := by
    simpa [hnbr5_size, hnbr4_size] using hB1_lt_4
  have hB1_ne_u2 : baseB + 1 ≠ u2 := by
    have : u2 < baseB + 1 := by
      have : u2 < m + 5 := Nat.lt_of_lt_of_le hu2_lt_m (Nat.le_add_right m 5)
      simpa [baseB, Nat.add_assoc] using this
    exact Nat.ne_of_gt this
  have hB1_ne_C3 : baseB + 1 ≠ baseC + 3 := by
    exact Nat.ne_of_lt (by
      have : (m + 5 : Nat) < m + 11 := Nat.add_lt_add_left (by decide : (5 : Nat) < 11) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have hkeep6 : nbr6[baseB + 1]! = nbr5[baseB + 1]! := by
    simpa [nbr6] using
      (setPair!_getBang_ne nbr5 u2 (baseC + 3) (baseB + 1) hu2_lt_5 hC3_lt_5 hB1_lt_5 hB1_ne_u2 hB1_ne_C3)
  have hA2_lt_6 : baseA + 2 < nbr6.size := by
    have : m + 2 < m + 12 := Nat.add_lt_add_left (by decide : (2 : Nat) < 12) m
    simpa [baseA, hnbr6_size, Nat.add_assoc] using this
  have hC0_lt_6 : baseC + 0 < nbr6.size := by
    have : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
    simpa [baseC, hnbr6_size, Nat.add_assoc] using this
  have hB1_lt_6 : baseB + 1 < nbr6.size := by
    simpa [hnbr6_size, hnbr5_size] using hB1_lt_5
  have hB1_ne_A2 : baseB + 1 ≠ baseA + 2 := by
    exact Nat.ne_of_gt (by
      have : (m + 2 : Nat) < m + 5 := Nat.add_lt_add_left (by decide : (2 : Nat) < 5) m
      simpa [baseA, baseB, Nat.add_assoc] using this)
  have hB1_ne_C0 : baseB + 1 ≠ baseC + 0 := by
    exact Nat.ne_of_lt (by
      have : (m + 5 : Nat) < m + 8 := Nat.add_lt_add_left (by decide : (5 : Nat) < 8) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have hkeep7 : nbr7[baseB + 1]! = nbr6[baseB + 1]! := by
    simpa [nbr7] using
      (setPair!_getBang_ne nbr6 (baseA + 2) (baseC + 0) (baseB + 1) hA2_lt_6 hC0_lt_6 hB1_lt_6 hB1_ne_A2 hB1_ne_C0)
  have hA3_lt_7 : baseA + 3 < nbr7.size := by
    have : m + 3 < m + 12 := Nat.add_lt_add_left (by decide : (3 : Nat) < 12) m
    simpa [baseA, hnbr7_size, Nat.add_assoc] using this
  have hB0_lt_7 : baseB + 0 < nbr7.size := by
    have : m + 4 < m + 12 := Nat.add_lt_add_left (by decide : (4 : Nat) < 12) m
    simpa [baseB, hnbr7_size, Nat.add_assoc] using this
  have hB1_lt_7 : baseB + 1 < nbr7.size := by
    simpa [hnbr7_size, hnbr6_size] using hB1_lt_6
  have hB1_ne_A3 : baseB + 1 ≠ baseA + 3 := by
    exact Nat.ne_of_gt (by
      have : (m + 3 : Nat) < m + 5 := Nat.add_lt_add_left (by decide : (3 : Nat) < 5) m
      simpa [baseA, baseB, Nat.add_assoc] using this)
  have hB1_ne_B0 : baseB + 1 ≠ baseB + 0 := by
    exact Nat.ne_of_gt (Nat.lt_succ_self (baseB + 0))
  have hkeep8 : nbr8[baseB + 1]! = nbr7[baseB + 1]! := by
    simpa [nbr8] using
      (setPair!_getBang_ne nbr7 (baseA + 3) (baseB + 0) (baseB + 1) hA3_lt_7 hB0_lt_7 hB1_lt_7 hB1_ne_A3 hB1_ne_B0)
  have hB2_lt_8 : baseB + 2 < nbr8.size := by
    have : m + 6 < m + 12 := Nat.add_lt_add_left (by decide : (6 : Nat) < 12) m
    simpa [baseB, hnbr8_size, Nat.add_assoc] using this
  have hC1_lt_8 : baseC + 1 < nbr8.size := by
    have : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
    simpa [baseC, hnbr8_size, Nat.add_assoc] using this
  have hB1_lt_8 : baseB + 1 < nbr8.size := by
    simpa [hnbr8_size, hnbr7_size] using hB1_lt_7
  have hB1_ne_B2 : baseB + 1 ≠ baseB + 2 := Nat.ne_of_lt (Nat.lt_succ_self (baseB + 1))
  have hB1_ne_C1 : baseB + 1 ≠ baseC + 1 := by
    exact Nat.ne_of_lt (by
      have : (m + 5 : Nat) < m + 9 := Nat.add_lt_add_left (by decide : (5 : Nat) < 9) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have hkeep : nbr[baseB + 1]! = nbr8[baseB + 1]! := by
    simpa [nbr] using (setPair!_getBang_ne nbr8 (baseB + 2) (baseC + 1) (baseB + 1) hB2_lt_8 hC1_lt_8 hB1_lt_8 hB1_ne_B2 hB1_ne_C1)
  have hnbr : r3BraidLeftNbr g x u w = nbr := by rfl
  have hFinal : nbr[baseB + 1]! = w := by
    calc
      nbr[baseB + 1]! = nbr8[baseB + 1]! := hkeep
      _ = nbr7[baseB + 1]! := hkeep8
      _ = nbr6[baseB + 1]! := hkeep7
      _ = nbr5[baseB + 1]! := hkeep6
      _ = nbr4[baseB + 1]! := hkeep5
      _ = nbr3[baseB + 1]! := hkeep4
      _ = w := hB1
  -- `baseB+1 = m+5`.
  simpa [r3BraidLeftGraph, hnbr, baseB, Nat.add_assoc] using hFinal

private theorem arcNbr_r3BraidLeft_baseB3
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    let x2 := g.arcNbr[x]!
    (r3BraidLeftGraph g x u w).arcNbr[m + 7]! = x2 := by
  classical
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  let m := g.numHalfEdges
  have hsizeG : g.arcNbr.size = m := by
    simpa [m] using PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg0
  have hx : x < m :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).1
  have hu : u < m :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.1
  have hw : w < m :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.2
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  have hx2_lt_m : x2 < m := PDGraph.Valid.get_lt hValidG (i := x) hx
  have hu2_lt_m : u2 < m := PDGraph.Valid.get_lt hValidG (i := u) hu
  have hw2_lt_m : w2 < m := PDGraph.Valid.get_lt hValidG (i := w) hw
  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
  let nbr1 := setPair! nbr0 x (baseA + 0)
  let nbr2 := setPair! nbr1 u (baseA + 1)
  let nbr3 := setPair! nbr2 w (baseB + 1)
  let nbr4 := setPair! nbr3 x2 (baseB + 3)
  let nbr5 := setPair! nbr4 w2 (baseC + 2)
  let nbr6 := setPair! nbr5 u2 (baseC + 3)
  let nbr7 := setPair! nbr6 (baseA + 2) (baseC + 0)
  let nbr8 := setPair! nbr7 (baseA + 3) (baseB + 0)
  let nbr := setPair! nbr8 (baseB + 2) (baseC + 1)
  have hnbr0_size : nbr0.size = m + 12 := by
    simp [nbr0, hsizeG, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hnbr1_size : nbr1.size = m + 12 := by
    simp [nbr1, setPair!_size, hnbr0_size]
  have hnbr2_size : nbr2.size = m + 12 := by
    simp [nbr2, setPair!_size, hnbr1_size]
  have hnbr3_size : nbr3.size = m + 12 := by
    simp [nbr3, setPair!_size, hnbr2_size]
  have hnbr4_size : nbr4.size = m + 12 := by
    simp [nbr4, setPair!_size, hnbr3_size]
  have hnbr5_size : nbr5.size = m + 12 := by
    simp [nbr5, setPair!_size, hnbr4_size]
  have hnbr6_size : nbr6.size = m + 12 := by
    simp [nbr6, setPair!_size, hnbr5_size]
  have hnbr7_size : nbr7.size = m + 12 := by
    simp [nbr7, setPair!_size, hnbr6_size]
  have hnbr8_size : nbr8.size = m + 12 := by
    simp [nbr8, setPair!_size, hnbr7_size]
  have hx2_lt_3 : x2 < nbr3.size := by
    have : x2 < m + 12 := Nat.lt_of_lt_of_le hx2_lt_m (Nat.le_add_right m 12)
    simpa [hnbr3_size] using this
  have hB3_lt_3 : baseB + 3 < nbr3.size := by
    have : m + 7 < m + 12 := Nat.add_lt_add_left (by decide : (7 : Nat) < 12) m
    simpa [baseB, hnbr3_size, Nat.add_assoc] using this
  have hB3 : nbr4[baseB + 3]! = x2 := by
    simpa [nbr4] using (setPair!_getBang_right nbr3 x2 (baseB + 3) hx2_lt_3 hB3_lt_3)
  -- Propagate through later, disjoint updates.
  have hw2_lt_4 : w2 < nbr4.size := by
    have : w2 < m + 12 := Nat.lt_of_lt_of_le hw2_lt_m (Nat.le_add_right m 12)
    simpa [hnbr4_size] using this
  have hC2_lt_4 : baseC + 2 < nbr4.size := by
    have : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
    simpa [baseC, hnbr4_size, Nat.add_assoc] using this
  have hB3_lt_4 : baseB + 3 < nbr4.size := by
    simpa [hnbr4_size, hnbr3_size] using hB3_lt_3
  have hB3_ne_w2 : baseB + 3 ≠ w2 := by
    have : w2 < baseB + 3 := by
      have : w2 < m + 7 := Nat.lt_of_lt_of_le hw2_lt_m (Nat.le_add_right m 7)
      simpa [baseB, Nat.add_assoc] using this
    exact Nat.ne_of_gt this
  have hB3_ne_C2 : baseB + 3 ≠ baseC + 2 := by
    exact Nat.ne_of_lt (by
      have : (m + 7 : Nat) < m + 10 := Nat.add_lt_add_left (by decide : (7 : Nat) < 10) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have hkeep5 : nbr5[baseB + 3]! = nbr4[baseB + 3]! := by
    simpa [nbr5] using
      (setPair!_getBang_ne nbr4 w2 (baseC + 2) (baseB + 3) hw2_lt_4 hC2_lt_4 hB3_lt_4 hB3_ne_w2 hB3_ne_C2)
  have hu2_lt_5 : u2 < nbr5.size := by
    have : u2 < m + 12 := Nat.lt_of_lt_of_le hu2_lt_m (Nat.le_add_right m 12)
    simpa [hnbr5_size] using this
  have hC3_lt_5 : baseC + 3 < nbr5.size := by
    have : m + 11 < m + 12 := Nat.add_lt_add_left (by decide : (11 : Nat) < 12) m
    simpa [baseC, hnbr5_size, Nat.add_assoc] using this
  have hB3_lt_5 : baseB + 3 < nbr5.size := by
    simpa [hnbr5_size, hnbr4_size] using hB3_lt_4
  have hB3_ne_u2 : baseB + 3 ≠ u2 := by
    have : u2 < baseB + 3 := by
      have : u2 < m + 7 := Nat.lt_of_lt_of_le hu2_lt_m (Nat.le_add_right m 7)
      simpa [baseB, Nat.add_assoc] using this
    exact Nat.ne_of_gt this
  have hB3_ne_C3 : baseB + 3 ≠ baseC + 3 := by
    exact Nat.ne_of_lt (by
      have : (m + 7 : Nat) < m + 11 := Nat.add_lt_add_left (by decide : (7 : Nat) < 11) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have hkeep6 : nbr6[baseB + 3]! = nbr5[baseB + 3]! := by
    simpa [nbr6] using
      (setPair!_getBang_ne nbr5 u2 (baseC + 3) (baseB + 3) hu2_lt_5 hC3_lt_5 hB3_lt_5 hB3_ne_u2 hB3_ne_C3)
  have hA2_lt_6 : baseA + 2 < nbr6.size := by
    have : m + 2 < m + 12 := Nat.add_lt_add_left (by decide : (2 : Nat) < 12) m
    simpa [baseA, hnbr6_size, Nat.add_assoc] using this
  have hC0_lt_6 : baseC + 0 < nbr6.size := by
    have : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
    simpa [baseC, hnbr6_size, Nat.add_assoc] using this
  have hB3_lt_6 : baseB + 3 < nbr6.size := by
    simpa [hnbr6_size, hnbr5_size] using hB3_lt_5
  have hB3_ne_A2 : baseB + 3 ≠ baseA + 2 := by
    exact Nat.ne_of_gt (by
      have : (m + 2 : Nat) < m + 7 := Nat.add_lt_add_left (by decide : (2 : Nat) < 7) m
      simpa [baseA, baseB, Nat.add_assoc] using this)
  have hB3_ne_C0 : baseB + 3 ≠ baseC + 0 := by
    exact Nat.ne_of_lt (by
      have : (m + 7 : Nat) < m + 8 := Nat.add_lt_add_left (by decide : (7 : Nat) < 8) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have hkeep7 : nbr7[baseB + 3]! = nbr6[baseB + 3]! := by
    simpa [nbr7] using
      (setPair!_getBang_ne nbr6 (baseA + 2) (baseC + 0) (baseB + 3) hA2_lt_6 hC0_lt_6 hB3_lt_6 hB3_ne_A2 hB3_ne_C0)
  have hA3_lt_7 : baseA + 3 < nbr7.size := by
    have : m + 3 < m + 12 := Nat.add_lt_add_left (by decide : (3 : Nat) < 12) m
    simpa [baseA, hnbr7_size, Nat.add_assoc] using this
  have hB0_lt_7 : baseB + 0 < nbr7.size := by
    have : m + 4 < m + 12 := Nat.add_lt_add_left (by decide : (4 : Nat) < 12) m
    simpa [baseB, hnbr7_size, Nat.add_assoc] using this
  have hB3_lt_7 : baseB + 3 < nbr7.size := by
    simpa [hnbr7_size, hnbr6_size] using hB3_lt_6
  have hB3_ne_A3 : baseB + 3 ≠ baseA + 3 := by
    exact Nat.ne_of_gt (by
      have : (m + 3 : Nat) < m + 7 := Nat.add_lt_add_left (by decide : (3 : Nat) < 7) m
      simpa [baseA, baseB, Nat.add_assoc] using this)
  have hB3_ne_B0 : baseB + 3 ≠ baseB + 0 := by
    exact Nat.ne_of_gt (Nat.lt_add_of_pos_right (n := baseB + 0) (by decide : 0 < 3))
  have hkeep8 : nbr8[baseB + 3]! = nbr7[baseB + 3]! := by
    simpa [nbr8] using
      (setPair!_getBang_ne nbr7 (baseA + 3) (baseB + 0) (baseB + 3) hA3_lt_7 hB0_lt_7 hB3_lt_7 hB3_ne_A3 hB3_ne_B0)
  have hB2_lt_8 : baseB + 2 < nbr8.size := by
    have : m + 6 < m + 12 := Nat.add_lt_add_left (by decide : (6 : Nat) < 12) m
    simpa [baseB, hnbr8_size, Nat.add_assoc] using this
  have hC1_lt_8 : baseC + 1 < nbr8.size := by
    have : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
    simpa [baseC, hnbr8_size, Nat.add_assoc] using this
  have hB3_lt_8 : baseB + 3 < nbr8.size := by
    simpa [hnbr8_size, hnbr7_size] using hB3_lt_7
  have hB3_ne_B2 : baseB + 3 ≠ baseB + 2 := by
    exact Nat.ne_of_gt (Nat.lt_succ_self (baseB + 2))
  have hB3_ne_C1 : baseB + 3 ≠ baseC + 1 := by
    exact Nat.ne_of_lt (by
      have : (m + 7 : Nat) < m + 9 := Nat.add_lt_add_left (by decide : (7 : Nat) < 9) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have hkeep : nbr[baseB + 3]! = nbr8[baseB + 3]! := by
    simpa [nbr] using
      (setPair!_getBang_ne nbr8 (baseB + 2) (baseC + 1) (baseB + 3) hB2_lt_8 hC1_lt_8 hB3_lt_8 hB3_ne_B2 hB3_ne_C1)
  have hnbr : r3BraidLeftNbr g x u w = nbr := by rfl
  have hFinal : nbr[baseB + 3]! = x2 := by
    calc
      nbr[baseB + 3]! = nbr8[baseB + 3]! := hkeep
      _ = nbr7[baseB + 3]! := hkeep8
      _ = nbr6[baseB + 3]! := hkeep7
      _ = nbr5[baseB + 3]! := hkeep6
      _ = nbr4[baseB + 3]! := hkeep5
      _ = x2 := hB3
  simpa [r3BraidLeftGraph, hnbr, baseB, Nat.add_assoc] using hFinal

private theorem arcNbr_r3BraidLeft_baseA2
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    (r3BraidLeftGraph g x u w).arcNbr[m + 2]! = m + 8 := by
  classical
  let m := g.numHalfEdges
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
  let nbr6 :=
    setPair!
      (setPair!
        (setPair!
          (setPair!
            (setPair!
              (setPair! nbr0 x (baseA + 0)) u (baseA + 1))
            w (baseB + 1))
          x2 (baseB + 3))
        w2 (baseC + 2))
      u2 (baseC + 3)
  let nbr7 := setPair! nbr6 (baseA + 2) (baseC + 0)
  let nbr8 := setPair! nbr7 (baseA + 3) (baseB + 0)
  let nbr := setPair! nbr8 (baseB + 2) (baseC + 1)
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hsizeG : g.arcNbr.size = m := by
    simpa [m] using PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg0
  have hnbr0_size : nbr0.size = m + 12 := by
    simp [nbr0, hsizeG, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hnbr6_size : nbr6.size = m + 12 := by
    -- `setPair!` is size-preserving.
    simp [nbr6, setPair!_size, hnbr0_size]
  have hi7 : baseA + 2 < nbr6.size := by
    have : m + 2 < m + 12 := Nat.add_lt_add_left (by decide : (2 : Nat) < 12) m
    simpa [hnbr6_size, baseA, Nat.add_assoc] using this
  have hj7 : baseC + 0 < nbr6.size := by
    have : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
    simpa [hnbr6_size, baseC, Nat.add_assoc] using this
  have hij7 : baseA + 2 ≠ baseC + 0 := by
    have : (m + 2 : Nat) < m + 8 := Nat.add_lt_add_left (by decide : (2 : Nat) < 8) m
    exact (Nat.ne_of_lt (by simpa [baseA, baseC, Nat.add_assoc] using this))
  have h7 : nbr7[baseA + 2]! = baseC + 0 := by
    simpa [nbr7] using (setPair!_getBang_left nbr6 (baseA + 2) (baseC + 0) hi7 hj7 hij7)
  have hk8 : baseA + 2 < nbr7.size := by
    simpa [nbr7, setPair!_size, hnbr6_size] using hi7
  have hi8 : baseA + 3 < nbr7.size := by
    have : m + 3 < m + 12 := Nat.add_lt_add_left (by decide : (3 : Nat) < 12) m
    simpa [nbr7, setPair!_size, hnbr6_size, baseA, Nat.add_assoc] using this
  have hj8 : baseB + 0 < nbr7.size := by
    have : m + 4 < m + 12 := Nat.add_lt_add_left (by decide : (4 : Nat) < 12) m
    simpa [nbr7, setPair!_size, hnbr6_size, baseB, Nat.add_assoc] using this
  have hki8 : baseA + 2 ≠ baseA + 3 := by
    exact Nat.ne_of_lt (by
      have : (2 : Nat) < 3 := by decide
      simpa [baseA, Nat.add_assoc] using Nat.add_lt_add_left this m)
  have hkj8 : baseA + 2 ≠ baseB + 0 := by
    exact Nat.ne_of_lt (by
      have : (m + 2 : Nat) < m + 4 := Nat.add_lt_add_left (by decide : (2 : Nat) < 4) m
      simpa [baseA, baseB, Nat.add_assoc] using this)
  have h8 : nbr8[baseA + 2]! = baseC + 0 := by
    have : nbr8[baseA + 2]! = nbr7[baseA + 2]! := by
      simpa [nbr8] using
        (setPair!_getBang_ne nbr7 (baseA + 3) (baseB + 0) (baseA + 2) hi8 hj8 hk8 hki8 hkj8)
    simpa [this] using h7
  have hk9 : baseA + 2 < nbr8.size := by
    simpa [nbr8, nbr7, setPair!_size, hnbr6_size] using hi7
  have hi9 : baseB + 2 < nbr8.size := by
    have : m + 6 < m + 12 := Nat.add_lt_add_left (by decide : (6 : Nat) < 12) m
    simpa [nbr8, nbr7, setPair!_size, hnbr6_size, baseB, Nat.add_assoc] using this
  have hj9 : baseC + 1 < nbr8.size := by
    have : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
    simpa [nbr8, nbr7, setPair!_size, hnbr6_size, baseC, Nat.add_assoc] using this
  have hki9 : baseA + 2 ≠ baseB + 2 := by
    exact Nat.ne_of_lt (by
      have : (m + 2 : Nat) < m + 6 := Nat.add_lt_add_left (by decide : (2 : Nat) < 6) m
      simpa [baseA, baseB, Nat.add_assoc] using this)
  have hkj9 : baseA + 2 ≠ baseC + 1 := by
    exact Nat.ne_of_lt (by
      have : (m + 2 : Nat) < m + 9 := Nat.add_lt_add_left (by decide : (2 : Nat) < 9) m
      simpa [baseA, baseC, Nat.add_assoc] using this)
  have h9 : nbr[baseA + 2]! = baseC + 0 := by
    have : nbr[baseA + 2]! = nbr8[baseA + 2]! := by
      simpa [nbr] using
        (setPair!_getBang_ne nbr8 (baseB + 2) (baseC + 1) (baseA + 2) hi9 hj9 hk9 hki9 hkj9)
    simpa [this] using h8
  have hnbr : r3BraidLeftNbr g x u w = nbr := by rfl
  -- `baseC+0 = m+8`.
  simpa [r3BraidLeftGraph, hnbr, baseA, baseC, Nat.add_assoc] using h9

private theorem arcNbr_r3BraidLeft_baseC1
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    (r3BraidLeftGraph g x u w).arcNbr[m + 9]! = m + 6 := by
  classical
  let m := g.numHalfEdges
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
  let nbr6 :=
    setPair!
      (setPair!
        (setPair!
          (setPair!
            (setPair!
              (setPair! nbr0 x (baseA + 0)) u (baseA + 1))
            w (baseB + 1))
          x2 (baseB + 3))
        w2 (baseC + 2))
      u2 (baseC + 3)
  let nbr7 := setPair! nbr6 (baseA + 2) (baseC + 0)
  let nbr8 := setPair! nbr7 (baseA + 3) (baseB + 0)
  let nbr := setPair! nbr8 (baseB + 2) (baseC + 1)
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hsizeG : g.arcNbr.size = m := by
    simpa [m] using PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg0
  have hnbr0_size : nbr0.size = m + 12 := by
    simp [nbr0, hsizeG, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hnbr8_size : nbr8.size = m + 12 := by
    simp [nbr8, nbr7, nbr6, setPair!_size, hnbr0_size]
  have hi : baseB + 2 < nbr8.size := by
    have : m + 6 < m + 12 := Nat.add_lt_add_left (by decide : (6 : Nat) < 12) m
    simpa [hnbr8_size, baseB, Nat.add_assoc] using this
  have hj : baseC + 1 < nbr8.size := by
    have : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
    simpa [hnbr8_size, baseC, Nat.add_assoc] using this
  have hval : nbr[baseC + 1]! = baseB + 2 := by
    simpa [nbr] using (setPair!_getBang_right nbr8 (baseB + 2) (baseC + 1) hi hj)
  have hnbr : r3BraidLeftNbr g x u w = nbr := by rfl
  -- `baseC+1 = m+9` and `baseB+2 = m+6`.
  simpa [r3BraidLeftGraph, hnbr, baseB, baseC, Nat.add_assoc] using hval

private theorem arcNbr_r3BraidLeft_baseC0
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    (r3BraidLeftGraph g x u w).arcNbr[m + 8]! = m + 2 := by
  classical
  let m := g.numHalfEdges
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
  let nbr6 :=
    setPair!
      (setPair!
        (setPair!
          (setPair!
            (setPair!
              (setPair! nbr0 x (baseA + 0)) u (baseA + 1))
            w (baseB + 1))
          x2 (baseB + 3))
        w2 (baseC + 2))
      u2 (baseC + 3)
  let nbr7 := setPair! nbr6 (baseA + 2) (baseC + 0)
  let nbr8 := setPair! nbr7 (baseA + 3) (baseB + 0)
  let nbr := setPair! nbr8 (baseB + 2) (baseC + 1)
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hsizeG : g.arcNbr.size = m := by
    simpa [m] using PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg0
  have hnbr0_size : nbr0.size = m + 12 := by
    simp [nbr0, hsizeG, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hnbr6_size : nbr6.size = m + 12 := by
    simp [nbr6, setPair!_size, hnbr0_size]
  have hi7 : baseA + 2 < nbr6.size := by
    have : m + 2 < m + 12 := Nat.add_lt_add_left (by decide : (2 : Nat) < 12) m
    simpa [hnbr6_size, baseA, Nat.add_assoc] using this
  have hj7 : baseC + 0 < nbr6.size := by
    have : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
    simpa [hnbr6_size, baseC, Nat.add_assoc] using this
  have h7 : nbr7[baseC + 0]! = baseA + 2 := by
    simpa [nbr7] using (setPair!_getBang_right nbr6 (baseA + 2) (baseC + 0) hi7 hj7)
  have hk8 : baseC + 0 < nbr7.size := by
    simpa [nbr7, setPair!_size, hnbr6_size] using hj7
  have hi8 : baseA + 3 < nbr7.size := by
    have : m + 3 < m + 12 := Nat.add_lt_add_left (by decide : (3 : Nat) < 12) m
    simpa [nbr7, setPair!_size, hnbr6_size, baseA, Nat.add_assoc] using this
  have hj8 : baseB + 0 < nbr7.size := by
    have : m + 4 < m + 12 := Nat.add_lt_add_left (by decide : (4 : Nat) < 12) m
    simpa [nbr7, setPair!_size, hnbr6_size, baseB, Nat.add_assoc] using this
  have hki8 : baseC + 0 ≠ baseA + 3 := by
    exact Nat.ne_of_gt (by
      have : (m + 3 : Nat) < m + 8 := Nat.add_lt_add_left (by decide : (3 : Nat) < 8) m
      simpa [baseA, baseC, Nat.add_assoc] using this)
  have hkj8 : baseC + 0 ≠ baseB + 0 := by
    exact Nat.ne_of_gt (by
      have : (m + 4 : Nat) < m + 8 := Nat.add_lt_add_left (by decide : (4 : Nat) < 8) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have h8 : nbr8[baseC + 0]! = nbr7[baseC + 0]! := by
    simpa [nbr8] using
      (setPair!_getBang_ne nbr7 (baseA + 3) (baseB + 0) (baseC + 0) hi8 hj8 hk8 hki8 hkj8)
  have hk9 : baseC + 0 < nbr8.size := by
    simpa [nbr8, nbr7, setPair!_size, hnbr6_size] using hj7
  have hi9 : baseB + 2 < nbr8.size := by
    have : m + 6 < m + 12 := Nat.add_lt_add_left (by decide : (6 : Nat) < 12) m
    simpa [nbr8, nbr7, setPair!_size, hnbr6_size, baseB, Nat.add_assoc] using this
  have hj9 : baseC + 1 < nbr8.size := by
    have : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
    simpa [nbr8, nbr7, setPair!_size, hnbr6_size, baseC, Nat.add_assoc] using this
  have hki9 : baseC + 0 ≠ baseB + 2 := by
    exact Nat.ne_of_gt (by
      have : (m + 6 : Nat) < m + 8 := Nat.add_lt_add_left (by decide : (6 : Nat) < 8) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have hkj9 : baseC + 0 ≠ baseC + 1 := by
    exact Nat.ne_of_lt (by
      have : (0 : Nat) < 1 := by decide
      simpa [baseC, Nat.add_assoc] using Nat.add_lt_add_left this m)
  have h9 : nbr[baseC + 0]! = nbr8[baseC + 0]! := by
    simpa [nbr] using
      (setPair!_getBang_ne nbr8 (baseB + 2) (baseC + 1) (baseC + 0) hi9 hj9 hk9 hki9 hkj9)
  have hnbr : r3BraidLeftNbr g x u w = nbr := by rfl
  have hval : nbr[baseC + 0]! = baseA + 2 := by
    calc
      nbr[baseC + 0]! = nbr8[baseC + 0]! := h9
      _ = nbr7[baseC + 0]! := h8
      _ = baseA + 2 := h7
  -- `baseC+0 = m+8` and `baseA+2 = m+2`.
  simpa [r3BraidLeftGraph, hnbr, baseA, baseC, Nat.add_assoc] using hval

private theorem r3BraidLeftGraph_valid_of_ok
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    PDGraph.Valid (r3BraidLeftGraph g x u w) := by
  classical
  have hValid : PDGraph.Valid gL := by
    simpa using (r3BraidLeft_valid (g := g) (gL := gL) (x := x) (u := u) (w := w) h)
  have hg : gL = r3BraidLeftGraph g x u w := by
    simpa [r3BraidLeftGraph, r3BraidLeftNbr] using
      (r3BraidLeft_eq_gOut (g := g) (gL := gL) (x := x) (u := u) (w := w) h)
  simpa [hg] using hValid

private theorem arcNbr_r3BraidLeft_baseC2
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    let w2 := g.arcNbr[w]!
    (r3BraidLeftGraph g x u w).arcNbr[m + 10]! = w2 := by
  classical
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  let m := g.numHalfEdges
  have hw : w < m :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.2
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  have hw2_lt : w2 < m := PDGraph.Valid.get_lt hValidG (i := w) hw
  have hu : u < m :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.1
  have hu2_lt : u2 < m := PDGraph.Valid.get_lt hValidG (i := u) hu
  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
  let nbr4 :=
    setPair!
      (setPair!
        (setPair!
          (setPair! nbr0 x (baseA + 0)) u (baseA + 1))
        w (baseB + 1))
      x2 (baseB + 3)
  let nbr5 := setPair! nbr4 w2 (baseC + 2)
  let nbr6 := setPair! nbr5 u2 (baseC + 3)
  let nbr7 := setPair! nbr6 (baseA + 2) (baseC + 0)
  let nbr8 := setPair! nbr7 (baseA + 3) (baseB + 0)
  let nbr := setPair! nbr8 (baseB + 2) (baseC + 1)
  have hsizeG : g.arcNbr.size = m := by
    simpa [m] using PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg0
  have hnbr0_size : nbr0.size = m + 12 := by
    simp [nbr0, hsizeG, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hnbr4_size : nbr4.size = m + 12 := by
    simp [nbr4, setPair!_size, hnbr0_size]
  have hw2_lt_nbr4 : w2 < nbr4.size := by
    have : w2 < m + 12 := Nat.lt_of_lt_of_le hw2_lt (Nat.le_add_right m 12)
    simpa [hnbr4_size] using this
  have hbaseC2_lt_nbr4 : baseC + 2 < nbr4.size := by
    have : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
    simpa [baseC, hnbr4_size, Nat.add_assoc] using this
  have h5 : nbr5[baseC + 2]! = w2 := by
    simpa [nbr5] using (setPair!_getBang_right nbr4 w2 (baseC + 2) hw2_lt_nbr4 hbaseC2_lt_nbr4)
  have hnbr5_size : nbr5.size = m + 12 := by
    simp [nbr5, setPair!_size, hnbr4_size]
  have hnbr6_size : nbr6.size = m + 12 := by
    simp [nbr6, setPair!_size, hnbr5_size]
  have hnbr7_size : nbr7.size = m + 12 := by
    simp [nbr7, setPair!_size, hnbr6_size]
  have hnbr8_size : nbr8.size = m + 12 := by
    simp [nbr8, setPair!_size, hnbr7_size]
  have hk5 : baseC + 2 < nbr5.size := by
    have : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
    simpa [baseC, hnbr5_size, Nat.add_assoc] using this
  have hk6 : baseC + 2 < nbr6.size := by
    have : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
    simpa [baseC, hnbr6_size, Nat.add_assoc] using this
  have hk7 : baseC + 2 < nbr7.size := by
    have : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
    simpa [baseC, hnbr7_size, Nat.add_assoc] using this
  have hk8 : baseC + 2 < nbr8.size := by
    have : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
    simpa [baseC, hnbr8_size, Nat.add_assoc] using this
  have hu2_lt_nbr5 : u2 < nbr5.size := by
    have : u2 < m + 12 := Nat.lt_of_lt_of_le hu2_lt (Nat.le_add_right m 12)
    simpa [hnbr5_size] using this
  have hbaseC3_lt_nbr5 : baseC + 3 < nbr5.size := by
    have : m + 11 < m + 12 := Nat.add_lt_add_left (by decide : (11 : Nat) < 12) m
    simpa [baseC, hnbr5_size, Nat.add_assoc] using this
  have hki6 : baseC + 2 ≠ u2 := by
    -- `u2 < m` while `baseC+2 = m+10`.
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hu2_lt (by simpa [baseC, Nat.add_assoc] using Nat.le_add_right m 10))
  have hkj6 : baseC + 2 ≠ baseC + 3 := Nat.ne_of_lt (Nat.lt_succ_self (baseC + 2))
  have h6 : nbr6[baseC + 2]! = nbr5[baseC + 2]! := by
    simpa [nbr6] using
      (setPair!_getBang_ne nbr5 u2 (baseC + 3) (baseC + 2) hu2_lt_nbr5 hbaseC3_lt_nbr5 hk5 hki6 hkj6)
  have hi7 : baseA + 2 < nbr6.size := by
    have : m + 2 < m + 12 := Nat.add_lt_add_left (by decide : (2 : Nat) < 12) m
    simpa [baseA, hnbr6_size, Nat.add_assoc] using this
  have hj7 : baseC + 0 < nbr6.size := by
    have : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
    simpa [baseC, hnbr6_size, Nat.add_assoc] using this
  have hki7 : baseC + 2 ≠ baseA + 2 := by
    exact Nat.ne_of_gt (by
      have : (m + 2 : Nat) < m + 10 := Nat.add_lt_add_left (by decide : (2 : Nat) < 10) m
      simpa [baseA, baseC, Nat.add_assoc] using this)
  have hkj7 : baseC + 2 ≠ baseC + 0 := by
    exact Nat.ne_of_gt (by
      have : (0 : Nat) < 2 := by decide
      simpa [baseC, Nat.add_assoc] using Nat.add_lt_add_left this m)
  have h7 : nbr7[baseC + 2]! = nbr6[baseC + 2]! := by
    simpa [nbr7] using (setPair!_getBang_ne nbr6 (baseA + 2) (baseC + 0) (baseC + 2) hi7 hj7 hk6 hki7 hkj7)
  have hi8 : baseA + 3 < nbr7.size := by
    have : m + 3 < m + 12 := Nat.add_lt_add_left (by decide : (3 : Nat) < 12) m
    simpa [baseA, hnbr7_size, Nat.add_assoc] using this
  have hj8 : baseB + 0 < nbr7.size := by
    have : m + 4 < m + 12 := Nat.add_lt_add_left (by decide : (4 : Nat) < 12) m
    simpa [baseB, hnbr7_size, Nat.add_assoc] using this
  have hki8 : baseC + 2 ≠ baseA + 3 := by
    exact Nat.ne_of_gt (by
      have : (m + 3 : Nat) < m + 10 := Nat.add_lt_add_left (by decide : (3 : Nat) < 10) m
      simpa [baseA, baseC, Nat.add_assoc] using this)
  have hkj8 : baseC + 2 ≠ baseB + 0 := by
    exact Nat.ne_of_gt (by
      have : (m + 4 : Nat) < m + 10 := Nat.add_lt_add_left (by decide : (4 : Nat) < 10) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have h8 : nbr8[baseC + 2]! = nbr7[baseC + 2]! := by
    simpa [nbr8] using (setPair!_getBang_ne nbr7 (baseA + 3) (baseB + 0) (baseC + 2) hi8 hj8 hk7 hki8 hkj8)
  have hi9 : baseB + 2 < nbr8.size := by
    have : m + 6 < m + 12 := Nat.add_lt_add_left (by decide : (6 : Nat) < 12) m
    simpa [baseB, hnbr8_size, Nat.add_assoc] using this
  have hj9 : baseC + 1 < nbr8.size := by
    have : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
    simpa [baseC, hnbr8_size, Nat.add_assoc] using this
  have hki9 : baseC + 2 ≠ baseB + 2 := by
    exact Nat.ne_of_gt (by
      have : (m + 6 : Nat) < m + 10 := Nat.add_lt_add_left (by decide : (6 : Nat) < 10) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have hkj9 : baseC + 2 ≠ baseC + 1 := by
    exact Nat.ne_of_gt (by
      have : (1 : Nat) < 2 := by decide
      simpa [baseC, Nat.add_assoc] using Nat.add_lt_add_left this m)
  have h9 : nbr[baseC + 2]! = nbr8[baseC + 2]! := by
    simpa [nbr] using (setPair!_getBang_ne nbr8 (baseB + 2) (baseC + 1) (baseC + 2) hi9 hj9 hk8 hki9 hkj9)
  have hnbr : r3BraidLeftNbr g x u w = nbr := by rfl
  have hFinal : nbr[baseC + 2]! = w2 := by
    calc
      nbr[baseC + 2]! = nbr8[baseC + 2]! := h9
      _ = nbr7[baseC + 2]! := h8
      _ = nbr6[baseC + 2]! := h7
      _ = nbr5[baseC + 2]! := h6
      _ = w2 := h5
  -- `baseC+2 = m+10`.
  simpa [r3BraidLeftGraph, hnbr, baseC, Nat.add_assoc] using hFinal

private theorem arcNbr_r3BraidLeft_baseC3
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    let u2 := g.arcNbr[u]!
    (r3BraidLeftGraph g x u w).arcNbr[m + 11]! = u2 := by
  classical
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  let m := g.numHalfEdges
  have hu : u < m :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.1
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  have hu2_lt : u2 < m := PDGraph.Valid.get_lt hValidG (i := u) hu
  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
  let nbr4 :=
    setPair!
      (setPair!
        (setPair!
          (setPair! nbr0 x (baseA + 0)) u (baseA + 1))
        w (baseB + 1))
      x2 (baseB + 3)
  let nbr5 := setPair! nbr4 w2 (baseC + 2)
  let nbr6 := setPair! nbr5 u2 (baseC + 3)
  let nbr7 := setPair! nbr6 (baseA + 2) (baseC + 0)
  let nbr8 := setPair! nbr7 (baseA + 3) (baseB + 0)
  let nbr := setPair! nbr8 (baseB + 2) (baseC + 1)
  have hsizeG : g.arcNbr.size = m := by
    simpa [m] using PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg0
  have hnbr0_size : nbr0.size = m + 12 := by
    simp [nbr0, hsizeG, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hnbr4_size : nbr4.size = m + 12 := by
    simp [nbr4, setPair!_size, hnbr0_size]
  have hnbr5_size : nbr5.size = m + 12 := by
    simp [nbr5, setPair!_size, hnbr4_size]
  have hu2_lt_nbr5 : u2 < nbr5.size := by
    have : u2 < m + 12 := Nat.lt_of_lt_of_le hu2_lt (Nat.le_add_right m 12)
    simpa [hnbr5_size] using this
  have hbaseC3_lt_nbr5 : baseC + 3 < nbr5.size := by
    have : m + 11 < m + 12 := Nat.add_lt_add_left (by decide : (11 : Nat) < 12) m
    simpa [baseC, hnbr5_size, Nat.add_assoc] using this
  have h6 : nbr6[baseC + 3]! = u2 := by
    simpa [nbr6] using (setPair!_getBang_right nbr5 u2 (baseC + 3) hu2_lt_nbr5 hbaseC3_lt_nbr5)
  have hnbr6_size : nbr6.size = m + 12 := by
    simp [nbr6, setPair!_size, hnbr5_size]
  have hnbr7_size : nbr7.size = m + 12 := by
    simp [nbr7, setPair!_size, hnbr6_size]
  have hnbr8_size : nbr8.size = m + 12 := by
    simp [nbr8, setPair!_size, hnbr7_size]
  have hk6 : baseC + 3 < nbr6.size := by
    have : m + 11 < m + 12 := Nat.add_lt_add_left (by decide : (11 : Nat) < 12) m
    simpa [baseC, hnbr6_size, Nat.add_assoc] using this
  have hk7 : baseC + 3 < nbr7.size := by
    have : m + 11 < m + 12 := Nat.add_lt_add_left (by decide : (11 : Nat) < 12) m
    simpa [baseC, hnbr7_size, Nat.add_assoc] using this
  have hk8 : baseC + 3 < nbr8.size := by
    have : m + 11 < m + 12 := Nat.add_lt_add_left (by decide : (11 : Nat) < 12) m
    simpa [baseC, hnbr8_size, Nat.add_assoc] using this
  have hi7 : baseA + 2 < nbr6.size := by
    have : m + 2 < m + 12 := Nat.add_lt_add_left (by decide : (2 : Nat) < 12) m
    simpa [baseA, hnbr6_size, Nat.add_assoc] using this
  have hj7 : baseC + 0 < nbr6.size := by
    have : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
    simpa [baseC, hnbr6_size, Nat.add_assoc] using this
  have hki7 : baseC + 3 ≠ baseA + 2 := by
    exact Nat.ne_of_gt (by
      have : (m + 2 : Nat) < m + 11 := Nat.add_lt_add_left (by decide : (2 : Nat) < 11) m
      simpa [baseA, baseC, Nat.add_assoc] using this)
  have hkj7 : baseC + 3 ≠ baseC + 0 := by
    exact Nat.ne_of_gt (by
      have : (0 : Nat) < 3 := by decide
      simpa [baseC, Nat.add_assoc] using Nat.add_lt_add_left this m)
  have h7 : nbr7[baseC + 3]! = nbr6[baseC + 3]! := by
    simpa [nbr7] using (setPair!_getBang_ne nbr6 (baseA + 2) (baseC + 0) (baseC + 3) hi7 hj7 hk6 hki7 hkj7)
  have hi8 : baseA + 3 < nbr7.size := by
    have : m + 3 < m + 12 := Nat.add_lt_add_left (by decide : (3 : Nat) < 12) m
    simpa [baseA, hnbr7_size, Nat.add_assoc] using this
  have hj8 : baseB + 0 < nbr7.size := by
    have : m + 4 < m + 12 := Nat.add_lt_add_left (by decide : (4 : Nat) < 12) m
    simpa [baseB, hnbr7_size, Nat.add_assoc] using this
  have hki8 : baseC + 3 ≠ baseA + 3 := by
    exact Nat.ne_of_gt (by
      have : (m + 3 : Nat) < m + 11 := Nat.add_lt_add_left (by decide : (3 : Nat) < 11) m
      simpa [baseA, baseC, Nat.add_assoc] using this)
  have hkj8 : baseC + 3 ≠ baseB + 0 := by
    exact Nat.ne_of_gt (by
      have : (m + 4 : Nat) < m + 11 := Nat.add_lt_add_left (by decide : (4 : Nat) < 11) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have h8 : nbr8[baseC + 3]! = nbr7[baseC + 3]! := by
    simpa [nbr8] using (setPair!_getBang_ne nbr7 (baseA + 3) (baseB + 0) (baseC + 3) hi8 hj8 hk7 hki8 hkj8)
  have hi9 : baseB + 2 < nbr8.size := by
    have : m + 6 < m + 12 := Nat.add_lt_add_left (by decide : (6 : Nat) < 12) m
    simpa [baseB, hnbr8_size, Nat.add_assoc] using this
  have hj9 : baseC + 1 < nbr8.size := by
    have : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
    simpa [baseC, hnbr8_size, Nat.add_assoc] using this
  have hki9 : baseC + 3 ≠ baseB + 2 := by
    exact Nat.ne_of_gt (by
      have : (m + 6 : Nat) < m + 11 := Nat.add_lt_add_left (by decide : (6 : Nat) < 11) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have hkj9 : baseC + 3 ≠ baseC + 1 := by
    exact Nat.ne_of_gt (by
      have : (1 : Nat) < 3 := by decide
      simpa [baseC, Nat.add_assoc] using Nat.add_lt_add_left this m)
  have h9 : nbr[baseC + 3]! = nbr8[baseC + 3]! := by
    simpa [nbr] using (setPair!_getBang_ne nbr8 (baseB + 2) (baseC + 1) (baseC + 3) hi9 hj9 hk8 hki9 hkj9)
  have hnbr : r3BraidLeftNbr g x u w = nbr := by rfl
  have hFinal : nbr[baseC + 3]! = u2 := by
    calc
      nbr[baseC + 3]! = nbr8[baseC + 3]! := h9
      _ = nbr7[baseC + 3]! := h8
      _ = nbr6[baseC + 3]! := h7
      _ = u2 := by simpa [h6] using h6
  -- `baseC+3 = m+11`.
  simpa [r3BraidLeftGraph, hnbr, baseC, Nat.add_assoc] using hFinal

private theorem arcNbr_r3BraidLeft_w2
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    let w2 := g.arcNbr[w]!
    (r3BraidLeftGraph g x u w).arcNbr[w2]! = m + 10 := by
  classical
  let m := g.numHalfEdges
  let w2 := g.arcNbr[w]!
  have hValid : PDGraph.Valid (r3BraidLeftGraph g x u w) :=
    r3BraidLeftGraph_valid_of_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hi : m + 10 < (r3BraidLeftGraph g x u w).numHalfEdges := by
    -- `numHalfEdges = 4*(g.n+3) = m+12`.
    dsimp [r3BraidLeftGraph, PDGraph.numHalfEdges, m]
    have : (10 : Nat) < 12 := by decide
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.add_lt_add_left this (4 * g.n)
  have hC2 : (r3BraidLeftGraph g x u w).arcNbr[m + 10]! = w2 :=
    arcNbr_r3BraidLeft_baseC2 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  -- Involutivity at `m+10`.
  have := PDGraph.Valid.invol hValid (i := m + 10) hi
  simpa [hC2, w2, m] using this

private theorem arcNbr_r3BraidLeft_u2
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    let u2 := g.arcNbr[u]!
    (r3BraidLeftGraph g x u w).arcNbr[u2]! = m + 11 := by
  classical
  let m := g.numHalfEdges
  let u2 := g.arcNbr[u]!
  have hValid : PDGraph.Valid (r3BraidLeftGraph g x u w) :=
    r3BraidLeftGraph_valid_of_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hi : m + 11 < (r3BraidLeftGraph g x u w).numHalfEdges := by
    dsimp [r3BraidLeftGraph, PDGraph.numHalfEdges, m]
    have : (11 : Nat) < 12 := by decide
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.add_lt_add_left this (4 * g.n)
  have hC3 : (r3BraidLeftGraph g x u w).arcNbr[m + 11]! = u2 :=
    arcNbr_r3BraidLeft_baseC3 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have := PDGraph.Valid.invol hValid (i := m + 11) hi
  simpa [hC3, u2, m] using this

private lemma smoothLastCoreML_rewire_getBang
    (n : Nat) (arcNbr : Array Nat) (isB : Bool)
    (i : Nat) (hi : i < (4 * n - 4)) :
    (smoothLastCoreML_rewire n arcNbr isB)[i]! =
      let base := (4 * n) - 4
      let p := arcNbr[i]!
      if p < base then
        p
      else
        smoothLastCoreML_exitFromExternal n arcNbr isB i := by
  classical
  have hiArr : i < (smoothLastCoreML_rewire n arcNbr isB).size := by
    simpa [smoothLastCoreML_rewire] using hi
  calc
    (smoothLastCoreML_rewire n arcNbr isB)[i]! =
        (smoothLastCoreML_rewire n arcNbr isB)[i]'hiArr := by
          simpa using (getBang_eq_getElem (a := smoothLastCoreML_rewire n arcNbr isB) (i := i) hiArr)
    _ = (let base := (4 * n) - 4
        let p := arcNbr[i]!
        if p < base then p else smoothLastCoreML_exitFromExternal n arcNbr isB i) := by
        simp [smoothLastCoreML_rewire]

private lemma smoothLastCoreML_exitFromExternal_eq_of_y_lt_base
    (n : Nat) (arcNbr : Array Nat) (isB : Bool)
    (x r : Nat) (hr : arcNbr[x]! = r)
    (hy : arcNbr[smoothLastCoreML_smooth n isB r]! < (4 * n - 4)) :
    smoothLastCoreML_exitFromExternal n arcNbr isB x =
      arcNbr[smoothLastCoreML_smooth n isB r]! := by
  -- The braid gadgets have no loops inside the removed region, so we exit on the first step.
  simp [smoothLastCoreML_exitFromExternal, smoothLastCoreML_exitFromExternalAux, hr, hy]

private theorem smoothLastCoreML_rewire_r3BraidLeft_baseA2_baseB2_A
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    let nbrA := smoothLastCoreML_rewire (g.n + 3) (r3BraidLeftGraph g x u w).arcNbr false
    nbrA[m + 2]! = m + 6 ∧ nbrA[m + 6]! = m + 2 := by
  classical
  let m := g.numHalfEdges
  let nB : Nat := g.n + 3
  let arcNbr := (r3BraidLeftGraph g x u w).arcNbr
  have hbase : (4 * nB) - 4 = m + 8 := by
    dsimp [nB, m, PDGraph.numHalfEdges]
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using baseC_eq g.n
  have hm2_lt : m + 2 < (4 * nB - 4) := by
    have : m + 2 < m + 8 := Nat.add_lt_add_left (by decide : (2 : Nat) < 8) m
    simpa [hbase] using this
  have hm6_lt : m + 6 < (4 * nB - 4) := by
    have : m + 6 < m + 8 := Nat.add_lt_add_left (by decide : (6 : Nat) < 8) m
    simpa [hbase] using this
  let nbrA := smoothLastCoreML_rewire nB arcNbr false
  have hA2 : (r3BraidLeftGraph g x u w).arcNbr[m + 2]! = m + 8 :=
    arcNbr_r3BraidLeft_baseA2 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hB2 : (r3BraidLeftGraph g x u w).arcNbr[m + 6]! = m + 9 :=
    arcNbr_r3BraidLeft_baseB2 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hC0 : (r3BraidLeftGraph g x u w).arcNbr[m + 8]! = m + 2 :=
    arcNbr_r3BraidLeft_baseC0 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hC1 : (r3BraidLeftGraph g x u w).arcNbr[m + 9]! = m + 6 :=
    arcNbr_r3BraidLeft_baseC1 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hrew_m2 : nbrA[m + 2]! = m + 6 := by
    have hsm : smoothLastCoreML_smooth nB false (m + 8) = m + 9 := by
      have hm0 : m % 4 = 0 := by
        dsimp [m, PDGraph.numHalfEdges]
        simp
      have hmod : (m + 8) % 4 = 0 := by
        calc
          (m + 8) % 4 = ((m % 4) + (8 % 4)) % 4 := by
            simpa [Nat.add_mod]
          _ = 0 := by simp [hm0]
      -- `pos = 0` gives `base+1`.
      simp [smoothLastCoreML_smooth, hbase, hmod]
    have hy : arcNbr[smoothLastCoreML_smooth nB false (m + 8)]! < (4 * nB - 4) := by
      have harc : arcNbr[m + 9]! = m + 6 := by
        simpa [arcNbr] using hC1
      have : m + 6 < m + 8 := Nat.add_lt_add_left (by decide : (6 : Nat) < 8) m
      simpa [hsm, hbase, harc] using this
    have hexit :
        smoothLastCoreML_exitFromExternal nB arcNbr false (m + 2) =
          arcNbr[smoothLastCoreML_smooth nB false (m + 8)]! := by
      simpa [hsm] using
        (smoothLastCoreML_exitFromExternal_eq_of_y_lt_base (n := nB) (arcNbr := arcNbr) (isB := false)
          (x := m + 2) (r := m + 8) (hr := by simpa [arcNbr] using hA2) hy)
    have hnot : ¬((r3BraidLeftGraph g x u w).arcNbr[m + 2]! < (4 * nB - 4)) := by
      simpa [hA2, hbase]
    have : nbrA[m + 2]! = smoothLastCoreML_exitFromExternal nB arcNbr false (m + 2) := by
      simpa [nbrA, arcNbr, hnot] using smoothLastCoreML_rewire_getBang nB arcNbr false (m + 2) hm2_lt
    calc
      nbrA[m + 2]! = smoothLastCoreML_exitFromExternal nB arcNbr false (m + 2) := this
      _ = arcNbr[smoothLastCoreML_smooth nB false (m + 8)]! := hexit
      _ = m + 6 := by simpa [hsm] using hC1
  have hrew_m6 : nbrA[m + 6]! = m + 2 := by
    have hsm : smoothLastCoreML_smooth nB false (m + 9) = m + 8 := by
      have hm0 : m % 4 = 0 := by
        dsimp [m, PDGraph.numHalfEdges]
        simp
      have hmod : (m + 9) % 4 = 1 := by
        calc
          (m + 9) % 4 = ((m % 4) + (9 % 4)) % 4 := by
            simpa [Nat.add_mod]
          _ = 1 := by simp [hm0]
      -- `pos = 1` gives `base+0`.
      simp [smoothLastCoreML_smooth, hbase, hmod]
    have hy : arcNbr[smoothLastCoreML_smooth nB false (m + 9)]! < (4 * nB - 4) := by
      have harc : arcNbr[m + 8]! = m + 2 := by
        simpa [arcNbr] using hC0
      have : m + 2 < m + 8 := Nat.add_lt_add_left (by decide : (2 : Nat) < 8) m
      simpa [hsm, hbase, harc] using this
    have hexit :
        smoothLastCoreML_exitFromExternal nB arcNbr false (m + 6) =
          arcNbr[smoothLastCoreML_smooth nB false (m + 9)]! := by
      simpa [hsm] using
        (smoothLastCoreML_exitFromExternal_eq_of_y_lt_base (n := nB) (arcNbr := arcNbr) (isB := false)
          (x := m + 6) (r := m + 9) (hr := by simpa [arcNbr] using hB2) hy)
    have hnot : ¬((r3BraidLeftGraph g x u w).arcNbr[m + 6]! < (4 * nB - 4)) := by
      simpa [hB2, hbase]
    have : nbrA[m + 6]! = smoothLastCoreML_exitFromExternal nB arcNbr false (m + 6) := by
      simpa [nbrA, arcNbr, hnot] using smoothLastCoreML_rewire_getBang nB arcNbr false (m + 6) hm6_lt
    calc
      nbrA[m + 6]! = smoothLastCoreML_exitFromExternal nB arcNbr false (m + 6) := this
      _ = arcNbr[smoothLastCoreML_smooth nB false (m + 9)]! := hexit
      _ = m + 2 := by simpa [hsm] using hC0
  exact ⟨hrew_m2, hrew_m6⟩

private theorem smoothLastCoreML_rewire_r3BraidLeft_u2_w2_A
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let u2 := g.arcNbr[u]!
    let w2 := g.arcNbr[w]!
    let nbrA := smoothLastCoreML_rewire (g.n + 3) (r3BraidLeftGraph g x u w).arcNbr false
    nbrA[u2]! = w2 ∧ nbrA[w2]! = u2 := by
  classical
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  let m := g.numHalfEdges
  have hu : u < m :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.1
  have hw : w < m :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.2
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  have hu2_lt : u2 < m := PDGraph.Valid.get_lt hValidG (i := u) hu
  have hw2_lt : w2 < m := PDGraph.Valid.get_lt hValidG (i := w) hw
  let nB : Nat := g.n + 3
  let arcNbr := (r3BraidLeftGraph g x u w).arcNbr
  have hbase : (4 * nB) - 4 = m + 8 := by
    dsimp [nB, m, PDGraph.numHalfEdges]
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using baseC_eq g.n
  have hu2_lt_base : u2 < (4 * nB - 4) := by
    have : u2 < m + 8 := Nat.lt_of_lt_of_le hu2_lt (Nat.le_add_right m 8)
    simpa [hbase] using this
  have hw2_lt_base : w2 < (4 * nB - 4) := by
    have : w2 < m + 8 := Nat.lt_of_lt_of_le hw2_lt (Nat.le_add_right m 8)
    simpa [hbase] using this
  let nbrA := smoothLastCoreML_rewire nB arcNbr false
  have hU : (r3BraidLeftGraph g x u w).arcNbr[u2]! = m + 11 :=
    arcNbr_r3BraidLeft_u2 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hW : (r3BraidLeftGraph g x u w).arcNbr[w2]! = m + 10 :=
    arcNbr_r3BraidLeft_w2 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hC2 : (r3BraidLeftGraph g x u w).arcNbr[m + 10]! = w2 :=
    arcNbr_r3BraidLeft_baseC2 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hC3 : (r3BraidLeftGraph g x u w).arcNbr[m + 11]! = u2 :=
    arcNbr_r3BraidLeft_baseC3 (g := g) (gL := gL) (x := x) (u := u) (w := w) h

  have hrew_u2 : nbrA[u2]! = w2 := by
    have hsm : smoothLastCoreML_smooth nB false (m + 11) = m + 10 := by
      have hm0 : m % 4 = 0 := by
        dsimp [m, PDGraph.numHalfEdges]
        simp
      have hmod : (m + 11) % 4 = 3 := by
        calc
          (m + 11) % 4 = ((m % 4) + (11 % 4)) % 4 := by simpa [Nat.add_mod]
          _ = 3 := by simp [hm0]
      -- `pos = 3` gives `base+2`.
      simp [smoothLastCoreML_smooth, hbase, hmod]
    have hy : arcNbr[smoothLastCoreML_smooth nB false (m + 11)]! < (4 * nB - 4) := by
      have harc : arcNbr[m + 10]! = w2 := by simpa [arcNbr] using hC2
      have : w2 < m + 8 := Nat.lt_of_lt_of_le hw2_lt (Nat.le_add_right m 8)
      simpa [hsm, hbase, harc] using this
    have hexit :
        smoothLastCoreML_exitFromExternal nB arcNbr false u2 =
          arcNbr[smoothLastCoreML_smooth nB false (m + 11)]! := by
      simpa [hsm] using
        (smoothLastCoreML_exitFromExternal_eq_of_y_lt_base (n := nB) (arcNbr := arcNbr) (isB := false)
          (x := u2) (r := m + 11) (hr := by simpa [arcNbr] using hU) hy)
    have hnot : ¬((r3BraidLeftGraph g x u w).arcNbr[u2]! < (4 * nB - 4)) := by
      simpa [hU, hbase]
    have : nbrA[u2]! = smoothLastCoreML_exitFromExternal nB arcNbr false u2 := by
      simpa [nbrA, arcNbr, hnot] using smoothLastCoreML_rewire_getBang nB arcNbr false u2 hu2_lt_base
    calc
      nbrA[u2]! = smoothLastCoreML_exitFromExternal nB arcNbr false u2 := this
      _ = arcNbr[smoothLastCoreML_smooth nB false (m + 11)]! := hexit
      _ = w2 := by simpa [hsm] using hC2

  have hrew_w2 : nbrA[w2]! = u2 := by
    have hsm : smoothLastCoreML_smooth nB false (m + 10) = m + 11 := by
      have hm0 : m % 4 = 0 := by
        dsimp [m, PDGraph.numHalfEdges]
        simp
      have hmod : (m + 10) % 4 = 2 := by
        calc
          (m + 10) % 4 = ((m % 4) + (10 % 4)) % 4 := by simpa [Nat.add_mod]
          _ = 2 := by simp [hm0]
      -- `pos = 2` gives `base+3`.
      simp [smoothLastCoreML_smooth, hbase, hmod]
    have hy : arcNbr[smoothLastCoreML_smooth nB false (m + 10)]! < (4 * nB - 4) := by
      have harc : arcNbr[m + 11]! = u2 := by simpa [arcNbr] using hC3
      have : u2 < m + 8 := Nat.lt_of_lt_of_le hu2_lt (Nat.le_add_right m 8)
      simpa [hsm, hbase, harc] using this
    have hexit :
        smoothLastCoreML_exitFromExternal nB arcNbr false w2 =
          arcNbr[smoothLastCoreML_smooth nB false (m + 10)]! := by
      simpa [hsm] using
        (smoothLastCoreML_exitFromExternal_eq_of_y_lt_base (n := nB) (arcNbr := arcNbr) (isB := false)
          (x := w2) (r := m + 10) (hr := by simpa [arcNbr] using hW) hy)
    have hnot : ¬((r3BraidLeftGraph g x u w).arcNbr[w2]! < (4 * nB - 4)) := by
      simpa [hW, hbase]
    have : nbrA[w2]! = smoothLastCoreML_exitFromExternal nB arcNbr false w2 := by
      simpa [nbrA, arcNbr, hnot] using smoothLastCoreML_rewire_getBang nB arcNbr false w2 hw2_lt_base
    calc
      nbrA[w2]! = smoothLastCoreML_exitFromExternal nB arcNbr false w2 := this
      _ = arcNbr[smoothLastCoreML_smooth nB false (m + 10)]! := hexit
      _ = u2 := by simpa [hsm] using hC3

  exact ⟨hrew_u2, hrew_w2⟩

private theorem smoothLastCoreML_rewire_r3BraidLeft_boundary_A
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    let u2 := g.arcNbr[u]!
    let w2 := g.arcNbr[w]!
    let nbrA := smoothLastCoreML_rewire (g.n + 3) (r3BraidLeftGraph g x u w).arcNbr false
    nbrA[m + 2]! = m + 6 ∧ nbrA[m + 6]! = m + 2 ∧ nbrA[u2]! = w2 ∧ nbrA[w2]! = u2 := by
  rcases smoothLastCoreML_rewire_r3BraidLeft_baseA2_baseB2_A
      (g := g) (gL := gL) (x := x) (u := u) (w := w) h with ⟨hA2, hB2⟩
  rcases smoothLastCoreML_rewire_r3BraidLeft_u2_w2_A
      (g := g) (gL := gL) (x := x) (u := u) (w := w) h with ⟨hU2, hW2⟩
  exact ⟨hA2, hB2, hU2, hW2⟩

private theorem smoothLastCoreML_rewire_r3BraidLeft_boundary_B
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    let u2 := g.arcNbr[u]!
    let w2 := g.arcNbr[w]!
    let nbrB := smoothLastCoreML_rewire (g.n + 3) (r3BraidLeftGraph g x u w).arcNbr true
    nbrB[m + 2]! = u2 ∧ nbrB[u2]! = m + 2 ∧ nbrB[m + 6]! = w2 ∧ nbrB[w2]! = m + 6 := by
  classical
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  let m := g.numHalfEdges
  have hu : u < m :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.1
  have hw : w < m :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.2
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  have hu2_lt : u2 < m := PDGraph.Valid.get_lt hValidG (i := u) hu
  have hw2_lt : w2 < m := PDGraph.Valid.get_lt hValidG (i := w) hw
  let nB : Nat := g.n + 3
  let arcNbr := (r3BraidLeftGraph g x u w).arcNbr
  have hbase : (4 * nB) - 4 = m + 8 := by
    dsimp [nB, m, PDGraph.numHalfEdges]
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using baseC_eq g.n
  let nbrB := smoothLastCoreML_rewire nB arcNbr true
  have hm2_lt_base : m + 2 < (4 * nB - 4) := by
    have : m + 2 < m + 8 := Nat.add_lt_add_left (by decide : (2 : Nat) < 8) m
    simpa [hbase] using this
  have hm6_lt_base : m + 6 < (4 * nB - 4) := by
    have : m + 6 < m + 8 := Nat.add_lt_add_left (by decide : (6 : Nat) < 8) m
    simpa [hbase] using this
  have hu2_lt_base : u2 < (4 * nB - 4) := by
    have : u2 < m + 8 := Nat.lt_of_lt_of_le hu2_lt (Nat.le_add_right m 8)
    simpa [hbase] using this
  have hw2_lt_base : w2 < (4 * nB - 4) := by
    have : w2 < m + 8 := Nat.lt_of_lt_of_le hw2_lt (Nat.le_add_right m 8)
    simpa [hbase] using this
  have hA2 : (r3BraidLeftGraph g x u w).arcNbr[m + 2]! = m + 8 :=
    arcNbr_r3BraidLeft_baseA2 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hB2 : (r3BraidLeftGraph g x u w).arcNbr[m + 6]! = m + 9 :=
    arcNbr_r3BraidLeft_baseB2 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hC0 : (r3BraidLeftGraph g x u w).arcNbr[m + 8]! = m + 2 :=
    arcNbr_r3BraidLeft_baseC0 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hC1 : (r3BraidLeftGraph g x u w).arcNbr[m + 9]! = m + 6 :=
    arcNbr_r3BraidLeft_baseC1 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hC2 : (r3BraidLeftGraph g x u w).arcNbr[m + 10]! = w2 :=
    arcNbr_r3BraidLeft_baseC2 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hC3 : (r3BraidLeftGraph g x u w).arcNbr[m + 11]! = u2 :=
    arcNbr_r3BraidLeft_baseC3 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hU : (r3BraidLeftGraph g x u w).arcNbr[u2]! = m + 11 :=
    arcNbr_r3BraidLeft_u2 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hW : (r3BraidLeftGraph g x u w).arcNbr[w2]! = m + 10 :=
    arcNbr_r3BraidLeft_w2 (g := g) (gL := gL) (x := x) (u := u) (w := w) h

  have hm0 : m % 4 = 0 := by
    dsimp [m, PDGraph.numHalfEdges]
    simp

  have hsm8 : smoothLastCoreML_smooth nB true (m + 8) = m + 11 := by
    have hmod : (m + 8) % 4 = 0 := by
      calc
        (m + 8) % 4 = ((m % 4) + (8 % 4)) % 4 := by simpa [Nat.add_mod]
        _ = 0 := by simp [hm0]
    simp [smoothLastCoreML_smooth, hbase, hmod]

  have hsm11 : smoothLastCoreML_smooth nB true (m + 11) = m + 8 := by
    have hmod : (m + 11) % 4 = 3 := by
      calc
        (m + 11) % 4 = ((m % 4) + (11 % 4)) % 4 := by simpa [Nat.add_mod]
        _ = 3 := by simp [hm0]
    simp [smoothLastCoreML_smooth, hbase, hmod]

  have hsm9 : smoothLastCoreML_smooth nB true (m + 9) = m + 10 := by
    have hmod : (m + 9) % 4 = 1 := by
      calc
        (m + 9) % 4 = ((m % 4) + (9 % 4)) % 4 := by simpa [Nat.add_mod]
        _ = 1 := by simp [hm0]
    simp [smoothLastCoreML_smooth, hbase, hmod]

  have hsm10 : smoothLastCoreML_smooth nB true (m + 10) = m + 9 := by
    have hmod : (m + 10) % 4 = 2 := by
      calc
        (m + 10) % 4 = ((m % 4) + (10 % 4)) % 4 := by simpa [Nat.add_mod]
        _ = 2 := by simp [hm0]
    simp [smoothLastCoreML_smooth, hbase, hmod]

  have hrew_m2 : nbrB[m + 2]! = u2 := by
    have hy : arcNbr[smoothLastCoreML_smooth nB true (m + 8)]! < (4 * nB - 4) := by
      have harc : arcNbr[m + 11]! = u2 := by simpa [arcNbr] using hC3
      have : u2 < m + 8 := Nat.lt_of_lt_of_le hu2_lt (Nat.le_add_right m 8)
      simpa [hsm8, hbase, harc] using this
    have hexit :
        smoothLastCoreML_exitFromExternal nB arcNbr true (m + 2) =
          arcNbr[smoothLastCoreML_smooth nB true (m + 8)]! := by
      simpa [hsm8] using
        (smoothLastCoreML_exitFromExternal_eq_of_y_lt_base (n := nB) (arcNbr := arcNbr) (isB := true)
          (x := m + 2) (r := m + 8) (hr := by simpa [arcNbr] using hA2) hy)
    have hnot : ¬((r3BraidLeftGraph g x u w).arcNbr[m + 2]! < (4 * nB - 4)) := by
      simpa [hA2, hbase]
    have : nbrB[m + 2]! = smoothLastCoreML_exitFromExternal nB arcNbr true (m + 2) := by
      simpa [nbrB, arcNbr, hnot] using smoothLastCoreML_rewire_getBang nB arcNbr true (m + 2) hm2_lt_base
    calc
      nbrB[m + 2]! = smoothLastCoreML_exitFromExternal nB arcNbr true (m + 2) := this
      _ = arcNbr[smoothLastCoreML_smooth nB true (m + 8)]! := hexit
      _ = u2 := by simpa [hsm8] using hC3

  have hrew_u2 : nbrB[u2]! = m + 2 := by
    have hy : arcNbr[smoothLastCoreML_smooth nB true (m + 11)]! < (4 * nB - 4) := by
      have harc : arcNbr[m + 8]! = m + 2 := by simpa [arcNbr] using hC0
      have : m + 2 < m + 8 := Nat.add_lt_add_left (by decide : (2 : Nat) < 8) m
      simpa [hsm11, hbase, harc] using this
    have hexit :
        smoothLastCoreML_exitFromExternal nB arcNbr true u2 =
          arcNbr[smoothLastCoreML_smooth nB true (m + 11)]! := by
      simpa [hsm11] using
        (smoothLastCoreML_exitFromExternal_eq_of_y_lt_base (n := nB) (arcNbr := arcNbr) (isB := true)
          (x := u2) (r := m + 11) (hr := by simpa [arcNbr] using hU) hy)
    have hnot : ¬((r3BraidLeftGraph g x u w).arcNbr[u2]! < (4 * nB - 4)) := by
      simpa [hU, hbase]
    have : nbrB[u2]! = smoothLastCoreML_exitFromExternal nB arcNbr true u2 := by
      simpa [nbrB, arcNbr, hnot] using smoothLastCoreML_rewire_getBang nB arcNbr true u2 hu2_lt_base
    calc
      nbrB[u2]! = smoothLastCoreML_exitFromExternal nB arcNbr true u2 := this
      _ = arcNbr[smoothLastCoreML_smooth nB true (m + 11)]! := hexit
      _ = m + 2 := by simpa [hsm11] using hC0

  have hrew_m6 : nbrB[m + 6]! = w2 := by
    have hy : arcNbr[smoothLastCoreML_smooth nB true (m + 9)]! < (4 * nB - 4) := by
      have harc : arcNbr[m + 10]! = w2 := by simpa [arcNbr] using hC2
      have : w2 < m + 8 := Nat.lt_of_lt_of_le hw2_lt (Nat.le_add_right m 8)
      simpa [hsm9, hbase, harc] using this
    have hexit :
        smoothLastCoreML_exitFromExternal nB arcNbr true (m + 6) =
          arcNbr[smoothLastCoreML_smooth nB true (m + 9)]! := by
      simpa [hsm9] using
        (smoothLastCoreML_exitFromExternal_eq_of_y_lt_base (n := nB) (arcNbr := arcNbr) (isB := true)
          (x := m + 6) (r := m + 9) (hr := by simpa [arcNbr] using hB2) hy)
    have hnot : ¬((r3BraidLeftGraph g x u w).arcNbr[m + 6]! < (4 * nB - 4)) := by
      simpa [hB2, hbase]
    have : nbrB[m + 6]! = smoothLastCoreML_exitFromExternal nB arcNbr true (m + 6) := by
      simpa [nbrB, arcNbr, hnot] using smoothLastCoreML_rewire_getBang nB arcNbr true (m + 6) hm6_lt_base
    calc
      nbrB[m + 6]! = smoothLastCoreML_exitFromExternal nB arcNbr true (m + 6) := this
      _ = arcNbr[smoothLastCoreML_smooth nB true (m + 9)]! := hexit
      _ = w2 := by simpa [hsm9] using hC2

  have hrew_w2 : nbrB[w2]! = m + 6 := by
    have hy : arcNbr[smoothLastCoreML_smooth nB true (m + 10)]! < (4 * nB - 4) := by
      have harc : arcNbr[m + 9]! = m + 6 := by simpa [arcNbr] using hC1
      have : m + 6 < m + 8 := Nat.add_lt_add_left (by decide : (6 : Nat) < 8) m
      simpa [hsm10, hbase, harc] using this
    have hexit :
        smoothLastCoreML_exitFromExternal nB arcNbr true w2 =
          arcNbr[smoothLastCoreML_smooth nB true (m + 10)]! := by
      simpa [hsm10] using
        (smoothLastCoreML_exitFromExternal_eq_of_y_lt_base (n := nB) (arcNbr := arcNbr) (isB := true)
          (x := w2) (r := m + 10) (hr := by simpa [arcNbr] using hW) hy)
    have hnot : ¬((r3BraidLeftGraph g x u w).arcNbr[w2]! < (4 * nB - 4)) := by
      simpa [hW, hbase]
    have : nbrB[w2]! = smoothLastCoreML_exitFromExternal nB arcNbr true w2 := by
      simpa [nbrB, arcNbr, hnot] using smoothLastCoreML_rewire_getBang nB arcNbr true w2 hw2_lt_base
    calc
      nbrB[w2]! = smoothLastCoreML_exitFromExternal nB arcNbr true w2 := this
      _ = arcNbr[smoothLastCoreML_smooth nB true (m + 10)]! := hexit
      _ = m + 6 := by simpa [hsm10] using hC1

  exact ⟨hrew_m2, hrew_u2, hrew_m6, hrew_w2⟩

private theorem smoothLastCoreML_rewire_r3BraidLeft_step1_signature
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    let u2 := g.arcNbr[u]!
    let w2 := g.arcNbr[w]!
    let nbrA := smoothLastCoreML_rewire (g.n + 3) (r3BraidLeftGraph g x u w).arcNbr false
    let nbrB := smoothLastCoreML_rewire (g.n + 3) (r3BraidLeftGraph g x u w).arcNbr true
    (nbrA[m + 2]! = m + 6 ∧ nbrA[m + 6]! = m + 2 ∧ nbrA[u2]! = w2 ∧ nbrA[w2]! = u2) ∧
      (nbrB[m + 2]! = u2 ∧ nbrB[u2]! = m + 2 ∧ nbrB[m + 6]! = w2 ∧ nbrB[w2]! = m + 6) := by
  exact ⟨smoothLastCoreML_rewire_r3BraidLeft_boundary_A
      (g := g) (gL := gL) (x := x) (u := u) (w := w) h,
    smoothLastCoreML_rewire_r3BraidLeft_boundary_B
      (g := g) (gL := gL) (x := x) (u := u) (w := w) h⟩

/-!
### Bridge step 1 (right gadget): explicit smoothing rewires on the last crossing

For the right braid gadget `σ₂σ₁σ₂`, the last crossing is still the final block `baseC = m+8`.
Its incident external endpoints are `(m+3)`, `(m+7)`, `u2`, and `x2`.
-/

private theorem r3BraidRightGraph_valid_of_ok
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    PDGraph.Valid (r3BraidRightGraph g x u w) := by
  classical
  have hValid : PDGraph.Valid gR := by
    simpa using (r3BraidRight_valid (g := g) (gR := gR) (x := x) (u := u) (w := w) h)
  have hg : gR = r3BraidRightGraph g x u w := by
    simpa [r3BraidRightGraph, r3BraidRightNbr] using
      (r3BraidRight_eq_gOut (g := g) (gR := gR) (x := x) (u := u) (w := w) h)
  simpa [hg] using hValid

private theorem arcNbr_r3BraidRight_baseC0
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    (r3BraidRightGraph g x u w).arcNbr[m + 8]! = m + 7 := by
  classical
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  let m := g.numHalfEdges
  have hsizeG : g.arcNbr.size = m := by
    simpa [m] using PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg0
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
  let nbr1 := setPair! nbr0 u (baseA + 0)
  let nbr2 := setPair! nbr1 w (baseA + 1)
  let nbr3 := setPair! nbr2 x (baseB + 0)
  let nbr4 := setPair! nbr3 w2 (baseB + 2)
  let nbr5 := setPair! nbr4 u2 (baseC + 2)
  let nbr6 := setPair! nbr5 x2 (baseC + 3)
  let nbr7 := setPair! nbr6 (baseA + 2) (baseB + 1)
  let nbr8 := setPair! nbr7 (baseB + 3) (baseC + 0)
  let nbr := setPair! nbr8 (baseA + 3) (baseC + 1)
  have hnbr0_size : nbr0.size = m + 12 := by
    simp [nbr0, hsizeG, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hnbr1_size : nbr1.size = m + 12 := by
    simp [nbr1, setPair!_size, hnbr0_size]
  have hnbr2_size : nbr2.size = m + 12 := by
    simp [nbr2, setPair!_size, hnbr1_size]
  have hnbr3_size : nbr3.size = m + 12 := by
    simp [nbr3, setPair!_size, hnbr2_size]
  have hnbr4_size : nbr4.size = m + 12 := by
    simp [nbr4, setPair!_size, hnbr3_size]
  have hnbr5_size : nbr5.size = m + 12 := by
    simp [nbr5, setPair!_size, hnbr4_size]
  have hnbr6_size : nbr6.size = m + 12 := by
    simp [nbr6, setPair!_size, hnbr5_size]
  have hnbr7_size : nbr7.size = m + 12 := by
    simp [nbr7, setPair!_size, hnbr6_size]
  have hnbr8_size : nbr8.size = m + 12 := by
    simp [nbr8, setPair!_size, hnbr7_size]
  have hi : baseB + 3 < nbr7.size := by
    have : m + 7 < m + 12 := Nat.add_lt_add_left (by decide : (7 : Nat) < 12) m
    simpa [baseB, hnbr7_size, Nat.add_assoc] using this
  have hj : baseC + 0 < nbr7.size := by
    have : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
    simpa [baseC, hnbr7_size, Nat.add_assoc] using this
  have hij : baseB + 3 ≠ baseC + 0 := by
    have : (m + 7 : Nat) < m + 8 := Nat.add_lt_add_left (by decide : (7 : Nat) < 8) m
    exact Nat.ne_of_lt (by simpa [baseB, baseC, Nat.add_assoc] using this)
  have h8 : nbr8[baseC + 0]! = baseB + 3 := by
    simpa [nbr8] using (setPair!_getBang_right nbr7 (baseB + 3) (baseC + 0) hi hj)
  have hk : baseC + 0 < nbr8.size := by
    have : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
    simpa [baseC, hnbr8_size, Nat.add_assoc] using this
  have hi9 : baseA + 3 < nbr8.size := by
    have : m + 3 < m + 12 := Nat.add_lt_add_left (by decide : (3 : Nat) < 12) m
    simpa [baseA, hnbr8_size, Nat.add_assoc] using this
  have hj9 : baseC + 1 < nbr8.size := by
    have : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
    simpa [baseC, hnbr8_size, Nat.add_assoc] using this
  have hki : baseC + 0 ≠ baseA + 3 := by
    have hlt : baseA + 3 < baseC + 0 := by
      have : (m + 3 : Nat) < m + 8 := Nat.add_lt_add_left (by decide : (3 : Nat) < 8) m
      simpa [baseA, baseC, Nat.add_assoc] using this
    exact (Nat.ne_of_lt hlt).symm
  have hkj : baseC + 0 ≠ baseC + 1 := by
    exact Nat.ne_of_lt (Nat.lt_succ_self (baseC + 0))
  have h9 : nbr[baseC + 0]! = nbr8[baseC + 0]! := by
    simpa [nbr] using
      (setPair!_getBang_ne nbr8 (baseA + 3) (baseC + 1) (baseC + 0) hi9 hj9 hk hki hkj)
  have hnbr : r3BraidRightNbr g x u w = nbr := by rfl
  have hFinal : nbr[baseC + 0]! = baseB + 3 := by
    calc
      nbr[baseC + 0]! = nbr8[baseC + 0]! := h9
      _ = baseB + 3 := h8
  -- `baseC+0 = m+8` and `baseB+3 = m+7`.
  simpa [r3BraidRightGraph, hnbr, baseB, baseC, Nat.add_assoc] using hFinal

private theorem arcNbr_r3BraidRight_baseC1
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    (r3BraidRightGraph g x u w).arcNbr[m + 9]! = m + 3 := by
  classical
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  let m := g.numHalfEdges
  have hsizeG : g.arcNbr.size = m := by
    simpa [m] using PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg0
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
  let nbr1 := setPair! nbr0 u (baseA + 0)
  let nbr2 := setPair! nbr1 w (baseA + 1)
  let nbr3 := setPair! nbr2 x (baseB + 0)
  let nbr4 := setPair! nbr3 w2 (baseB + 2)
  let nbr5 := setPair! nbr4 u2 (baseC + 2)
  let nbr6 := setPair! nbr5 x2 (baseC + 3)
  let nbr7 := setPair! nbr6 (baseA + 2) (baseB + 1)
  let nbr8 := setPair! nbr7 (baseB + 3) (baseC + 0)
  let nbr := setPair! nbr8 (baseA + 3) (baseC + 1)
  have hnbr0_size : nbr0.size = m + 12 := by
    simp [nbr0, hsizeG, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hnbr1_size : nbr1.size = m + 12 := by
    simp [nbr1, setPair!_size, hnbr0_size]
  have hnbr2_size : nbr2.size = m + 12 := by
    simp [nbr2, setPair!_size, hnbr1_size]
  have hnbr3_size : nbr3.size = m + 12 := by
    simp [nbr3, setPair!_size, hnbr2_size]
  have hnbr4_size : nbr4.size = m + 12 := by
    simp [nbr4, setPair!_size, hnbr3_size]
  have hnbr5_size : nbr5.size = m + 12 := by
    simp [nbr5, setPair!_size, hnbr4_size]
  have hnbr6_size : nbr6.size = m + 12 := by
    simp [nbr6, setPair!_size, hnbr5_size]
  have hnbr7_size : nbr7.size = m + 12 := by
    simp [nbr7, setPair!_size, hnbr6_size]
  have hnbr8_size : nbr8.size = m + 12 := by
    simp [nbr8, setPair!_size, hnbr7_size]
  have hi : baseA + 3 < nbr8.size := by
    have : m + 3 < m + 12 := Nat.add_lt_add_left (by decide : (3 : Nat) < 12) m
    simpa [baseA, hnbr8_size, Nat.add_assoc] using this
  have hj : baseC + 1 < nbr8.size := by
    have : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
    simpa [baseC, hnbr8_size, Nat.add_assoc] using this
  have hij : baseA + 3 ≠ baseC + 1 := by
    have : (m + 3 : Nat) < m + 9 := Nat.add_lt_add_left (by decide : (3 : Nat) < 9) m
    exact Nat.ne_of_lt (by simpa [baseA, baseC, Nat.add_assoc] using this)
  have hval : nbr[baseC + 1]! = baseA + 3 := by
    simpa [nbr] using (setPair!_getBang_right nbr8 (baseA + 3) (baseC + 1) hi hj)
  have hnbr : r3BraidRightNbr g x u w = nbr := by rfl
  -- `baseC+1 = m+9` and `baseA+3 = m+3`.
  simpa [r3BraidRightGraph, hnbr, baseA, baseC, Nat.add_assoc] using hval

private theorem arcNbr_r3BraidRight_baseC2
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    let u2 := g.arcNbr[u]!
    (r3BraidRightGraph g x u w).arcNbr[m + 10]! = u2 := by
  classical
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  let m := g.numHalfEdges
  have hsizeG : g.arcNbr.size = m := by
    simpa [m] using PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg0
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
  let nbr1 := setPair! nbr0 u (baseA + 0)
  let nbr2 := setPair! nbr1 w (baseA + 1)
  let nbr3 := setPair! nbr2 x (baseB + 0)
  let nbr4 := setPair! nbr3 w2 (baseB + 2)
  let nbr5 := setPair! nbr4 u2 (baseC + 2)
  let nbr6 := setPair! nbr5 x2 (baseC + 3)
  let nbr7 := setPair! nbr6 (baseA + 2) (baseB + 1)
  let nbr8 := setPair! nbr7 (baseB + 3) (baseC + 0)
  let nbr := setPair! nbr8 (baseA + 3) (baseC + 1)
  have hnbr0_size : nbr0.size = m + 12 := by
    simp [nbr0, hsizeG, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hnbr1_size : nbr1.size = m + 12 := by
    simp [nbr1, setPair!_size, hnbr0_size]
  have hnbr2_size : nbr2.size = m + 12 := by
    simp [nbr2, setPair!_size, hnbr1_size]
  have hnbr3_size : nbr3.size = m + 12 := by
    simp [nbr3, setPair!_size, hnbr2_size]
  have hnbr4_size : nbr4.size = m + 12 := by
    simp [nbr4, setPair!_size, hnbr3_size]
  have hu2_lt : u2 < nbr4.size := by
    have hu : u < m :=
      (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.1
    have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
    have hu2_lt_m : u2 < m := PDGraph.Valid.get_lt hValidG (i := u) hu
    have : u2 < m + 12 := Nat.lt_of_lt_of_le hu2_lt_m (Nat.le_add_right m 12)
    simpa [hnbr4_size] using this
  have hbaseC2_lt : baseC + 2 < nbr4.size := by
    have : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
    simpa [baseC, hnbr4_size, Nat.add_assoc] using this
  have h5 : nbr5[baseC + 2]! = u2 := by
    simpa [nbr5] using (setPair!_getBang_right nbr4 u2 (baseC + 2) hu2_lt hbaseC2_lt)
  have hnbr5_size : nbr5.size = m + 12 := by
    simp [nbr5, setPair!_size, hnbr4_size]
  have hnbr6_size : nbr6.size = m + 12 := by
    simp [nbr6, setPair!_size, hnbr5_size]
  have hnbr7_size : nbr7.size = m + 12 := by
    simp [nbr7, setPair!_size, hnbr6_size]
  have hnbr8_size : nbr8.size = m + 12 := by
    simp [nbr8, setPair!_size, hnbr7_size]
  have hi9 : baseC + 2 < nbr8.size := by
    have : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
    simpa [baseC, hnbr8_size, Nat.add_assoc] using this
  have hi10 : baseA + 3 < nbr8.size := by
    have : m + 3 < m + 12 := Nat.add_lt_add_left (by decide : (3 : Nat) < 12) m
    simpa [baseA, hnbr8_size, Nat.add_assoc] using this
  have hj10 : baseC + 1 < nbr8.size := by
    have : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
    simpa [baseC, hnbr8_size, Nat.add_assoc] using this
  have hki10 : baseC + 2 ≠ baseA + 3 := by
    have hlt : baseA + 3 < baseC + 2 := by
      have : (m + 3 : Nat) < m + 10 := Nat.add_lt_add_left (by decide : (3 : Nat) < 10) m
      simpa [baseA, baseC, Nat.add_assoc] using this
    exact (Nat.ne_of_lt hlt).symm
  have hkj10 : baseC + 2 ≠ baseC + 1 := by
    have : (m + 9 : Nat) < m + 10 := Nat.add_lt_add_left (by decide : (9 : Nat) < 10) m
    exact Nat.ne_of_gt (by simpa [baseC, Nat.add_assoc] using this)
  have h10 : nbr[baseC + 2]! = nbr8[baseC + 2]! := by
    simpa [nbr] using (setPair!_getBang_ne nbr8 (baseA + 3) (baseC + 1) (baseC + 2) hi10 hj10 hi9 hki10 hkj10)
  have hi11 : baseB + 3 < nbr7.size := by
    have : m + 7 < m + 12 := Nat.add_lt_add_left (by decide : (7 : Nat) < 12) m
    simpa [baseB, hnbr7_size, Nat.add_assoc] using this
  have hj11 : baseC + 0 < nbr7.size := by
    have : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
    simpa [baseC, hnbr7_size, Nat.add_assoc] using this
  have hk8 : baseC + 2 < nbr7.size := by
    have : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
    simpa [baseC, hnbr7_size, Nat.add_assoc] using this
  have hki11 : baseC + 2 ≠ baseB + 3 := by
    have hlt : baseB + 3 < baseC + 2 := by
      have : (m + 7 : Nat) < m + 10 := Nat.add_lt_add_left (by decide : (7 : Nat) < 10) m
      simpa [baseB, baseC, Nat.add_assoc] using this
    exact (Nat.ne_of_lt hlt).symm
  have hkj11 : baseC + 2 ≠ baseC + 0 := by
    exact Nat.ne_of_gt (by
      have : (m + 8 : Nat) < m + 10 := Nat.add_lt_add_left (by decide : (8 : Nat) < 10) m
      simpa [baseC, Nat.add_assoc] using this)
  have h11 : nbr8[baseC + 2]! = nbr7[baseC + 2]! := by
    simpa [nbr8] using (setPair!_getBang_ne nbr7 (baseB + 3) (baseC + 0) (baseC + 2) hi11 hj11 hk8 hki11 hkj11)
  have hi7 : baseA + 2 < nbr6.size := by
    have : m + 2 < m + 12 := Nat.add_lt_add_left (by decide : (2 : Nat) < 12) m
    simpa [baseA, hnbr6_size, Nat.add_assoc] using this
  have hj7 : baseB + 1 < nbr6.size := by
    have : m + 5 < m + 12 := Nat.add_lt_add_left (by decide : (5 : Nat) < 12) m
    simpa [baseB, hnbr6_size, Nat.add_assoc] using this
  have hk6 : baseC + 2 < nbr6.size := by
    have : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
    simpa [baseC, hnbr6_size, Nat.add_assoc] using this
  have hki7 : baseC + 2 ≠ baseA + 2 := by
    exact Nat.ne_of_gt (by
      have : (m + 2 : Nat) < m + 10 := Nat.add_lt_add_left (by decide : (2 : Nat) < 10) m
      simpa [baseA, baseC, Nat.add_assoc] using this)
  have hkj7 : baseC + 2 ≠ baseB + 1 := by
    exact Nat.ne_of_gt (by
      have : (m + 5 : Nat) < m + 10 := Nat.add_lt_add_left (by decide : (5 : Nat) < 10) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have h7 : nbr7[baseC + 2]! = nbr6[baseC + 2]! := by
    simpa [nbr7] using (setPair!_getBang_ne nbr6 (baseA + 2) (baseB + 1) (baseC + 2) hi7 hj7 hk6 hki7 hkj7)
  have hx2_lt : x2 < nbr5.size := by
    have hx : x < m :=
      (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).1
    have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
    have hx2_lt_m : x2 < m := PDGraph.Valid.get_lt hValidG (i := x) hx
    have : x2 < m + 12 := Nat.lt_of_lt_of_le hx2_lt_m (Nat.le_add_right m 12)
    simpa [hnbr5_size] using this
  have hbaseC3_lt : baseC + 3 < nbr5.size := by
    have : m + 11 < m + 12 := Nat.add_lt_add_left (by decide : (11 : Nat) < 12) m
    simpa [baseC, hnbr5_size, Nat.add_assoc] using this
  have hk5 : baseC + 2 < nbr5.size := by
    have : m + 10 < m + 12 := Nat.add_lt_add_left (by decide : (10 : Nat) < 12) m
    simpa [baseC, hnbr5_size, Nat.add_assoc] using this
  have hki6 : baseC + 2 ≠ x2 := by
    have : x2 < m := by
      have hx : x < m :=
        (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).1
      have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
      exact PDGraph.Valid.get_lt hValidG (i := x) hx
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le this (by simpa [baseC, Nat.add_assoc] using Nat.le_add_right m 10))
  have hkj6 : baseC + 2 ≠ baseC + 3 := Nat.ne_of_lt (Nat.lt_succ_self (baseC + 2))
  have h6 : nbr6[baseC + 2]! = nbr5[baseC + 2]! := by
    simpa [nbr6] using (setPair!_getBang_ne nbr5 x2 (baseC + 3) (baseC + 2) hx2_lt hbaseC3_lt hk5 hki6 hkj6)
  have hnbr : r3BraidRightNbr g x u w = nbr := by rfl
  have hFinal : nbr[baseC + 2]! = u2 := by
    calc
      nbr[baseC + 2]! = nbr8[baseC + 2]! := h10
      _ = nbr7[baseC + 2]! := h11
      _ = nbr6[baseC + 2]! := h7
      _ = nbr5[baseC + 2]! := h6
      _ = u2 := h5
  -- `baseC+2 = m+10`.
  simpa [r3BraidRightGraph, hnbr, baseC, Nat.add_assoc] using hFinal

private theorem arcNbr_r3BraidRight_baseC3
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    let x2 := g.arcNbr[x]!
    (r3BraidRightGraph g x u w).arcNbr[m + 11]! = x2 := by
  classical
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  let m := g.numHalfEdges
  have hsizeG : g.arcNbr.size = m := by
    simpa [m] using PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg0
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
  let nbr1 := setPair! nbr0 u (baseA + 0)
  let nbr2 := setPair! nbr1 w (baseA + 1)
  let nbr3 := setPair! nbr2 x (baseB + 0)
  let nbr4 := setPair! nbr3 w2 (baseB + 2)
  let nbr5 := setPair! nbr4 u2 (baseC + 2)
  let nbr6 := setPair! nbr5 x2 (baseC + 3)
  let nbr7 := setPair! nbr6 (baseA + 2) (baseB + 1)
  let nbr8 := setPair! nbr7 (baseB + 3) (baseC + 0)
  let nbr := setPair! nbr8 (baseA + 3) (baseC + 1)
  have hnbr0_size : nbr0.size = m + 12 := by
    simp [nbr0, hsizeG, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hnbr1_size : nbr1.size = m + 12 := by
    simp [nbr1, setPair!_size, hnbr0_size]
  have hnbr2_size : nbr2.size = m + 12 := by
    simp [nbr2, setPair!_size, hnbr1_size]
  have hnbr3_size : nbr3.size = m + 12 := by
    simp [nbr3, setPair!_size, hnbr2_size]
  have hnbr4_size : nbr4.size = m + 12 := by
    simp [nbr4, setPair!_size, hnbr3_size]
  have hnbr5_size : nbr5.size = m + 12 := by
    simp [nbr5, setPair!_size, hnbr4_size]
  have hx2_lt : x2 < nbr5.size := by
    have hx : x < m :=
      (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).1
    have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
    have hx2_lt_m : x2 < m := PDGraph.Valid.get_lt hValidG (i := x) hx
    have : x2 < m + 12 := Nat.lt_of_lt_of_le hx2_lt_m (Nat.le_add_right m 12)
    simpa [hnbr5_size] using this
  have hbaseC3_lt : baseC + 3 < nbr5.size := by
    have : m + 11 < m + 12 := Nat.add_lt_add_left (by decide : (11 : Nat) < 12) m
    simpa [baseC, hnbr5_size, Nat.add_assoc] using this
  have hval : nbr6[baseC + 3]! = x2 := by
    simpa [nbr6] using (setPair!_getBang_right nbr5 x2 (baseC + 3) hx2_lt hbaseC3_lt)
  have hnbr6_size : nbr6.size = m + 12 := by
    simp [nbr6, setPair!_size, hnbr5_size]
  have hnbr7_size : nbr7.size = m + 12 := by
    simp [nbr7, setPair!_size, hnbr6_size]
  have hnbr8_size : nbr8.size = m + 12 := by
    simp [nbr8, setPair!_size, hnbr7_size]
  have hi7 : baseA + 2 < nbr6.size := by
    have : m + 2 < m + 12 := Nat.add_lt_add_left (by decide : (2 : Nat) < 12) m
    simpa [baseA, hnbr6_size, Nat.add_assoc] using this
  have hj7 : baseB + 1 < nbr6.size := by
    have : m + 5 < m + 12 := Nat.add_lt_add_left (by decide : (5 : Nat) < 12) m
    simpa [baseB, hnbr6_size, Nat.add_assoc] using this
  have hk6 : baseC + 3 < nbr6.size := by
    have : m + 11 < m + 12 := Nat.add_lt_add_left (by decide : (11 : Nat) < 12) m
    simpa [baseC, hnbr6_size, Nat.add_assoc] using this
  have hki7 : baseC + 3 ≠ baseA + 2 := by
    exact Nat.ne_of_gt (by
      have : (m + 2 : Nat) < m + 11 := Nat.add_lt_add_left (by decide : (2 : Nat) < 11) m
      simpa [baseA, baseC, Nat.add_assoc] using this)
  have hkj7 : baseC + 3 ≠ baseB + 1 := by
    exact Nat.ne_of_gt (by
      have : (m + 5 : Nat) < m + 11 := Nat.add_lt_add_left (by decide : (5 : Nat) < 11) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have h7 : nbr7[baseC + 3]! = nbr6[baseC + 3]! := by
    simpa [nbr7] using (setPair!_getBang_ne nbr6 (baseA + 2) (baseB + 1) (baseC + 3) hi7 hj7 hk6 hki7 hkj7)
  have hi8 : baseB + 3 < nbr7.size := by
    have : m + 7 < m + 12 := Nat.add_lt_add_left (by decide : (7 : Nat) < 12) m
    simpa [baseB, hnbr7_size, Nat.add_assoc] using this
  have hj8 : baseC + 0 < nbr7.size := by
    have : m + 8 < m + 12 := Nat.add_lt_add_left (by decide : (8 : Nat) < 12) m
    simpa [baseC, hnbr7_size, Nat.add_assoc] using this
  have hk7 : baseC + 3 < nbr7.size := by
    have : m + 11 < m + 12 := Nat.add_lt_add_left (by decide : (11 : Nat) < 12) m
    simpa [baseC, hnbr7_size, Nat.add_assoc] using this
  have hki8 : baseC + 3 ≠ baseB + 3 := by
    exact Nat.ne_of_gt (by
      have : (m + 7 : Nat) < m + 11 := Nat.add_lt_add_left (by decide : (7 : Nat) < 11) m
      simpa [baseB, baseC, Nat.add_assoc] using this)
  have hkj8 : baseC + 3 ≠ baseC + 0 := by
    exact Nat.ne_of_gt (by
      have : (m + 8 : Nat) < m + 11 := Nat.add_lt_add_left (by decide : (8 : Nat) < 11) m
      simpa [baseC, Nat.add_assoc] using this)
  have h8 : nbr8[baseC + 3]! = nbr7[baseC + 3]! := by
    simpa [nbr8] using (setPair!_getBang_ne nbr7 (baseB + 3) (baseC + 0) (baseC + 3) hi8 hj8 hk7 hki8 hkj8)
  have hi9 : baseA + 3 < nbr8.size := by
    have : m + 3 < m + 12 := Nat.add_lt_add_left (by decide : (3 : Nat) < 12) m
    simpa [baseA, hnbr8_size, Nat.add_assoc] using this
  have hj9 : baseC + 1 < nbr8.size := by
    have : m + 9 < m + 12 := Nat.add_lt_add_left (by decide : (9 : Nat) < 12) m
    simpa [baseC, hnbr8_size, Nat.add_assoc] using this
  have hk8 : baseC + 3 < nbr8.size := by
    have : m + 11 < m + 12 := Nat.add_lt_add_left (by decide : (11 : Nat) < 12) m
    simpa [baseC, hnbr8_size, Nat.add_assoc] using this
  have hki9 : baseC + 3 ≠ baseA + 3 := by
    exact Nat.ne_of_gt (by
      have : (m + 3 : Nat) < m + 11 := Nat.add_lt_add_left (by decide : (3 : Nat) < 11) m
      simpa [baseA, baseC, Nat.add_assoc] using this)
  have hkj9 : baseC + 3 ≠ baseC + 1 := by
    exact Nat.ne_of_gt (by
      have : (m + 9 : Nat) < m + 11 := Nat.add_lt_add_left (by decide : (9 : Nat) < 11) m
      simpa [baseC, Nat.add_assoc] using this)
  have h9 : nbr[baseC + 3]! = nbr8[baseC + 3]! := by
    simpa [nbr] using (setPair!_getBang_ne nbr8 (baseA + 3) (baseC + 1) (baseC + 3) hi9 hj9 hk8 hki9 hkj9)
  have hnbr : r3BraidRightNbr g x u w = nbr := by rfl
  have hFinal : nbr[baseC + 3]! = x2 := by
    calc
      nbr[baseC + 3]! = nbr8[baseC + 3]! := h9
      _ = nbr7[baseC + 3]! := h8
      _ = nbr6[baseC + 3]! := h7
      _ = x2 := by simpa using hval
  -- `baseC+3 = m+11`.
  simpa [r3BraidRightGraph, hnbr, baseC, Nat.add_assoc] using hFinal

private theorem arcNbr_r3BraidRight_baseB0
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    (r3BraidRightGraph g x u w).arcNbr[m + 4]! = x := by
  classical
  let m := g.numHalfEdges
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
  let nbr1 := setPair! nbr0 u (baseA + 0)
  let nbr2 := setPair! nbr1 w (baseA + 1)
  let nbr3 := setPair! nbr2 x (baseB + 0)
  let nbr4 := setPair! nbr3 w2 (baseB + 2)
  let nbr5 := setPair! nbr4 u2 (baseC + 2)
  let nbr6 := setPair! nbr5 x2 (baseC + 3)
  let nbr7 := setPair! nbr6 (baseA + 2) (baseB + 1)
  let nbr8 := setPair! nbr7 (baseB + 3) (baseC + 0)
  let nbr := setPair! nbr8 (baseA + 3) (baseC + 1)
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hx : x < m :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).1
  have hsizeG : g.arcNbr.size = m := by
    simpa [m] using PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg0
  have hnbr0_size : nbr0.size = m + 12 := by
    simp [nbr0, hsizeG, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hnbr1_size : nbr1.size = m + 12 := by
    simp [nbr1, setPair!_size, hnbr0_size]
  have hnbr2_size : nbr2.size = m + 12 := by
    simp [nbr2, setPair!_size, hnbr1_size]
  have hx_lt_nbr2 : x < nbr2.size := by
    have : x < m + 12 := Nat.lt_of_lt_of_le hx (Nat.le_add_right m 12)
    simpa [hnbr2_size] using this
  have hbaseB0_lt_nbr2 : baseB + 0 < nbr2.size := by
    have : m + 4 < m + 12 := by omega
    simpa [baseB, hnbr2_size, Nat.add_assoc] using this
  have h3 : nbr3[baseB + 0]! = x := by
    simpa [nbr3] using (setPair!_getBang_right nbr2 x (baseB + 0) hx_lt_nbr2 hbaseB0_lt_nbr2)
  have hnbr3_size : nbr3.size = m + 12 := by
    simp [nbr3, setPair!_size, hnbr2_size]
  have hk3 : baseB + 0 < nbr3.size := by
    have : m + 4 < m + 12 := by omega
    simpa [baseB, hnbr3_size, Nat.add_assoc] using this
  have h4 : nbr4[baseB + 0]! = nbr3[baseB + 0]! := by
    have hi : w2 < nbr3.size := by
      have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
      have hw : w < m :=
        (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.2
      have hw2 : w2 < m := PDGraph.Valid.get_lt hValidG (i := w) hw
      have : w2 < m + 12 := Nat.lt_of_lt_of_le hw2 (Nat.le_add_right m 12)
      simpa [hnbr3_size] using this
    have hj : baseB + 2 < nbr3.size := by
      have : m + 6 < m + 12 := by omega
      simpa [baseB, hnbr3_size, Nat.add_assoc] using this
    have hki : baseB + 0 ≠ w2 := by
      have : w2 < baseB + 0 := by
        have hm_le : m ≤ baseB + 0 := by
          simpa [baseB, Nat.add_assoc] using (Nat.le_add_right m 4)
        exact Nat.lt_of_lt_of_le (PDGraph.Valid.get_lt (PDGraph.valid_of_validate_eq_ok hvg0)
          (i := w) ((lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.2)) hm_le
      exact (Nat.ne_of_lt this).symm
    have hkj : baseB + 0 ≠ baseB + 2 := by omega
    simpa [nbr4] using (setPair!_getBang_ne nbr3 w2 (baseB + 2) (baseB + 0) hi hj hk3 hki hkj)
  have hnbr4_size : nbr4.size = m + 12 := by
    simp [nbr4, setPair!_size, hnbr3_size]
  have hk4 : baseB + 0 < nbr4.size := by
    have : m + 4 < m + 12 := by omega
    simpa [baseB, hnbr4_size, Nat.add_assoc] using this
  have h5 : nbr5[baseB + 0]! = nbr4[baseB + 0]! := by
    have hi : u2 < nbr4.size := by
      have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
      have hu : u < m :=
        (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.1
      have hu2 : u2 < m := PDGraph.Valid.get_lt hValidG (i := u) hu
      have : u2 < m + 12 := Nat.lt_of_lt_of_le hu2 (Nat.le_add_right m 12)
      simpa [hnbr4_size] using this
    have hj : baseC + 2 < nbr4.size := by
      have : m + 10 < m + 12 := by omega
      simpa [baseC, hnbr4_size, Nat.add_assoc] using this
    have hki : baseB + 0 ≠ u2 := by
      have : u2 < baseB + 0 := by
        have hm_le : m ≤ baseB + 0 := by
          simpa [baseB, Nat.add_assoc] using (Nat.le_add_right m 4)
        exact Nat.lt_of_lt_of_le (PDGraph.Valid.get_lt (PDGraph.valid_of_validate_eq_ok hvg0)
          (i := u) ((lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.1)) hm_le
      exact (Nat.ne_of_lt this).symm
    have hkj : baseB + 0 ≠ baseC + 2 := by omega
    simpa [nbr5] using (setPair!_getBang_ne nbr4 u2 (baseC + 2) (baseB + 0) hi hj hk4 hki hkj)
  have hnbr5_size : nbr5.size = m + 12 := by
    simp [nbr5, setPair!_size, hnbr4_size]
  have hk5 : baseB + 0 < nbr5.size := by
    have : m + 4 < m + 12 := by omega
    simpa [baseB, hnbr5_size, Nat.add_assoc] using this
  have h6 : nbr6[baseB + 0]! = nbr5[baseB + 0]! := by
    have hi : x2 < nbr5.size := by
      have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
      have hx2 : x2 < m := PDGraph.Valid.get_lt hValidG (i := x) hx
      have : x2 < m + 12 := Nat.lt_of_lt_of_le hx2 (Nat.le_add_right m 12)
      simpa [hnbr5_size] using this
    have hj : baseC + 3 < nbr5.size := by
      have : m + 11 < m + 12 := by omega
      simpa [baseC, hnbr5_size, Nat.add_assoc] using this
    have hki : baseB + 0 ≠ x2 := by
      have : x2 < baseB + 0 := by
        have hm_le : m ≤ baseB + 0 := by
          simpa [baseB, Nat.add_assoc] using (Nat.le_add_right m 4)
        exact Nat.lt_of_lt_of_le (PDGraph.Valid.get_lt (PDGraph.valid_of_validate_eq_ok hvg0) (i := x) hx) hm_le
      exact (Nat.ne_of_lt this).symm
    have hkj : baseB + 0 ≠ baseC + 3 := by omega
    simpa [nbr6] using (setPair!_getBang_ne nbr5 x2 (baseC + 3) (baseB + 0) hi hj hk5 hki hkj)
  have hnbr6_size : nbr6.size = m + 12 := by
    simp [nbr6, setPair!_size, hnbr5_size]
  have hk6 : baseB + 0 < nbr6.size := by
    have : m + 4 < m + 12 := by omega
    simpa [baseB, hnbr6_size, Nat.add_assoc] using this
  have h7 : nbr7[baseB + 0]! = nbr6[baseB + 0]! := by
    have hi : baseA + 2 < nbr6.size := by
      have : m + 2 < m + 12 := by omega
      simpa [baseA, hnbr6_size, Nat.add_assoc] using this
    have hj : baseB + 1 < nbr6.size := by
      have : m + 5 < m + 12 := by omega
      simpa [baseB, hnbr6_size, Nat.add_assoc] using this
    have hki : baseB + 0 ≠ baseA + 2 := by omega
    have hkj : baseB + 0 ≠ baseB + 1 := by omega
    simpa [nbr7] using (setPair!_getBang_ne nbr6 (baseA + 2) (baseB + 1) (baseB + 0) hi hj hk6 hki hkj)
  have hnbr7_size : nbr7.size = m + 12 := by
    simp [nbr7, setPair!_size, hnbr6_size]
  have hk7 : baseB + 0 < nbr7.size := by
    have : m + 4 < m + 12 := by omega
    simpa [baseB, hnbr7_size, Nat.add_assoc] using this
  have h8 : nbr8[baseB + 0]! = nbr7[baseB + 0]! := by
    have hi : baseB + 3 < nbr7.size := by
      have : m + 7 < m + 12 := by omega
      simpa [baseB, hnbr7_size, Nat.add_assoc] using this
    have hj : baseC + 0 < nbr7.size := by
      have : m + 8 < m + 12 := by omega
      simpa [baseC, hnbr7_size, Nat.add_assoc] using this
    have hki : baseB + 0 ≠ baseB + 3 := by omega
    have hkj : baseB + 0 ≠ baseC + 0 := by omega
    simpa [nbr8] using (setPair!_getBang_ne nbr7 (baseB + 3) (baseC + 0) (baseB + 0) hi hj hk7 hki hkj)
  have hnbr8_size : nbr8.size = m + 12 := by
    simp [nbr8, setPair!_size, hnbr7_size]
  have hk8 : baseB + 0 < nbr8.size := by
    have : m + 4 < m + 12 := by omega
    simpa [baseB, hnbr8_size, Nat.add_assoc] using this
  have h9 : nbr[baseB + 0]! = nbr8[baseB + 0]! := by
    have hi : baseA + 3 < nbr8.size := by
      have : m + 3 < m + 12 := by omega
      simpa [baseA, hnbr8_size, Nat.add_assoc] using this
    have hj : baseC + 1 < nbr8.size := by
      have : m + 9 < m + 12 := by omega
      simpa [baseC, hnbr8_size, Nat.add_assoc] using this
    have hki : baseB + 0 ≠ baseA + 3 := by omega
    have hkj : baseB + 0 ≠ baseC + 1 := by omega
    simpa [nbr] using (setPair!_getBang_ne nbr8 (baseA + 3) (baseC + 1) (baseB + 0) hi hj hk8 hki hkj)
  have hnbr : r3BraidRightNbr g x u w = nbr := by rfl
  have hFinal : nbr[baseB + 0]! = x := by
    calc
      nbr[baseB + 0]! = nbr8[baseB + 0]! := h9
      _ = nbr7[baseB + 0]! := h8
      _ = nbr6[baseB + 0]! := h7
      _ = nbr5[baseB + 0]! := h6
      _ = nbr4[baseB + 0]! := h5
      _ = nbr3[baseB + 0]! := h4
      _ = x := h3
  simpa [r3BraidRightGraph, hnbr, baseB, Nat.add_assoc] using hFinal

private theorem arcNbr_r3BraidRight_baseB2
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    let w2 := g.arcNbr[w]!
    (r3BraidRightGraph g x u w).arcNbr[m + 6]! = w2 := by
  classical
  let m := g.numHalfEdges
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  let baseA := m
  let baseB := m + 4
  let baseC := m + 8
  let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 12 0
  let nbr1 := setPair! nbr0 u (baseA + 0)
  let nbr2 := setPair! nbr1 w (baseA + 1)
  let nbr3 := setPair! nbr2 x (baseB + 0)
  let nbr4 := setPair! nbr3 w2 (baseB + 2)
  let nbr5 := setPair! nbr4 u2 (baseC + 2)
  let nbr6 := setPair! nbr5 x2 (baseC + 3)
  let nbr7 := setPair! nbr6 (baseA + 2) (baseB + 1)
  let nbr8 := setPair! nbr7 (baseB + 3) (baseC + 0)
  let nbr := setPair! nbr8 (baseA + 3) (baseC + 1)
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  have hw : w < m :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.2
  have hw2 : w2 < m := PDGraph.Valid.get_lt hValidG (i := w) hw
  have hsizeG : g.arcNbr.size = m := by
    simpa [m] using PDGraph.size_eq_numHalfEdges_of_validate_eq_ok (g := g) hvg0
  have hnbr0_size : nbr0.size = m + 12 := by
    simp [nbr0, hsizeG, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hnbr3_size : nbr3.size = m + 12 := by
    simp [nbr3, nbr2, nbr1, setPair!_size, hnbr0_size]
  have hw2_lt_nbr3 : w2 < nbr3.size := by
    have : w2 < m + 12 := Nat.lt_of_lt_of_le hw2 (Nat.le_add_right m 12)
    simpa [hnbr3_size] using this
  have hbaseB2_lt_nbr3 : baseB + 2 < nbr3.size := by
    have : m + 6 < m + 12 := by omega
    simpa [baseB, hnbr3_size, Nat.add_assoc] using this
  have h4 : nbr4[baseB + 2]! = w2 := by
    simpa [nbr4] using (setPair!_getBang_right nbr3 w2 (baseB + 2) hw2_lt_nbr3 hbaseB2_lt_nbr3)
  have hnbr4_size : nbr4.size = m + 12 := by
    simp [nbr4, setPair!_size, hnbr3_size]
  have hk4 : baseB + 2 < nbr4.size := by
    have : m + 6 < m + 12 := by omega
    simpa [baseB, hnbr4_size, Nat.add_assoc] using this
  have h5 : nbr5[baseB + 2]! = nbr4[baseB + 2]! := by
    have hi : u2 < nbr4.size := by
      have hu : u < m :=
        (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.1
      have hu2 : u2 < m := PDGraph.Valid.get_lt hValidG (i := u) hu
      have : u2 < m + 12 := Nat.lt_of_lt_of_le hu2 (Nat.le_add_right m 12)
      simpa [hnbr4_size] using this
    have hj : baseC + 2 < nbr4.size := by
      have : m + 10 < m + 12 := by omega
      simpa [baseC, hnbr4_size, Nat.add_assoc] using this
    have hki : baseB + 2 ≠ u2 := by
      have : u2 < baseB + 2 := by
        have hm_le : m ≤ baseB + 2 := by
          simpa [baseB, Nat.add_assoc] using (Nat.le_add_right m 6)
        exact Nat.lt_of_lt_of_le (PDGraph.Valid.get_lt hValidG
          (i := u) ((lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.1)) hm_le
      exact (Nat.ne_of_lt this).symm
    have hkj : baseB + 2 ≠ baseC + 2 := by omega
    simpa [nbr5] using (setPair!_getBang_ne nbr4 u2 (baseC + 2) (baseB + 2) hi hj hk4 hki hkj)
  have hnbr5_size : nbr5.size = m + 12 := by
    simp [nbr5, setPair!_size, hnbr4_size]
  have hk5 : baseB + 2 < nbr5.size := by
    have : m + 6 < m + 12 := by omega
    simpa [baseB, hnbr5_size, Nat.add_assoc] using this
  have h6 : nbr6[baseB + 2]! = nbr5[baseB + 2]! := by
    have hi : x2 < nbr5.size := by
      have hx : x < m :=
        (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).1
      have hx2 : x2 < m := PDGraph.Valid.get_lt hValidG (i := x) hx
      have : x2 < m + 12 := Nat.lt_of_lt_of_le hx2 (Nat.le_add_right m 12)
      simpa [hnbr5_size] using this
    have hj : baseC + 3 < nbr5.size := by
      have : m + 11 < m + 12 := by omega
      simpa [baseC, hnbr5_size, Nat.add_assoc] using this
    have hki : baseB + 2 ≠ x2 := by
      have : x2 < baseB + 2 := by
        have hm_le : m ≤ baseB + 2 := by
          simpa [baseB, Nat.add_assoc] using (Nat.le_add_right m 6)
        exact Nat.lt_of_lt_of_le (PDGraph.Valid.get_lt hValidG
          (i := x) ((lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).1)) hm_le
      exact (Nat.ne_of_lt this).symm
    have hkj : baseB + 2 ≠ baseC + 3 := by omega
    simpa [nbr6] using (setPair!_getBang_ne nbr5 x2 (baseC + 3) (baseB + 2) hi hj hk5 hki hkj)
  have hnbr6_size : nbr6.size = m + 12 := by
    simp [nbr6, setPair!_size, hnbr5_size]
  have hk6 : baseB + 2 < nbr6.size := by
    have : m + 6 < m + 12 := by omega
    simpa [baseB, hnbr6_size, Nat.add_assoc] using this
  have h7 : nbr7[baseB + 2]! = nbr6[baseB + 2]! := by
    have hi : baseA + 2 < nbr6.size := by
      have : m + 2 < m + 12 := by omega
      simpa [baseA, hnbr6_size, Nat.add_assoc] using this
    have hj : baseB + 1 < nbr6.size := by
      have : m + 5 < m + 12 := by omega
      simpa [baseB, hnbr6_size, Nat.add_assoc] using this
    have hki : baseB + 2 ≠ baseA + 2 := by omega
    have hkj : baseB + 2 ≠ baseB + 1 := by omega
    simpa [nbr7] using (setPair!_getBang_ne nbr6 (baseA + 2) (baseB + 1) (baseB + 2) hi hj hk6 hki hkj)
  have hnbr7_size : nbr7.size = m + 12 := by
    simp [nbr7, setPair!_size, hnbr6_size]
  have hk7 : baseB + 2 < nbr7.size := by
    have : m + 6 < m + 12 := by omega
    simpa [baseB, hnbr7_size, Nat.add_assoc] using this
  have h8 : nbr8[baseB + 2]! = nbr7[baseB + 2]! := by
    have hi : baseB + 3 < nbr7.size := by
      have : m + 7 < m + 12 := by omega
      simpa [baseB, hnbr7_size, Nat.add_assoc] using this
    have hj : baseC + 0 < nbr7.size := by
      have : m + 8 < m + 12 := by omega
      simpa [baseC, hnbr7_size, Nat.add_assoc] using this
    have hki : baseB + 2 ≠ baseB + 3 := by omega
    have hkj : baseB + 2 ≠ baseC + 0 := by omega
    simpa [nbr8] using (setPair!_getBang_ne nbr7 (baseB + 3) (baseC + 0) (baseB + 2) hi hj hk7 hki hkj)
  have hnbr8_size : nbr8.size = m + 12 := by
    simp [nbr8, setPair!_size, hnbr7_size]
  have hk8 : baseB + 2 < nbr8.size := by
    have : m + 6 < m + 12 := by omega
    simpa [baseB, hnbr8_size, Nat.add_assoc] using this
  have h9 : nbr[baseB + 2]! = nbr8[baseB + 2]! := by
    have hi : baseA + 3 < nbr8.size := by
      have : m + 3 < m + 12 := by omega
      simpa [baseA, hnbr8_size, Nat.add_assoc] using this
    have hj : baseC + 1 < nbr8.size := by
      have : m + 9 < m + 12 := by omega
      simpa [baseC, hnbr8_size, Nat.add_assoc] using this
    have hki : baseB + 2 ≠ baseA + 3 := by omega
    have hkj : baseB + 2 ≠ baseC + 1 := by omega
    simpa [nbr] using (setPair!_getBang_ne nbr8 (baseA + 3) (baseC + 1) (baseB + 2) hi hj hk8 hki hkj)
  have hnbr : r3BraidRightNbr g x u w = nbr := by rfl
  have hFinal : nbr[baseB + 2]! = w2 := by
    calc
      nbr[baseB + 2]! = nbr8[baseB + 2]! := h9
      _ = nbr7[baseB + 2]! := h8
      _ = nbr6[baseB + 2]! := h7
      _ = nbr5[baseB + 2]! := h6
      _ = nbr4[baseB + 2]! := h5
      _ = w2 := h4
  simpa [r3BraidRightGraph, hnbr, baseB, Nat.add_assoc, w2] using hFinal

private theorem arcNbr_r3BraidRight_baseA3
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    (r3BraidRightGraph g x u w).arcNbr[m + 3]! = m + 9 := by
  classical
  let m := g.numHalfEdges
  have hValid : PDGraph.Valid (r3BraidRightGraph g x u w) :=
    r3BraidRightGraph_valid_of_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hi : m + 9 < (r3BraidRightGraph g x u w).numHalfEdges := by
    dsimp [r3BraidRightGraph, PDGraph.numHalfEdges, m]
    have : (9 : Nat) < 12 := by decide
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.add_lt_add_left this (4 * g.n)
  have hC1 : (r3BraidRightGraph g x u w).arcNbr[m + 9]! = m + 3 :=
    arcNbr_r3BraidRight_baseC1 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have := PDGraph.Valid.invol hValid (i := m + 9) hi
  simpa [hC1, m] using this

private theorem arcNbr_r3BraidRight_baseB3
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    (r3BraidRightGraph g x u w).arcNbr[m + 7]! = m + 8 := by
  classical
  let m := g.numHalfEdges
  have hValid : PDGraph.Valid (r3BraidRightGraph g x u w) :=
    r3BraidRightGraph_valid_of_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hi : m + 8 < (r3BraidRightGraph g x u w).numHalfEdges := by
    dsimp [r3BraidRightGraph, PDGraph.numHalfEdges, m]
    have : (8 : Nat) < 12 := by decide
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.add_lt_add_left this (4 * g.n)
  have hC0 : (r3BraidRightGraph g x u w).arcNbr[m + 8]! = m + 7 :=
    arcNbr_r3BraidRight_baseC0 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have := PDGraph.Valid.invol hValid (i := m + 8) hi
  simpa [hC0, m] using this

private theorem arcNbr_r3BraidRight_u2
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    let u2 := g.arcNbr[u]!
    (r3BraidRightGraph g x u w).arcNbr[u2]! = m + 10 := by
  classical
  let m := g.numHalfEdges
  let u2 := g.arcNbr[u]!
  have hValid : PDGraph.Valid (r3BraidRightGraph g x u w) :=
    r3BraidRightGraph_valid_of_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hi : m + 10 < (r3BraidRightGraph g x u w).numHalfEdges := by
    dsimp [r3BraidRightGraph, PDGraph.numHalfEdges, m]
    have : (10 : Nat) < 12 := by decide
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.add_lt_add_left this (4 * g.n)
  have hC2 : (r3BraidRightGraph g x u w).arcNbr[m + 10]! = u2 :=
    arcNbr_r3BraidRight_baseC2 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have := PDGraph.Valid.invol hValid (i := m + 10) hi
  simpa [hC2, u2, m] using this

private theorem arcNbr_r3BraidRight_x2
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    let x2 := g.arcNbr[x]!
    (r3BraidRightGraph g x u w).arcNbr[x2]! = m + 11 := by
  classical
  let m := g.numHalfEdges
  let x2 := g.arcNbr[x]!
  have hValid : PDGraph.Valid (r3BraidRightGraph g x u w) :=
    r3BraidRightGraph_valid_of_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hi : m + 11 < (r3BraidRightGraph g x u w).numHalfEdges := by
    dsimp [r3BraidRightGraph, PDGraph.numHalfEdges, m]
    have : (11 : Nat) < 12 := by decide
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.add_lt_add_left this (4 * g.n)
  have hC3 : (r3BraidRightGraph g x u w).arcNbr[m + 11]! = x2 :=
    arcNbr_r3BraidRight_baseC3 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have := PDGraph.Valid.invol hValid (i := m + 11) hi
  simpa [hC3, x2, m] using this

private theorem smoothLastCoreML_rewire_r3BraidRight_boundary_A
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    let x2 := g.arcNbr[x]!
    let u2 := g.arcNbr[u]!
    let nbrA := smoothLastCoreML_rewire (g.n + 3) (r3BraidRightGraph g x u w).arcNbr false
    nbrA[m + 3]! = m + 7 ∧ nbrA[m + 7]! = m + 3 ∧ nbrA[x2]! = u2 ∧ nbrA[u2]! = x2 := by
  classical
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  let m := g.numHalfEdges
  have hx : x < m :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).1
  have hu : u < m :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.1
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  have hx2_lt : x2 < m := PDGraph.Valid.get_lt hValidG (i := x) hx
  have hu2_lt : u2 < m := PDGraph.Valid.get_lt hValidG (i := u) hu
  let nB : Nat := g.n + 3
  let arcNbr := (r3BraidRightGraph g x u w).arcNbr
  have hbase : (4 * nB) - 4 = m + 8 := by
    dsimp [nB, m, PDGraph.numHalfEdges]
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using baseC_eq g.n
  have hm3_lt : m + 3 < (4 * nB - 4) := by
    have : m + 3 < m + 8 := Nat.add_lt_add_left (by decide : (3 : Nat) < 8) m
    simpa [hbase] using this
  have hm7_lt : m + 7 < (4 * nB - 4) := by
    have : m + 7 < m + 8 := Nat.add_lt_add_left (by decide : (7 : Nat) < 8) m
    simpa [hbase] using this
  have hx2_lt_base : x2 < (4 * nB - 4) := by
    have : x2 < m + 8 := Nat.lt_of_lt_of_le hx2_lt (Nat.le_add_right m 8)
    simpa [hbase] using this
  have hu2_lt_base : u2 < (4 * nB - 4) := by
    have : u2 < m + 8 := Nat.lt_of_lt_of_le hu2_lt (Nat.le_add_right m 8)
    simpa [hbase] using this
  let nbrA := smoothLastCoreML_rewire nB arcNbr false
  have hC0 : (r3BraidRightGraph g x u w).arcNbr[m + 8]! = m + 7 :=
    arcNbr_r3BraidRight_baseC0 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hC1 : (r3BraidRightGraph g x u w).arcNbr[m + 9]! = m + 3 :=
    arcNbr_r3BraidRight_baseC1 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hC2 : (r3BraidRightGraph g x u w).arcNbr[m + 10]! = u2 :=
    arcNbr_r3BraidRight_baseC2 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hC3 : (r3BraidRightGraph g x u w).arcNbr[m + 11]! = x2 :=
    arcNbr_r3BraidRight_baseC3 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hA3 : (r3BraidRightGraph g x u w).arcNbr[m + 3]! = m + 9 :=
    arcNbr_r3BraidRight_baseA3 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hB3 : (r3BraidRightGraph g x u w).arcNbr[m + 7]! = m + 8 :=
    arcNbr_r3BraidRight_baseB3 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hX : (r3BraidRightGraph g x u w).arcNbr[x2]! = m + 11 :=
    arcNbr_r3BraidRight_x2 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hU : (r3BraidRightGraph g x u w).arcNbr[u2]! = m + 10 :=
    arcNbr_r3BraidRight_u2 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hA3' : arcNbr[m + 3]! = m + 9 := by simpa [arcNbr] using hA3
  have hB3' : arcNbr[m + 7]! = m + 8 := by simpa [arcNbr] using hB3
  have hC0' : arcNbr[m + 8]! = m + 7 := by simpa [arcNbr] using hC0
  have hC1' : arcNbr[m + 9]! = m + 3 := by simpa [arcNbr] using hC1
  have hC2' : arcNbr[m + 10]! = u2 := by simpa [arcNbr] using hC2
  have hC3' : arcNbr[m + 11]! = x2 := by simpa [arcNbr] using hC3
  have hX' : arcNbr[x2]! = m + 11 := by simpa [arcNbr] using hX
  have hU' : arcNbr[u2]! = m + 10 := by simpa [arcNbr] using hU
  have hsm8 : smoothLastCoreML_smooth nB false (m + 8) = m + 9 := by
    have hm0 : m % 4 = 0 := by
      dsimp [m, PDGraph.numHalfEdges]
      simp
    have hmod : (m + 8) % 4 = 0 := by
      calc
        (m + 8) % 4 = ((m % 4) + (8 % 4)) % 4 := by simpa [Nat.add_mod]
        _ = 0 := by simp [hm0]
    simp [smoothLastCoreML_smooth, hbase, hmod]
  have hsm10 : smoothLastCoreML_smooth nB false (m + 10) = m + 11 := by
    have hm0 : m % 4 = 0 := by
      dsimp [m, PDGraph.numHalfEdges]
      simp
    have hmod : (m + 10) % 4 = 2 := by
      calc
        (m + 10) % 4 = ((m % 4) + (10 % 4)) % 4 := by simpa [Nat.add_mod]
        _ = 2 := by simp [hm0]
    simp [smoothLastCoreML_smooth, hbase, hmod]
  have hsm9 : smoothLastCoreML_smooth nB false (m + 9) = m + 8 := by
    have hm0 : m % 4 = 0 := by dsimp [m, PDGraph.numHalfEdges]; simp
    have hmod : (m + 9) % 4 = 1 := by
      calc
        (m + 9) % 4 = ((m % 4) + (9 % 4)) % 4 := by simpa [Nat.add_mod]
        _ = 1 := by simp [hm0]
    simp [smoothLastCoreML_smooth, hbase, hmod]
  have hsm11 : smoothLastCoreML_smooth nB false (m + 11) = m + 10 := by
    have hm0 : m % 4 = 0 := by dsimp [m, PDGraph.numHalfEdges]; simp
    have hmod : (m + 11) % 4 = 3 := by
      calc
        (m + 11) % 4 = ((m % 4) + (11 % 4)) % 4 := by simpa [Nat.add_mod]
        _ = 3 := by simp [hm0]
    simp [smoothLastCoreML_smooth, hbase, hmod]

  have hrew_m3 : nbrA[m + 3]! = m + 7 := by
    have hy : arcNbr[smoothLastCoreML_smooth nB false (m + 9)]! < (4 * nB - 4) := by
      have : m + 7 < m + 8 := Nat.add_lt_add_left (by decide : (7 : Nat) < 8) m
      simpa [hsm9, hbase, hC0'] using this
    have hexit :
        smoothLastCoreML_exitFromExternal nB arcNbr false (m + 3) =
          arcNbr[smoothLastCoreML_smooth nB false (m + 9)]! := by
      simpa [hsm9] using
        (smoothLastCoreML_exitFromExternal_eq_of_y_lt_base (n := nB) (arcNbr := arcNbr) (isB := false)
          (x := m + 3) (r := m + 9) (hr := hA3') hy)
    have hnot : ¬(arcNbr[m + 3]! < (4 * nB - 4)) := by
      have : ¬(m + 9 < m + 8) := Nat.not_lt_of_ge (Nat.le_succ (m + 8))
      simpa [hA3', hbase] using this
    have : nbrA[m + 3]! = smoothLastCoreML_exitFromExternal nB arcNbr false (m + 3) := by
      simpa [nbrA, arcNbr, hnot] using smoothLastCoreML_rewire_getBang nB arcNbr false (m + 3) hm3_lt
    calc
      nbrA[m + 3]! = smoothLastCoreML_exitFromExternal nB arcNbr false (m + 3) := this
      _ = arcNbr[smoothLastCoreML_smooth nB false (m + 9)]! := hexit
      _ = m + 7 := by
        simpa [hsm9] using hC0'

  have hrew_m7 : nbrA[m + 7]! = m + 3 := by
    have hy : arcNbr[smoothLastCoreML_smooth nB false (m + 8)]! < (4 * nB - 4) := by
      have : m + 3 < m + 8 := Nat.add_lt_add_left (by decide : (3 : Nat) < 8) m
      simpa [hsm8, hbase, hC1'] using this
    have hexit :
        smoothLastCoreML_exitFromExternal nB arcNbr false (m + 7) =
          arcNbr[smoothLastCoreML_smooth nB false (m + 8)]! := by
      simpa [hsm8] using
        (smoothLastCoreML_exitFromExternal_eq_of_y_lt_base (n := nB) (arcNbr := arcNbr) (isB := false)
          (x := m + 7) (r := m + 8) (hr := hB3') hy)
    have hnot : ¬(arcNbr[m + 7]! < (4 * nB - 4)) := by
      have : ¬(m + 8 < m + 8) := by simpa using (Nat.lt_irrefl (m + 8))
      simpa [hB3', hbase] using this
    have : nbrA[m + 7]! = smoothLastCoreML_exitFromExternal nB arcNbr false (m + 7) := by
      simpa [nbrA, arcNbr, hnot] using smoothLastCoreML_rewire_getBang nB arcNbr false (m + 7) hm7_lt
    calc
      nbrA[m + 7]! = smoothLastCoreML_exitFromExternal nB arcNbr false (m + 7) := this
      _ = arcNbr[smoothLastCoreML_smooth nB false (m + 8)]! := hexit
      _ = m + 3 := by simpa [hsm8] using hC1'

  have hrew_u2 : nbrA[u2]! = x2 := by
    have hy : arcNbr[smoothLastCoreML_smooth nB false (m + 10)]! < (4 * nB - 4) := by
      have : x2 < m + 8 := Nat.lt_of_lt_of_le hx2_lt (Nat.le_add_right m 8)
      simpa [hsm10, hbase, hC3'] using this
    have hexit :
        smoothLastCoreML_exitFromExternal nB arcNbr false u2 =
          arcNbr[smoothLastCoreML_smooth nB false (m + 10)]! := by
      simpa [hsm10] using
        (smoothLastCoreML_exitFromExternal_eq_of_y_lt_base (n := nB) (arcNbr := arcNbr) (isB := false)
          (x := u2) (r := m + 10) (hr := hU') hy)
    have hnot : ¬(arcNbr[u2]! < (4 * nB - 4)) := by
      -- Simpler: `m+8 ≤ m+10`.
      have hge : m + 8 ≤ m + 10 := by
        exact Nat.le_trans (Nat.le_succ (m + 8)) (Nat.le_succ (m + 9))
      have : ¬(m + 10 < m + 8) := Nat.not_lt_of_ge hge
      simpa [hU', hbase] using this
    have : nbrA[u2]! = smoothLastCoreML_exitFromExternal nB arcNbr false u2 := by
      simpa [nbrA, arcNbr, hnot] using smoothLastCoreML_rewire_getBang nB arcNbr false u2 hu2_lt_base
    calc
      nbrA[u2]! = smoothLastCoreML_exitFromExternal nB arcNbr false u2 := this
      _ = arcNbr[smoothLastCoreML_smooth nB false (m + 10)]! := hexit
      _ = x2 := by simpa [hsm10] using hC3'

  have hrew_x2 : nbrA[x2]! = u2 := by
    have hy : arcNbr[smoothLastCoreML_smooth nB false (m + 11)]! < (4 * nB - 4) := by
      have : u2 < m + 8 := Nat.lt_of_lt_of_le hu2_lt (Nat.le_add_right m 8)
      simpa [hsm11, hbase, hC2'] using this
    have hexit :
        smoothLastCoreML_exitFromExternal nB arcNbr false x2 =
          arcNbr[smoothLastCoreML_smooth nB false (m + 11)]! := by
      simpa [hsm11] using
        (smoothLastCoreML_exitFromExternal_eq_of_y_lt_base (n := nB) (arcNbr := arcNbr) (isB := false)
          (x := x2) (r := m + 11) (hr := hX') hy)
    have hnot : ¬(arcNbr[x2]! < (4 * nB - 4)) := by
      have hge : m + 8 ≤ m + 11 := by
        exact Nat.le_trans (Nat.le_succ (m + 8)) (Nat.le_trans (Nat.le_succ (m + 9)) (Nat.le_succ (m + 10)))
      have : ¬(m + 11 < m + 8) := Nat.not_lt_of_ge hge
      simpa [hX', hbase] using this
    have : nbrA[x2]! = smoothLastCoreML_exitFromExternal nB arcNbr false x2 := by
      simpa [nbrA, arcNbr, hnot] using smoothLastCoreML_rewire_getBang nB arcNbr false x2 hx2_lt_base
    calc
      nbrA[x2]! = smoothLastCoreML_exitFromExternal nB arcNbr false x2 := this
      _ = arcNbr[smoothLastCoreML_smooth nB false (m + 11)]! := hexit
      _ = u2 := by simpa [hsm11] using hC2'

  exact ⟨hrew_m3, hrew_m7, hrew_x2, hrew_u2⟩

private theorem smoothLastCoreML_rewire_r3BraidRight_boundary_B
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    let x2 := g.arcNbr[x]!
    let u2 := g.arcNbr[u]!
    let nbrB := smoothLastCoreML_rewire (g.n + 3) (r3BraidRightGraph g x u w).arcNbr true
    nbrB[m + 3]! = u2 ∧ nbrB[u2]! = m + 3 ∧ nbrB[m + 7]! = x2 ∧ nbrB[x2]! = m + 7 := by
  classical
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  let m := g.numHalfEdges
  have hx : x < m :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).1
  have hu : u < m :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.1
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  have hx2_lt : x2 < m := PDGraph.Valid.get_lt hValidG (i := x) hx
  have hu2_lt : u2 < m := PDGraph.Valid.get_lt hValidG (i := u) hu
  let nB : Nat := g.n + 3
  let arcNbr := (r3BraidRightGraph g x u w).arcNbr
  have hbase : (4 * nB) - 4 = m + 8 := by
    dsimp [nB, m, PDGraph.numHalfEdges]
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using baseC_eq g.n
  have hm3_lt : m + 3 < (4 * nB - 4) := by
    have : m + 3 < m + 8 := Nat.add_lt_add_left (by decide : (3 : Nat) < 8) m
    simpa [hbase] using this
  have hm7_lt : m + 7 < (4 * nB - 4) := by
    have : m + 7 < m + 8 := Nat.add_lt_add_left (by decide : (7 : Nat) < 8) m
    simpa [hbase] using this
  have hx2_lt_base : x2 < (4 * nB - 4) := by
    have : x2 < m + 8 := Nat.lt_of_lt_of_le hx2_lt (Nat.le_add_right m 8)
    simpa [hbase] using this
  have hu2_lt_base : u2 < (4 * nB - 4) := by
    have : u2 < m + 8 := Nat.lt_of_lt_of_le hu2_lt (Nat.le_add_right m 8)
    simpa [hbase] using this
  let nbrB := smoothLastCoreML_rewire nB arcNbr true
  have hC0 : (r3BraidRightGraph g x u w).arcNbr[m + 8]! = m + 7 :=
    arcNbr_r3BraidRight_baseC0 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hC1 : (r3BraidRightGraph g x u w).arcNbr[m + 9]! = m + 3 :=
    arcNbr_r3BraidRight_baseC1 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hC2 : (r3BraidRightGraph g x u w).arcNbr[m + 10]! = u2 :=
    arcNbr_r3BraidRight_baseC2 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hC3 : (r3BraidRightGraph g x u w).arcNbr[m + 11]! = x2 :=
    arcNbr_r3BraidRight_baseC3 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hA3 : (r3BraidRightGraph g x u w).arcNbr[m + 3]! = m + 9 :=
    arcNbr_r3BraidRight_baseA3 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hB3 : (r3BraidRightGraph g x u w).arcNbr[m + 7]! = m + 8 :=
    arcNbr_r3BraidRight_baseB3 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hX : (r3BraidRightGraph g x u w).arcNbr[x2]! = m + 11 :=
    arcNbr_r3BraidRight_x2 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hU : (r3BraidRightGraph g x u w).arcNbr[u2]! = m + 10 :=
    arcNbr_r3BraidRight_u2 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hA3' : arcNbr[m + 3]! = m + 9 := by simpa [arcNbr] using hA3
  have hB3' : arcNbr[m + 7]! = m + 8 := by simpa [arcNbr] using hB3
  have hC0' : arcNbr[m + 8]! = m + 7 := by simpa [arcNbr] using hC0
  have hC1' : arcNbr[m + 9]! = m + 3 := by simpa [arcNbr] using hC1
  have hC2' : arcNbr[m + 10]! = u2 := by simpa [arcNbr] using hC2
  have hC3' : arcNbr[m + 11]! = x2 := by simpa [arcNbr] using hC3
  have hX' : arcNbr[x2]! = m + 11 := by simpa [arcNbr] using hX
  have hU' : arcNbr[u2]! = m + 10 := by simpa [arcNbr] using hU
  have hsm8 : smoothLastCoreML_smooth nB true (m + 8) = m + 11 := by
    have hm0 : m % 4 = 0 := by dsimp [m, PDGraph.numHalfEdges]; simp
    have hmod : (m + 8) % 4 = 0 := by
      calc
        (m + 8) % 4 = ((m % 4) + (8 % 4)) % 4 := by simpa [Nat.add_mod]
        _ = 0 := by simp [hm0]
    simp [smoothLastCoreML_smooth, hbase, hmod]
  have hsm9 : smoothLastCoreML_smooth nB true (m + 9) = m + 10 := by
    have hm0 : m % 4 = 0 := by dsimp [m, PDGraph.numHalfEdges]; simp
    have hmod : (m + 9) % 4 = 1 := by
      calc
        (m + 9) % 4 = ((m % 4) + (9 % 4)) % 4 := by simpa [Nat.add_mod]
        _ = 1 := by simp [hm0]
    simp [smoothLastCoreML_smooth, hbase, hmod]
  have hsm10 : smoothLastCoreML_smooth nB true (m + 10) = m + 9 := by
    have hm0 : m % 4 = 0 := by dsimp [m, PDGraph.numHalfEdges]; simp
    have hmod : (m + 10) % 4 = 2 := by
      calc
        (m + 10) % 4 = ((m % 4) + (10 % 4)) % 4 := by simpa [Nat.add_mod]
        _ = 2 := by simp [hm0]
    simp [smoothLastCoreML_smooth, hbase, hmod]
  have hsm11 : smoothLastCoreML_smooth nB true (m + 11) = m + 8 := by
    have hm0 : m % 4 = 0 := by dsimp [m, PDGraph.numHalfEdges]; simp
    have hmod : (m + 11) % 4 = 3 := by
      calc
        (m + 11) % 4 = ((m % 4) + (11 % 4)) % 4 := by simpa [Nat.add_mod]
        _ = 3 := by simp [hm0]
    simp [smoothLastCoreML_smooth, hbase, hmod]

  have hrew_m3 : nbrB[m + 3]! = u2 := by
    have hy : arcNbr[smoothLastCoreML_smooth nB true (m + 9)]! < (4 * nB - 4) := by
      have : u2 < m + 8 := Nat.lt_of_lt_of_le hu2_lt (Nat.le_add_right m 8)
      simpa [hsm9, hbase, hC2'] using this
    have hexit :
        smoothLastCoreML_exitFromExternal nB arcNbr true (m + 3) =
          arcNbr[smoothLastCoreML_smooth nB true (m + 9)]! := by
      simpa [hsm9] using
        (smoothLastCoreML_exitFromExternal_eq_of_y_lt_base (n := nB) (arcNbr := arcNbr) (isB := true)
          (x := m + 3) (r := m + 9) (hr := hA3') hy)
    have hnot : ¬(arcNbr[m + 3]! < (4 * nB - 4)) := by
      have : ¬(m + 9 < m + 8) := Nat.not_lt_of_ge (Nat.le_succ (m + 8))
      simpa [hA3', hbase] using this
    have : nbrB[m + 3]! = smoothLastCoreML_exitFromExternal nB arcNbr true (m + 3) := by
      simpa [nbrB, arcNbr, hnot] using smoothLastCoreML_rewire_getBang nB arcNbr true (m + 3) hm3_lt
    calc
      nbrB[m + 3]! = smoothLastCoreML_exitFromExternal nB arcNbr true (m + 3) := this
      _ = arcNbr[smoothLastCoreML_smooth nB true (m + 9)]! := hexit
      _ = u2 := by simpa [hsm9] using hC2'

  have hrew_u2 : nbrB[u2]! = m + 3 := by
    have hy : arcNbr[smoothLastCoreML_smooth nB true (m + 10)]! < (4 * nB - 4) := by
      have : m + 3 < m + 8 := Nat.add_lt_add_left (by decide : (3 : Nat) < 8) m
      simpa [hsm10, hbase, hC1'] using this
    have hexit :
        smoothLastCoreML_exitFromExternal nB arcNbr true u2 =
          arcNbr[smoothLastCoreML_smooth nB true (m + 10)]! := by
      simpa [hsm10] using
        (smoothLastCoreML_exitFromExternal_eq_of_y_lt_base (n := nB) (arcNbr := arcNbr) (isB := true)
          (x := u2) (r := m + 10) (hr := hU') hy)
    have hnot : ¬(arcNbr[u2]! < (4 * nB - 4)) := by
      have hge : m + 8 ≤ m + 10 := by
        exact Nat.le_trans (Nat.le_succ (m + 8)) (Nat.le_succ (m + 9))
      have : ¬(m + 10 < m + 8) := Nat.not_lt_of_ge hge
      simpa [hU', hbase] using this
    have : nbrB[u2]! = smoothLastCoreML_exitFromExternal nB arcNbr true u2 := by
      simpa [nbrB, arcNbr, hnot] using smoothLastCoreML_rewire_getBang nB arcNbr true u2 hu2_lt_base
    calc
      nbrB[u2]! = smoothLastCoreML_exitFromExternal nB arcNbr true u2 := this
      _ = arcNbr[smoothLastCoreML_smooth nB true (m + 10)]! := hexit
      _ = m + 3 := by simpa [hsm10] using hC1'

  have hrew_m7 : nbrB[m + 7]! = x2 := by
    have hy : arcNbr[smoothLastCoreML_smooth nB true (m + 8)]! < (4 * nB - 4) := by
      have : x2 < m + 8 := Nat.lt_of_lt_of_le hx2_lt (Nat.le_add_right m 8)
      simpa [hsm8, hbase, hC3'] using this
    have hexit :
        smoothLastCoreML_exitFromExternal nB arcNbr true (m + 7) =
          arcNbr[smoothLastCoreML_smooth nB true (m + 8)]! := by
      simpa [hsm8] using
        (smoothLastCoreML_exitFromExternal_eq_of_y_lt_base (n := nB) (arcNbr := arcNbr) (isB := true)
          (x := m + 7) (r := m + 8) (hr := hB3') hy)
    have hnot : ¬(arcNbr[m + 7]! < (4 * nB - 4)) := by
      have : ¬(m + 8 < m + 8) := by simpa using (Nat.lt_irrefl (m + 8))
      simpa [hB3', hbase] using this
    have : nbrB[m + 7]! = smoothLastCoreML_exitFromExternal nB arcNbr true (m + 7) := by
      simpa [nbrB, arcNbr, hnot] using smoothLastCoreML_rewire_getBang nB arcNbr true (m + 7) hm7_lt
    calc
      nbrB[m + 7]! = smoothLastCoreML_exitFromExternal nB arcNbr true (m + 7) := this
      _ = arcNbr[smoothLastCoreML_smooth nB true (m + 8)]! := hexit
      _ = x2 := by simpa [hsm8] using hC3'

  have hrew_x2 : nbrB[x2]! = m + 7 := by
    have hy : arcNbr[smoothLastCoreML_smooth nB true (m + 11)]! < (4 * nB - 4) := by
      have : m + 7 < m + 8 := Nat.add_lt_add_left (by decide : (7 : Nat) < 8) m
      simpa [hsm11, hbase, hC0'] using this
    have hexit :
        smoothLastCoreML_exitFromExternal nB arcNbr true x2 =
          arcNbr[smoothLastCoreML_smooth nB true (m + 11)]! := by
      simpa [hsm11] using
        (smoothLastCoreML_exitFromExternal_eq_of_y_lt_base (n := nB) (arcNbr := arcNbr) (isB := true)
          (x := x2) (r := m + 11) (hr := hX') hy)
    have hnot : ¬(arcNbr[x2]! < (4 * nB - 4)) := by
      have hge : m + 8 ≤ m + 11 := by
        exact Nat.le_trans (Nat.le_succ (m + 8)) (Nat.le_trans (Nat.le_succ (m + 9)) (Nat.le_succ (m + 10)))
      have : ¬(m + 11 < m + 8) := Nat.not_lt_of_ge hge
      simpa [hX', hbase] using this
    have : nbrB[x2]! = smoothLastCoreML_exitFromExternal nB arcNbr true x2 := by
      simpa [nbrB, arcNbr, hnot] using smoothLastCoreML_rewire_getBang nB arcNbr true x2 hx2_lt_base
    calc
      nbrB[x2]! = smoothLastCoreML_exitFromExternal nB arcNbr true x2 := this
      _ = arcNbr[smoothLastCoreML_smooth nB true (m + 11)]! := hexit
      _ = m + 7 := by simpa [hsm11] using hC0'

  exact ⟨hrew_m3, hrew_u2, hrew_m7, hrew_x2⟩

private theorem smoothLastCoreML_rewire_r3BraidRight_step1_signature
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    let x2 := g.arcNbr[x]!
    let u2 := g.arcNbr[u]!
    let nbrA := smoothLastCoreML_rewire (g.n + 3) (r3BraidRightGraph g x u w).arcNbr false
    let nbrB := smoothLastCoreML_rewire (g.n + 3) (r3BraidRightGraph g x u w).arcNbr true
    (nbrA[m + 3]! = m + 7 ∧ nbrA[m + 7]! = m + 3 ∧ nbrA[x2]! = u2 ∧ nbrA[u2]! = x2) ∧
      (nbrB[m + 3]! = u2 ∧ nbrB[u2]! = m + 3 ∧ nbrB[m + 7]! = x2 ∧ nbrB[x2]! = m + 7) := by
  exact ⟨smoothLastCoreML_rewire_r3BraidRight_boundary_A
      (g := g) (gR := gR) (x := x) (u := u) (w := w) h,
    smoothLastCoreML_rewire_r3BraidRight_boundary_B
      (g := g) (gR := gR) (x := x) (u := u) (w := w) h⟩

end BridgeStep1

/-!
## R3 invariance (Phase 1 target)

The actual Reidemeister-III invariance theorem will be proved by connecting the explicit braid
gadgets to the pre-proved TL₃ braid relation (`TL3Expr.braid_relation`) via the context functional
above.
-/

namespace R3

open TL3Expr

def tlWordLeft : TL3Expr :=
  (TL3Expr.sigma1 * TL3Expr.sigma2) * TL3Expr.sigma1

def tlWordRight : TL3Expr :=
  (TL3Expr.sigma2 * TL3Expr.sigma1) * TL3Expr.sigma2

/--
TL3 bridge nucleus: any fixed context functional over TL3 expressions respects
the braid relation by congruence.

This isolates the remaining R3 gap to connecting concrete braid-gadget
one-step evaluator outputs (`r3SkeinStep`) to this context-evaluation layer.
-/
theorem evalTL3Expr_braid_relation
    (fuel : Nat) (g : PDGraph) (x u w : Nat) :
    TL3Context.evalTL3Expr fuel g x u w tlWordLeft =
      TL3Context.evalTL3Expr fuel g x u w tlWordRight := by
  simpa [tlWordLeft, tlWordRight] using
    congrArg (fun a => TL3Context.evalTL3Expr fuel g x u w a)
      TL3Expr.braid_relation

/--
Left TL word expansion in evaluator normal form.

This is a bookkeeping lemma used by BridgeStep2/3: it fixes the exact
`evalTL3Expr` computation shape for `σ₁σ₂σ₁` before branch-level graph
identifications are applied.
-/
private theorem evalTL3Expr_tlWordLeft_expanded
    (fuel : Nat) (g : PDGraph) (x u w : Nat) :
    TL3Context.evalTL3Expr fuel g x u w tlWordLeft =
      (do
        let pid ← TL3Context.evalBasis fuel g x u w .id
        let pe1 ← TL3Context.evalBasis fuel g x u w .e1
        let pe2 ← TL3Context.evalBasis fuel g x u w .e2
        let pe1e2 ← TL3Context.evalBasis fuel g x u w .e1e2
        let pe2e1 ← TL3Context.evalBasis fuel g x u w .e2e1
        return (tlWordLeft.coeff .id) * pid
          + (tlWordLeft.coeff .e1) * pe1
          + (tlWordLeft.coeff .e2) * pe2
          + (tlWordLeft.coeff .e1e2) * pe1e2
          + (tlWordLeft.coeff .e2e1) * pe2e1) := by
  simp [TL3Context.evalTL3Expr]

/--
Right TL word expansion in evaluator normal form.

This is the mirror bookkeeping lemma for `σ₂σ₁σ₂`.
-/
private theorem evalTL3Expr_tlWordRight_expanded
    (fuel : Nat) (g : PDGraph) (x u w : Nat) :
    TL3Context.evalTL3Expr fuel g x u w tlWordRight =
      (do
        let pid ← TL3Context.evalBasis fuel g x u w .id
        let pe1 ← TL3Context.evalBasis fuel g x u w .e1
        let pe2 ← TL3Context.evalBasis fuel g x u w .e2
        let pe1e2 ← TL3Context.evalBasis fuel g x u w .e1e2
        let pe2e1 ← TL3Context.evalBasis fuel g x u w .e2e1
        return (tlWordRight.coeff .id) * pid
          + (tlWordRight.coeff .e1) * pe1
          + (tlWordRight.coeff .e2) * pe2
          + (tlWordRight.coeff .e1e2) * pe1e2
          + (tlWordRight.coeff .e2e1) * pe2e1) := by
  simp [TL3Context.evalTL3Expr]


/-!
## One-step skein expansion on the braid gadgets

These lemmas rewrite `bracketGraphML` on `r3Braid{Left,Right}` outputs into the raw skein step,
using the earlier facts that the R1/R2 short-circuit branches do not apply at the end of the
3-crossing braid gadgets.
-/

theorem bracketGraphML_skein_of_r3BraidLeft_ok
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    bracketGraphML gL =
      (do
        let n' := gL.n - 1
        let (freeA, nbrA) := smoothLastCoreML gL.freeLoops gL.n gL.arcNbr false
        let (freeB, nbrB) := smoothLastCoreML gL.freeLoops gL.n gL.arcNbr true
        let gA : PDGraph := { freeLoops := freeA, n := n', arcNbr := nbrA }
        let gB : PDGraph := { freeLoops := freeB, n := n', arcNbr := nbrB }
        let a ← bracketGraphMLAux (gL.n - 1) gA
        let b ← bracketGraphMLAux (gL.n - 1) gB
        return (AML * a) + (AinvML * b)) := by
  classical
  have hValid : PDGraph.Valid gL :=
    r3BraidLeft_valid (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hvgL : PDGraph.validate gL = .ok () :=
    PDGraph.validate_eq_ok_of_valid hValid
  have hn0 : gL.n ≠ 0 := by
    have hn : gL.n = g.n + 3 := r3BraidLeft_n_eq (g := g) (gL := gL) (x := x) (u := u) (w := w) h
    simpa [hn] using (Nat.succ_ne_zero (g.n + 2))
  cases hnFuel : gL.n with
  | zero =>
      cases hn0 (by simpa [hnFuel])
  | succ fuel =>
      -- Force the evaluator into the skein branch (R1/R2 checks fail on the braid gadget).
      have hr1p := r1RemoveLast_pos_err_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
      have hr1n := r1RemoveLast_neg_err_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
      have hr2 := r2RemoveLast_err_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
      simp [bracketGraphML, bracketGraphMLAux, hvgL, hnFuel, hr1p, hr1n, hr2,
        Bind.bind, Except.bind, Pure.pure, Except.pure, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

theorem bracketGraphML_skein_of_r3BraidRight_ok
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    bracketGraphML gR =
      (do
        let n' := gR.n - 1
        let (freeA, nbrA) := smoothLastCoreML gR.freeLoops gR.n gR.arcNbr false
        let (freeB, nbrB) := smoothLastCoreML gR.freeLoops gR.n gR.arcNbr true
        let gA : PDGraph := { freeLoops := freeA, n := n', arcNbr := nbrA }
        let gB : PDGraph := { freeLoops := freeB, n := n', arcNbr := nbrB }
        let a ← bracketGraphMLAux (gR.n - 1) gA
        let b ← bracketGraphMLAux (gR.n - 1) gB
        return (AML * a) + (AinvML * b)) := by
  classical
  have hValid : PDGraph.Valid gR :=
    r3BraidRight_valid (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hvgR : PDGraph.validate gR = .ok () :=
    PDGraph.validate_eq_ok_of_valid hValid
  have hn0 : gR.n ≠ 0 := by
    have hn : gR.n = g.n + 3 := r3BraidRight_n_eq (g := g) (gR := gR) (x := x) (u := u) (w := w) h
    simpa [hn] using (Nat.succ_ne_zero (g.n + 2))
  cases hnFuel : gR.n with
  | zero =>
      cases hn0 (by simpa [hnFuel])
  | succ fuel =>
      have hr1p := r1RemoveLast_pos_err_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
      have hr1n := r1RemoveLast_neg_err_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
      have hr2 := r2RemoveLast_err_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
      simp [bracketGraphML, bracketGraphMLAux, hvgR, hnFuel, hr1p, hr1n, hr2,
        Bind.bind, Except.bind, Pure.pure, Except.pure, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

end R3

/-- Public one-step skein evaluator used as the R3 endpoint interface. -/
def r3SkeinStep (g : PDGraph) : Except String PolyML := do
  let n' := g.n - 1
  let (freeA, nbrA) := smoothLastCoreML g.freeLoops g.n g.arcNbr false
  let (freeB, nbrB) := smoothLastCoreML g.freeLoops g.n g.arcNbr true
  let gA : PDGraph := { freeLoops := freeA, n := n', arcNbr := nbrA }
  let gB : PDGraph := { freeLoops := freeB, n := n', arcNbr := nbrB }
  let a ← bracketGraphMLAux (g.n - 1) gA
  let b ← bracketGraphMLAux (g.n - 1) gB
  return (AML * a) + (AinvML * b)

/--
Generic skein-branch unfolding for `bracketGraphML`.

This factors out recurring proof boilerplate: once validation and exclusion of
R1/R2 short-circuit branches are established for a graph `g`, evaluation
unfolds deterministically to the one-step skein branch.
-/
private theorem bracketGraphML_skein_of_no_shortcuts
    {g : PDGraph}
    (hvg : PDGraph.validate g = .ok ())
    (hn0 : g.n ≠ 0)
    (hr1p : ∀ g0 : PDGraph, Reidemeister.r1RemoveLast g .pos ≠ .ok g0)
    (hr1n : ∀ g0 : PDGraph, Reidemeister.r1RemoveLast g .neg ≠ .ok g0)
    (hr2 : ∀ g0 : PDGraph, Reidemeister.r2RemoveLast g ≠ .ok g0) :
    bracketGraphML g =
      (do
        let n' := g.n - 1
        let (freeA, nbrA) := smoothLastCoreML g.freeLoops g.n g.arcNbr false
        let (freeB, nbrB) := smoothLastCoreML g.freeLoops g.n g.arcNbr true
        let gA : PDGraph := { freeLoops := freeA, n := n', arcNbr := nbrA }
        let gB : PDGraph := { freeLoops := freeB, n := n', arcNbr := nbrB }
        let a ← bracketGraphMLAux (g.n - 1) gA
        let b ← bracketGraphMLAux (g.n - 1) gB
        return (AML * a) + (AinvML * b)) := by
  cases hnFuel : g.n with
  | zero =>
      cases hn0 (by simpa [hnFuel])
  | succ fuel =>
      have hr1p_err : ∃ e, Reidemeister.r1RemoveLast g .pos = .error e := by
        cases h1 : Reidemeister.r1RemoveLast g .pos with
        | ok g0 =>
            exact False.elim ((hr1p g0) h1)
        | error e =>
            exact ⟨e, rfl⟩
      have hr1n_err : ∃ e, Reidemeister.r1RemoveLast g .neg = .error e := by
        cases h1 : Reidemeister.r1RemoveLast g .neg with
        | ok g0 =>
            exact False.elim ((hr1n g0) h1)
        | error e =>
            exact ⟨e, rfl⟩
      have hr2_err : ∃ e, Reidemeister.r2RemoveLast g = .error e := by
        cases h2 : Reidemeister.r2RemoveLast g with
        | ok g0 =>
            exact False.elim ((hr2 g0) h2)
        | error e =>
            exact ⟨e, rfl⟩
      rcases hr1p_err with ⟨e1, he1⟩
      rcases hr1n_err with ⟨e2, he2⟩
      rcases hr2_err with ⟨e3, he3⟩
      simp [bracketGraphML, bracketGraphMLAux, hvg, hnFuel, he1, he2, he3,
        Bind.bind, Except.bind, Pure.pure, Except.pure, Nat.succ_eq_add_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private def r3BraidLeftStepA (g : PDGraph) (x u w : Nat) : PDGraph :=
  let gL := r3BraidLeftGraph g x u w
  let n' := gL.n - 1
  let (freeA, nbrA) := smoothLastCoreML gL.freeLoops gL.n gL.arcNbr false
  { freeLoops := freeA, n := n', arcNbr := nbrA }

private def r3BraidLeftStepB (g : PDGraph) (x u w : Nat) : PDGraph :=
  let gL := r3BraidLeftGraph g x u w
  let n' := gL.n - 1
  let (freeB, nbrB) := smoothLastCoreML gL.freeLoops gL.n gL.arcNbr true
  { freeLoops := freeB, n := n', arcNbr := nbrB }

private def r3BraidRightStepA (g : PDGraph) (x u w : Nat) : PDGraph :=
  let gR := r3BraidRightGraph g x u w
  let n' := gR.n - 1
  let (freeA, nbrA) := smoothLastCoreML gR.freeLoops gR.n gR.arcNbr false
  { freeLoops := freeA, n := n', arcNbr := nbrA }

private def r3BraidRightStepB (g : PDGraph) (x u w : Nat) : PDGraph :=
  let gR := r3BraidRightGraph g x u w
  let n' := gR.n - 1
  let (freeB, nbrB) := smoothLastCoreML gR.freeLoops gR.n gR.arcNbr true
  { freeLoops := freeB, n := n', arcNbr := nbrB }

private def r3BraidLeftStepAA (g : PDGraph) (x u w : Nat) : PDGraph :=
  let gA := r3BraidLeftStepA g x u w
  let n' := gA.n - 1
  let (freeAA, nbrAA) := smoothLastCoreML gA.freeLoops gA.n gA.arcNbr false
  { freeLoops := freeAA, n := n', arcNbr := nbrAA }

private def r3BraidLeftStepAB (g : PDGraph) (x u w : Nat) : PDGraph :=
  let gA := r3BraidLeftStepA g x u w
  let n' := gA.n - 1
  let (freeAB, nbrAB) := smoothLastCoreML gA.freeLoops gA.n gA.arcNbr true
  { freeLoops := freeAB, n := n', arcNbr := nbrAB }

private def r3BraidLeftStepBA (g : PDGraph) (x u w : Nat) : PDGraph :=
  let gB := r3BraidLeftStepB g x u w
  let n' := gB.n - 1
  let (freeBA, nbrBA) := smoothLastCoreML gB.freeLoops gB.n gB.arcNbr false
  { freeLoops := freeBA, n := n', arcNbr := nbrBA }

private def r3BraidLeftStepBB (g : PDGraph) (x u w : Nat) : PDGraph :=
  let gB := r3BraidLeftStepB g x u w
  let n' := gB.n - 1
  let (freeBB, nbrBB) := smoothLastCoreML gB.freeLoops gB.n gB.arcNbr true
  { freeLoops := freeBB, n := n', arcNbr := nbrBB }

private def r3BraidRightStepAA (g : PDGraph) (x u w : Nat) : PDGraph :=
  let gA := r3BraidRightStepA g x u w
  let n' := gA.n - 1
  let (freeAA, nbrAA) := smoothLastCoreML gA.freeLoops gA.n gA.arcNbr false
  { freeLoops := freeAA, n := n', arcNbr := nbrAA }

private def r3BraidRightStepAB (g : PDGraph) (x u w : Nat) : PDGraph :=
  let gA := r3BraidRightStepA g x u w
  let n' := gA.n - 1
  let (freeAB, nbrAB) := smoothLastCoreML gA.freeLoops gA.n gA.arcNbr true
  { freeLoops := freeAB, n := n', arcNbr := nbrAB }

private def r3BraidRightStepBA (g : PDGraph) (x u w : Nat) : PDGraph :=
  let gB := r3BraidRightStepB g x u w
  let n' := gB.n - 1
  let (freeBA, nbrBA) := smoothLastCoreML gB.freeLoops gB.n gB.arcNbr false
  { freeLoops := freeBA, n := n', arcNbr := nbrBA }

private def r3BraidRightStepBB (g : PDGraph) (x u w : Nat) : PDGraph :=
  let gB := r3BraidRightStepB g x u w
  let n' := gB.n - 1
  let (freeBB, nbrBB) := smoothLastCoreML gB.freeLoops gB.n gB.arcNbr true
  { freeLoops := freeBB, n := n', arcNbr := nbrBB }

private theorem r3BraidLeftStepAA_n (g : PDGraph) (x u w : Nat) :
    (r3BraidLeftStepAA g x u w).n = g.n + 1 := by
  simp [r3BraidLeftStepAA, r3BraidLeftStepA, r3BraidLeftGraph]

private theorem r3BraidLeftStepAB_n (g : PDGraph) (x u w : Nat) :
    (r3BraidLeftStepAB g x u w).n = g.n + 1 := by
  simp [r3BraidLeftStepAB, r3BraidLeftStepA, r3BraidLeftGraph]

private theorem r3BraidLeftStepBA_n (g : PDGraph) (x u w : Nat) :
    (r3BraidLeftStepBA g x u w).n = g.n + 1 := by
  simp [r3BraidLeftStepBA, r3BraidLeftStepB, r3BraidLeftGraph]

private theorem r3BraidLeftStepBB_n (g : PDGraph) (x u w : Nat) :
    (r3BraidLeftStepBB g x u w).n = g.n + 1 := by
  simp [r3BraidLeftStepBB, r3BraidLeftStepB, r3BraidLeftGraph]

private theorem r3BraidRightStepAA_n (g : PDGraph) (x u w : Nat) :
    (r3BraidRightStepAA g x u w).n = g.n + 1 := by
  simp [r3BraidRightStepAA, r3BraidRightStepA, r3BraidRightGraph]

private theorem r3BraidRightStepAB_n (g : PDGraph) (x u w : Nat) :
    (r3BraidRightStepAB g x u w).n = g.n + 1 := by
  simp [r3BraidRightStepAB, r3BraidRightStepA, r3BraidRightGraph]

private theorem r3BraidRightStepBA_n (g : PDGraph) (x u w : Nat) :
    (r3BraidRightStepBA g x u w).n = g.n + 1 := by
  simp [r3BraidRightStepBA, r3BraidRightStepB, r3BraidRightGraph]

private theorem r3BraidRightStepBB_n (g : PDGraph) (x u w : Nat) :
    (r3BraidRightStepBB g x u w).n = g.n + 1 := by
  simp [r3BraidRightStepBB, r3BraidRightStepB, r3BraidRightGraph]

private theorem r3BraidLeftStepAA_numHalfEdges (g : PDGraph) (x u w : Nat) :
    (r3BraidLeftStepAA g x u w).numHalfEdges = g.numHalfEdges + 4 := by
  simp [r3BraidLeftStepAA_n, PDGraph.numHalfEdges, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem r3BraidLeftStepAB_numHalfEdges (g : PDGraph) (x u w : Nat) :
    (r3BraidLeftStepAB g x u w).numHalfEdges = g.numHalfEdges + 4 := by
  simp [r3BraidLeftStepAB_n, PDGraph.numHalfEdges, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem r3BraidLeftStepBA_numHalfEdges (g : PDGraph) (x u w : Nat) :
    (r3BraidLeftStepBA g x u w).numHalfEdges = g.numHalfEdges + 4 := by
  simp [r3BraidLeftStepBA_n, PDGraph.numHalfEdges, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem r3BraidLeftStepBB_numHalfEdges (g : PDGraph) (x u w : Nat) :
    (r3BraidLeftStepBB g x u w).numHalfEdges = g.numHalfEdges + 4 := by
  simp [r3BraidLeftStepBB_n, PDGraph.numHalfEdges, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem r3BraidRightStepAA_numHalfEdges (g : PDGraph) (x u w : Nat) :
    (r3BraidRightStepAA g x u w).numHalfEdges = g.numHalfEdges + 4 := by
  simp [r3BraidRightStepAA_n, PDGraph.numHalfEdges, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem r3BraidRightStepAB_numHalfEdges (g : PDGraph) (x u w : Nat) :
    (r3BraidRightStepAB g x u w).numHalfEdges = g.numHalfEdges + 4 := by
  simp [r3BraidRightStepAB_n, PDGraph.numHalfEdges, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem r3BraidRightStepBA_numHalfEdges (g : PDGraph) (x u w : Nat) :
    (r3BraidRightStepBA g x u w).numHalfEdges = g.numHalfEdges + 4 := by
  simp [r3BraidRightStepBA_n, PDGraph.numHalfEdges, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem r3BraidRightStepBB_numHalfEdges (g : PDGraph) (x u w : Nat) :
    (r3BraidRightStepBB g x u w).numHalfEdges = g.numHalfEdges + 4 := by
  simp [r3BraidRightStepBB_n, PDGraph.numHalfEdges, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/--
Second-level skein unfolding scaffold for the left-A branch.

This is the first BridgeStep2 decomposition lemma: once R1/R2 short-circuit
branches are ruled out on `r3BraidLeftStepA`, its `bracketGraphML` evaluation
unfolds into the explicit `(AA, AB)` branch pair.
-/
private theorem bracketGraphML_leftStepA_skein_of_no_shortcuts
    (g : PDGraph) (x u w : Nat)
    (hvgA : PDGraph.validate (r3BraidLeftStepA g x u w) = .ok ())
    (hr1pA : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidLeftStepA g x u w) .pos ≠ .ok g0)
    (hr1nA : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidLeftStepA g x u w) .neg ≠ .ok g0)
    (hr2A : ∀ g0 : PDGraph,
      Reidemeister.r2RemoveLast (r3BraidLeftStepA g x u w) ≠ .ok g0) :
    bracketGraphML (r3BraidLeftStepA g x u w) =
      (do
        let a ← bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAA g x u w)
        let b ← bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAB g x u w)
        return (AML * a) + (AinvML * b)) := by
  have hn0A : (r3BraidLeftStepA g x u w).n ≠ 0 := by
    simp [r3BraidLeftStepA, r3BraidLeftGraph]
  simpa [r3BraidLeftStepAA, r3BraidLeftStepAB, r3BraidLeftStepA]
    using
      (bracketGraphML_skein_of_no_shortcuts
        (g := r3BraidLeftStepA g x u w)
        hvgA hn0A hr1pA hr1nA hr2A)

private theorem bracketGraphML_leftStepB_skein_of_no_shortcuts
    (g : PDGraph) (x u w : Nat)
    (hvgB : PDGraph.validate (r3BraidLeftStepB g x u w) = .ok ())
    (hr1pB : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidLeftStepB g x u w) .pos ≠ .ok g0)
    (hr1nB : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidLeftStepB g x u w) .neg ≠ .ok g0)
    (hr2B : ∀ g0 : PDGraph,
      Reidemeister.r2RemoveLast (r3BraidLeftStepB g x u w) ≠ .ok g0) :
    bracketGraphML (r3BraidLeftStepB g x u w) =
      (do
        let a ← bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
          (r3BraidLeftStepBA g x u w)
        let b ← bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
          (r3BraidLeftStepBB g x u w)
        return (AML * a) + (AinvML * b)) := by
  have hn0B : (r3BraidLeftStepB g x u w).n ≠ 0 := by
    simp [r3BraidLeftStepB, r3BraidLeftGraph]
  simpa [r3BraidLeftStepBA, r3BraidLeftStepBB, r3BraidLeftStepB]
    using
      (bracketGraphML_skein_of_no_shortcuts
        (g := r3BraidLeftStepB g x u w)
        hvgB hn0B hr1pB hr1nB hr2B)

private theorem bracketGraphML_rightStepA_skein_of_no_shortcuts
    (g : PDGraph) (x u w : Nat)
    (hvgA : PDGraph.validate (r3BraidRightStepA g x u w) = .ok ())
    (hr1pA : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidRightStepA g x u w) .pos ≠ .ok g0)
    (hr1nA : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidRightStepA g x u w) .neg ≠ .ok g0)
    (hr2A : ∀ g0 : PDGraph,
      Reidemeister.r2RemoveLast (r3BraidRightStepA g x u w) ≠ .ok g0) :
    bracketGraphML (r3BraidRightStepA g x u w) =
      (do
        let a ← bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
          (r3BraidRightStepAA g x u w)
        let b ← bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
          (r3BraidRightStepAB g x u w)
        return (AML * a) + (AinvML * b)) := by
  have hn0A : (r3BraidRightStepA g x u w).n ≠ 0 := by
    simp [r3BraidRightStepA, r3BraidRightGraph]
  simpa [r3BraidRightStepAA, r3BraidRightStepAB, r3BraidRightStepA]
    using
      (bracketGraphML_skein_of_no_shortcuts
        (g := r3BraidRightStepA g x u w)
        hvgA hn0A hr1pA hr1nA hr2A)

private theorem bracketGraphML_rightStepB_skein_of_no_shortcuts
    (g : PDGraph) (x u w : Nat)
    (hvgB : PDGraph.validate (r3BraidRightStepB g x u w) = .ok ())
    (hr1pB : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidRightStepB g x u w) .pos ≠ .ok g0)
    (hr1nB : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidRightStepB g x u w) .neg ≠ .ok g0)
    (hr2B : ∀ g0 : PDGraph,
      Reidemeister.r2RemoveLast (r3BraidRightStepB g x u w) ≠ .ok g0) :
    bracketGraphML (r3BraidRightStepB g x u w) =
      (do
        let a ← bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
          (r3BraidRightStepBA g x u w)
        let b ← bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
          (r3BraidRightStepBB g x u w)
        return (AML * a) + (AinvML * b)) := by
  have hn0B : (r3BraidRightStepB g x u w).n ≠ 0 := by
    simp [r3BraidRightStepB, r3BraidRightGraph]
  simpa [r3BraidRightStepBA, r3BraidRightStepBB, r3BraidRightStepB]
    using
      (bracketGraphML_skein_of_no_shortcuts
        (g := r3BraidRightStepB g x u w)
        hvgB hn0B hr1pB hr1nB hr2B)

/--
Canonical left-gadget expansion of `r3SkeinStep` into explicit first-step
branch graphs.
-/
private theorem r3SkeinStep_left_canonical_expanded
    (g : PDGraph) (x u w : Nat) :
    r3SkeinStep (r3BraidLeftGraph g x u w) =
      (do
        let a ← bracketGraphMLAux ((r3BraidLeftGraph g x u w).n - 1)
          (r3BraidLeftStepA g x u w)
        let b ← bracketGraphMLAux ((r3BraidLeftGraph g x u w).n - 1)
          (r3BraidLeftStepB g x u w)
        return (AML * a) + (AinvML * b)) := by
  simp [r3SkeinStep, r3BraidLeftStepA, r3BraidLeftStepB]

/--
Canonical right-gadget expansion of `r3SkeinStep` into explicit first-step
branch graphs.
-/
private theorem r3SkeinStep_right_canonical_expanded
    (g : PDGraph) (x u w : Nat) :
    r3SkeinStep (r3BraidRightGraph g x u w) =
      (do
        let a ← bracketGraphMLAux ((r3BraidRightGraph g x u w).n - 1)
          (r3BraidRightStepA g x u w)
        let b ← bracketGraphMLAux ((r3BraidRightGraph g x u w).n - 1)
          (r3BraidRightStepB g x u w)
        return (AML * a) + (AinvML * b)) := by
  simp [r3SkeinStep, r3BraidRightStepA, r3BraidRightStepB]

/-!
### BridgeStep1.5: normalized first-step signatures on step graphs

These lemmas repackage `BridgeStep1` array-level rewiring signatures directly on
the concrete first-step graphs (`r3Braid{Left,Right}Step{A,B}`), so later
BridgeStep2/3 proofs can avoid repeated unfolding boilerplate.
-/

private theorem r3BraidLeftStepA_signature
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    let u2 := g.arcNbr[u]!
    let w2 := g.arcNbr[w]!
    (r3BraidLeftStepA g x u w).arcNbr[m + 2]! = m + 6 ∧
      (r3BraidLeftStepA g x u w).arcNbr[m + 6]! = m + 2 ∧
      (r3BraidLeftStepA g x u w).arcNbr[u2]! = w2 ∧
      (r3BraidLeftStepA g x u w).arcNbr[w2]! = u2 := by
  have hSig := smoothLastCoreML_rewire_r3BraidLeft_step1_signature
    (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  simpa [r3BraidLeftStepA, r3BraidLeftGraph] using hSig.1

private theorem r3BraidLeftStepB_signature
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    let u2 := g.arcNbr[u]!
    let w2 := g.arcNbr[w]!
    (r3BraidLeftStepB g x u w).arcNbr[m + 2]! = u2 ∧
      (r3BraidLeftStepB g x u w).arcNbr[u2]! = m + 2 ∧
      (r3BraidLeftStepB g x u w).arcNbr[m + 6]! = w2 ∧
      (r3BraidLeftStepB g x u w).arcNbr[w2]! = m + 6 := by
  have hSig := smoothLastCoreML_rewire_r3BraidLeft_step1_signature
    (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  simpa [r3BraidLeftStepB, r3BraidLeftGraph] using hSig.2

private theorem r3BraidRightStepA_signature
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    let x2 := g.arcNbr[x]!
    let u2 := g.arcNbr[u]!
    (r3BraidRightStepA g x u w).arcNbr[m + 3]! = m + 7 ∧
      (r3BraidRightStepA g x u w).arcNbr[m + 7]! = m + 3 ∧
      (r3BraidRightStepA g x u w).arcNbr[x2]! = u2 ∧
      (r3BraidRightStepA g x u w).arcNbr[u2]! = x2 := by
  have hSig := smoothLastCoreML_rewire_r3BraidRight_step1_signature
    (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  simpa [r3BraidRightStepA, r3BraidRightGraph] using hSig.1

private theorem r3BraidRightStepB_signature
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    let x2 := g.arcNbr[x]!
    let u2 := g.arcNbr[u]!
    (r3BraidRightStepB g x u w).arcNbr[m + 3]! = u2 ∧
      (r3BraidRightStepB g x u w).arcNbr[u2]! = m + 3 ∧
      (r3BraidRightStepB g x u w).arcNbr[m + 7]! = x2 ∧
      (r3BraidRightStepB g x u w).arcNbr[x2]! = m + 7 := by
  have hSig := smoothLastCoreML_rewire_r3BraidRight_step1_signature
    (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  simpa [r3BraidRightStepB, r3BraidRightGraph] using hSig.2

/--
Track-B helper (`AA`, left): the external `(u2,w2)` pair survives the second
`A`-smoothing on `r3BraidLeftStepA`.
-/
private theorem r3BraidLeftStepAA_external_pair
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let u2 := g.arcNbr[u]!
    let w2 := g.arcNbr[w]!
    (r3BraidLeftStepAA g x u w).arcNbr[u2]! = w2 ∧
      (r3BraidLeftStepAA g x u w).arcNbr[w2]! = u2 := by
  let stepA := r3BraidLeftStepA g x u w
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  have hSig := r3BraidLeftStepA_signature
    (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hU2_stepA : stepA.arcNbr[u2]! = w2 := by
    simpa [stepA, u2, w2] using hSig.2.2.1
  have hW2_stepA : stepA.arcNbr[w2]! = u2 := by
    simpa [stepA, u2, w2] using hSig.2.2.2
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  have hu : u < g.numHalfEdges :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.1
  have hw : w < g.numHalfEdges :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.2
  have hu2_lt_m : u2 < g.numHalfEdges := by
    simpa [u2] using PDGraph.Valid.get_lt hValidG (i := u) hu
  have hw2_lt_m : w2 < g.numHalfEdges := by
    simpa [w2] using PDGraph.Valid.get_lt hValidG (i := w) hw
  have hbase : (4 * stepA.n) - 4 = g.numHalfEdges + 4 := by
    simp [stepA, r3BraidLeftStepA, r3BraidLeftGraph, PDGraph.numHalfEdges,
      Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hu2_lt_base : u2 < (4 * stepA.n) - 4 := by
    have hu2_lt : u2 < g.numHalfEdges + 4 :=
      Nat.lt_of_lt_of_le hu2_lt_m (Nat.le_add_right _ _)
    simpa [hbase] using hu2_lt
  have hw2_lt_base : w2 < (4 * stepA.n) - 4 := by
    have hw2_lt : w2 < g.numHalfEdges + 4 :=
      Nat.lt_of_lt_of_le hw2_lt_m (Nat.le_add_right _ _)
    simpa [hbase] using hw2_lt
  have hp_u2_lt_base : stepA.arcNbr[u2]! < (4 * stepA.n) - 4 := by
    calc
      stepA.arcNbr[u2]! = w2 := hU2_stepA
      _ < (4 * stepA.n) - 4 := hw2_lt_base
  have hp_w2_lt_base : stepA.arcNbr[w2]! < (4 * stepA.n) - 4 := by
    calc
      stepA.arcNbr[w2]! = u2 := hW2_stepA
      _ < (4 * stepA.n) - 4 := hu2_lt_base
  have hrew_u2 :
      (smoothLastCoreML_rewire stepA.n stepA.arcNbr false)[u2]! =
        stepA.arcNbr[u2]! := by
    have hget := smoothLastCoreML_rewire_getBang stepA.n stepA.arcNbr false u2 hu2_lt_base
    simpa [hp_u2_lt_base] using hget
  have hrew_w2 :
      (smoothLastCoreML_rewire stepA.n stepA.arcNbr false)[w2]! =
        stepA.arcNbr[w2]! := by
    have hget := smoothLastCoreML_rewire_getBang stepA.n stepA.arcNbr false w2 hw2_lt_base
    simpa [hp_w2_lt_base] using hget
  have hAA_u2 : (r3BraidLeftStepAA g x u w).arcNbr[u2]! = w2 := by
    calc
      (r3BraidLeftStepAA g x u w).arcNbr[u2]!
          = (smoothLastCoreML_rewire stepA.n stepA.arcNbr false)[u2]! := by
              simp [r3BraidLeftStepAA, stepA, smoothLastCoreML]
      _ = stepA.arcNbr[u2]! := hrew_u2
      _ = w2 := hU2_stepA
  have hAA_w2 : (r3BraidLeftStepAA g x u w).arcNbr[w2]! = u2 := by
    calc
      (r3BraidLeftStepAA g x u w).arcNbr[w2]!
          = (smoothLastCoreML_rewire stepA.n stepA.arcNbr false)[w2]! := by
              simp [r3BraidLeftStepAA, stepA, smoothLastCoreML]
      _ = stepA.arcNbr[w2]! := hrew_w2
      _ = u2 := hW2_stepA
  exact ⟨hAA_u2, hAA_w2⟩

/--
Track-B helper (`AA`, right): the external `(x2,u2)` pair survives the second
`A`-smoothing on `r3BraidRightStepA`.
-/
private theorem r3BraidRightStepAA_external_pair
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let x2 := g.arcNbr[x]!
    let u2 := g.arcNbr[u]!
    (r3BraidRightStepAA g x u w).arcNbr[x2]! = u2 ∧
      (r3BraidRightStepAA g x u w).arcNbr[u2]! = x2 := by
  let stepA := r3BraidRightStepA g x u w
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  have hSig := r3BraidRightStepA_signature
    (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hX2_stepA : stepA.arcNbr[x2]! = u2 := by
    simpa [stepA, x2, u2] using hSig.2.2.1
  have hU2_stepA : stepA.arcNbr[u2]! = x2 := by
    simpa [stepA, x2, u2] using hSig.2.2.2
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  have hx : x < g.numHalfEdges :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).1
  have hu : u < g.numHalfEdges :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.1
  have hx2_lt_m : x2 < g.numHalfEdges := by
    simpa [x2] using PDGraph.Valid.get_lt hValidG (i := x) hx
  have hu2_lt_m : u2 < g.numHalfEdges := by
    simpa [u2] using PDGraph.Valid.get_lt hValidG (i := u) hu
  have hbase : (4 * stepA.n) - 4 = g.numHalfEdges + 4 := by
    simp [stepA, r3BraidRightStepA, r3BraidRightGraph, PDGraph.numHalfEdges,
      Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hx2_lt_base : x2 < (4 * stepA.n) - 4 := by
    have hx2_lt : x2 < g.numHalfEdges + 4 :=
      Nat.lt_of_lt_of_le hx2_lt_m (Nat.le_add_right _ _)
    simpa [hbase] using hx2_lt
  have hu2_lt_base : u2 < (4 * stepA.n) - 4 := by
    have hu2_lt : u2 < g.numHalfEdges + 4 :=
      Nat.lt_of_lt_of_le hu2_lt_m (Nat.le_add_right _ _)
    simpa [hbase] using hu2_lt
  have hp_x2_lt_base : stepA.arcNbr[x2]! < (4 * stepA.n) - 4 := by
    calc
      stepA.arcNbr[x2]! = u2 := hX2_stepA
      _ < (4 * stepA.n) - 4 := hu2_lt_base
  have hp_u2_lt_base : stepA.arcNbr[u2]! < (4 * stepA.n) - 4 := by
    calc
      stepA.arcNbr[u2]! = x2 := hU2_stepA
      _ < (4 * stepA.n) - 4 := hx2_lt_base
  have hrew_x2 :
      (smoothLastCoreML_rewire stepA.n stepA.arcNbr false)[x2]! =
        stepA.arcNbr[x2]! := by
    have hget := smoothLastCoreML_rewire_getBang stepA.n stepA.arcNbr false x2 hx2_lt_base
    simpa [hp_x2_lt_base] using hget
  have hrew_u2 :
      (smoothLastCoreML_rewire stepA.n stepA.arcNbr false)[u2]! =
        stepA.arcNbr[u2]! := by
    have hget := smoothLastCoreML_rewire_getBang stepA.n stepA.arcNbr false u2 hu2_lt_base
    simpa [hp_u2_lt_base] using hget
  have hAA_x2 : (r3BraidRightStepAA g x u w).arcNbr[x2]! = u2 := by
    calc
      (r3BraidRightStepAA g x u w).arcNbr[x2]!
          = (smoothLastCoreML_rewire stepA.n stepA.arcNbr false)[x2]! := by
              simp [r3BraidRightStepAA, stepA, smoothLastCoreML]
      _ = stepA.arcNbr[x2]! := hrew_x2
      _ = u2 := hX2_stepA
  have hAA_u2 : (r3BraidRightStepAA g x u w).arcNbr[u2]! = x2 := by
    calc
      (r3BraidRightStepAA g x u w).arcNbr[u2]!
          = (smoothLastCoreML_rewire stepA.n stepA.arcNbr false)[u2]! := by
              simp [r3BraidRightStepAA, stepA, smoothLastCoreML]
      _ = stepA.arcNbr[u2]! := hrew_u2
      _ = x2 := hU2_stepA
  exact ⟨hAA_x2, hAA_u2⟩

/--
Track-B helper (`AB`, left): the external `(u2,w2)` pair survives the second
`B`-smoothing on `r3BraidLeftStepA`.
-/
private theorem r3BraidLeftStepAB_external_pair
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let u2 := g.arcNbr[u]!
    let w2 := g.arcNbr[w]!
    (r3BraidLeftStepAB g x u w).arcNbr[u2]! = w2 ∧
      (r3BraidLeftStepAB g x u w).arcNbr[w2]! = u2 := by
  let stepA := r3BraidLeftStepA g x u w
  let u2 := g.arcNbr[u]!
  let w2 := g.arcNbr[w]!
  have hSig := r3BraidLeftStepA_signature
    (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hU2_stepA : stepA.arcNbr[u2]! = w2 := by
    simpa [stepA, u2, w2] using hSig.2.2.1
  have hW2_stepA : stepA.arcNbr[w2]! = u2 := by
    simpa [stepA, u2, w2] using hSig.2.2.2
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  have hu : u < g.numHalfEdges :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.1
  have hw : w < g.numHalfEdges :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.2
  have hu2_lt_m : u2 < g.numHalfEdges := by
    simpa [u2] using PDGraph.Valid.get_lt hValidG (i := u) hu
  have hw2_lt_m : w2 < g.numHalfEdges := by
    simpa [w2] using PDGraph.Valid.get_lt hValidG (i := w) hw
  have hbase : (4 * stepA.n) - 4 = g.numHalfEdges + 4 := by
    simp [stepA, r3BraidLeftStepA, r3BraidLeftGraph, PDGraph.numHalfEdges,
      Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hu2_lt_base : u2 < (4 * stepA.n) - 4 := by
    have hu2_lt : u2 < g.numHalfEdges + 4 :=
      Nat.lt_of_lt_of_le hu2_lt_m (Nat.le_add_right _ _)
    simpa [hbase] using hu2_lt
  have hw2_lt_base : w2 < (4 * stepA.n) - 4 := by
    have hw2_lt : w2 < g.numHalfEdges + 4 :=
      Nat.lt_of_lt_of_le hw2_lt_m (Nat.le_add_right _ _)
    simpa [hbase] using hw2_lt
  have hp_u2_lt_base : stepA.arcNbr[u2]! < (4 * stepA.n) - 4 := by
    calc
      stepA.arcNbr[u2]! = w2 := hU2_stepA
      _ < (4 * stepA.n) - 4 := hw2_lt_base
  have hp_w2_lt_base : stepA.arcNbr[w2]! < (4 * stepA.n) - 4 := by
    calc
      stepA.arcNbr[w2]! = u2 := hW2_stepA
      _ < (4 * stepA.n) - 4 := hu2_lt_base
  have hrew_u2 :
      (smoothLastCoreML_rewire stepA.n stepA.arcNbr true)[u2]! =
        stepA.arcNbr[u2]! := by
    have hget := smoothLastCoreML_rewire_getBang stepA.n stepA.arcNbr true u2 hu2_lt_base
    simpa [hp_u2_lt_base] using hget
  have hrew_w2 :
      (smoothLastCoreML_rewire stepA.n stepA.arcNbr true)[w2]! =
        stepA.arcNbr[w2]! := by
    have hget := smoothLastCoreML_rewire_getBang stepA.n stepA.arcNbr true w2 hw2_lt_base
    simpa [hp_w2_lt_base] using hget
  have hAB_u2 : (r3BraidLeftStepAB g x u w).arcNbr[u2]! = w2 := by
    calc
      (r3BraidLeftStepAB g x u w).arcNbr[u2]!
          = (smoothLastCoreML_rewire stepA.n stepA.arcNbr true)[u2]! := by
              simp [r3BraidLeftStepAB, stepA, smoothLastCoreML]
      _ = stepA.arcNbr[u2]! := hrew_u2
      _ = w2 := hU2_stepA
  have hAB_w2 : (r3BraidLeftStepAB g x u w).arcNbr[w2]! = u2 := by
    calc
      (r3BraidLeftStepAB g x u w).arcNbr[w2]!
          = (smoothLastCoreML_rewire stepA.n stepA.arcNbr true)[w2]! := by
              simp [r3BraidLeftStepAB, stepA, smoothLastCoreML]
      _ = stepA.arcNbr[w2]! := hrew_w2
      _ = u2 := hW2_stepA
  exact ⟨hAB_u2, hAB_w2⟩

/--
Track-B helper (`AB`, right): the external `(x2,u2)` pair survives the second
`B`-smoothing on `r3BraidRightStepA`.
-/
private theorem r3BraidRightStepAB_external_pair
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let x2 := g.arcNbr[x]!
    let u2 := g.arcNbr[u]!
    (r3BraidRightStepAB g x u w).arcNbr[x2]! = u2 ∧
      (r3BraidRightStepAB g x u w).arcNbr[u2]! = x2 := by
  let stepA := r3BraidRightStepA g x u w
  let x2 := g.arcNbr[x]!
  let u2 := g.arcNbr[u]!
  have hSig := r3BraidRightStepA_signature
    (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hX2_stepA : stepA.arcNbr[x2]! = u2 := by
    simpa [stepA, x2, u2] using hSig.2.2.1
  have hU2_stepA : stepA.arcNbr[u2]! = x2 := by
    simpa [stepA, x2, u2] using hSig.2.2.2
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  have hx : x < g.numHalfEdges :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).1
  have hu : u < g.numHalfEdges :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.1
  have hx2_lt_m : x2 < g.numHalfEdges := by
    simpa [x2] using PDGraph.Valid.get_lt hValidG (i := x) hx
  have hu2_lt_m : u2 < g.numHalfEdges := by
    simpa [u2] using PDGraph.Valid.get_lt hValidG (i := u) hu
  have hbase : (4 * stepA.n) - 4 = g.numHalfEdges + 4 := by
    simp [stepA, r3BraidRightStepA, r3BraidRightGraph, PDGraph.numHalfEdges,
      Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hx2_lt_base : x2 < (4 * stepA.n) - 4 := by
    have hx2_lt : x2 < g.numHalfEdges + 4 :=
      Nat.lt_of_lt_of_le hx2_lt_m (Nat.le_add_right _ _)
    simpa [hbase] using hx2_lt
  have hu2_lt_base : u2 < (4 * stepA.n) - 4 := by
    have hu2_lt : u2 < g.numHalfEdges + 4 :=
      Nat.lt_of_lt_of_le hu2_lt_m (Nat.le_add_right _ _)
    simpa [hbase] using hu2_lt
  have hp_x2_lt_base : stepA.arcNbr[x2]! < (4 * stepA.n) - 4 := by
    calc
      stepA.arcNbr[x2]! = u2 := hX2_stepA
      _ < (4 * stepA.n) - 4 := hu2_lt_base
  have hp_u2_lt_base : stepA.arcNbr[u2]! < (4 * stepA.n) - 4 := by
    calc
      stepA.arcNbr[u2]! = x2 := hU2_stepA
      _ < (4 * stepA.n) - 4 := hx2_lt_base
  have hrew_x2 :
      (smoothLastCoreML_rewire stepA.n stepA.arcNbr true)[x2]! =
        stepA.arcNbr[x2]! := by
    have hget := smoothLastCoreML_rewire_getBang stepA.n stepA.arcNbr true x2 hx2_lt_base
    simpa [hp_x2_lt_base] using hget
  have hrew_u2 :
      (smoothLastCoreML_rewire stepA.n stepA.arcNbr true)[u2]! =
        stepA.arcNbr[u2]! := by
    have hget := smoothLastCoreML_rewire_getBang stepA.n stepA.arcNbr true u2 hu2_lt_base
    simpa [hp_u2_lt_base] using hget
  have hAB_x2 : (r3BraidRightStepAB g x u w).arcNbr[x2]! = u2 := by
    calc
      (r3BraidRightStepAB g x u w).arcNbr[x2]!
          = (smoothLastCoreML_rewire stepA.n stepA.arcNbr true)[x2]! := by
              simp [r3BraidRightStepAB, stepA, smoothLastCoreML]
      _ = stepA.arcNbr[x2]! := hrew_x2
      _ = u2 := hX2_stepA
  have hAB_u2 : (r3BraidRightStepAB g x u w).arcNbr[u2]! = x2 := by
    calc
      (r3BraidRightStepAB g x u w).arcNbr[u2]!
          = (smoothLastCoreML_rewire stepA.n stepA.arcNbr true)[u2]! := by
              simp [r3BraidRightStepAB, stepA, smoothLastCoreML]
      _ = stepA.arcNbr[u2]! := hrew_u2
      _ = x2 := hU2_stepA
  exact ⟨hAB_x2, hAB_u2⟩

/--
Track-B helper (`BA`, left): the `(m+2,u2)` pair survives the second
`A`-smoothing on `r3BraidLeftStepB`.
-/
private theorem r3BraidLeftStepBA_m2_u2_pair
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    let u2 := g.arcNbr[u]!
    (r3BraidLeftStepBA g x u w).arcNbr[m + 2]! = u2 ∧
      (r3BraidLeftStepBA g x u w).arcNbr[u2]! = m + 2 := by
  let stepB := r3BraidLeftStepB g x u w
  let m := g.numHalfEdges
  let u2 := g.arcNbr[u]!
  have hSig := r3BraidLeftStepB_signature
    (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hm2_stepB : stepB.arcNbr[m + 2]! = u2 := by
    simpa [stepB, m, u2] using hSig.1
  have hu2_stepB : stepB.arcNbr[u2]! = m + 2 := by
    simpa [stepB, m, u2] using hSig.2.1
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  have hu : u < g.numHalfEdges :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.1
  have hu2_lt_m : u2 < g.numHalfEdges := by
    simpa [u2] using PDGraph.Valid.get_lt hValidG (i := u) hu
  have hbase : (4 * stepB.n) - 4 = m + 4 := by
    simp [stepB, m, r3BraidLeftStepB, r3BraidLeftGraph, PDGraph.numHalfEdges,
      Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hm2_lt_base : m + 2 < (4 * stepB.n) - 4 := by
    have hm2_lt : m + 2 < m + 4 := Nat.add_lt_add_left (by decide : (2 : Nat) < 4) m
    simpa [hbase] using hm2_lt
  have hu2_lt_base : u2 < (4 * stepB.n) - 4 := by
    have hu2_lt : u2 < m + 4 :=
      Nat.lt_of_lt_of_le hu2_lt_m (Nat.le_add_right _ _)
    simpa [hbase] using hu2_lt
  have hp_m2_lt_base : stepB.arcNbr[m + 2]! < (4 * stepB.n) - 4 := by
    calc
      stepB.arcNbr[m + 2]! = u2 := hm2_stepB
      _ < (4 * stepB.n) - 4 := hu2_lt_base
  have hp_u2_lt_base : stepB.arcNbr[u2]! < (4 * stepB.n) - 4 := by
    calc
      stepB.arcNbr[u2]! = m + 2 := hu2_stepB
      _ < (4 * stepB.n) - 4 := hm2_lt_base
  have hrew_m2 :
      (smoothLastCoreML_rewire stepB.n stepB.arcNbr false)[m + 2]! =
        stepB.arcNbr[m + 2]! := by
    have hget := smoothLastCoreML_rewire_getBang stepB.n stepB.arcNbr false (m + 2) hm2_lt_base
    simpa [hp_m2_lt_base] using hget
  have hrew_u2 :
      (smoothLastCoreML_rewire stepB.n stepB.arcNbr false)[u2]! =
        stepB.arcNbr[u2]! := by
    have hget := smoothLastCoreML_rewire_getBang stepB.n stepB.arcNbr false u2 hu2_lt_base
    simpa [hp_u2_lt_base] using hget
  have hBA_m2 : (r3BraidLeftStepBA g x u w).arcNbr[m + 2]! = u2 := by
    calc
      (r3BraidLeftStepBA g x u w).arcNbr[m + 2]!
          = (smoothLastCoreML_rewire stepB.n stepB.arcNbr false)[m + 2]! := by
              simp [r3BraidLeftStepBA, stepB, smoothLastCoreML]
      _ = stepB.arcNbr[m + 2]! := hrew_m2
      _ = u2 := hm2_stepB
  have hBA_u2 : (r3BraidLeftStepBA g x u w).arcNbr[u2]! = m + 2 := by
    calc
      (r3BraidLeftStepBA g x u w).arcNbr[u2]!
          = (smoothLastCoreML_rewire stepB.n stepB.arcNbr false)[u2]! := by
              simp [r3BraidLeftStepBA, stepB, smoothLastCoreML]
      _ = stepB.arcNbr[u2]! := hrew_u2
      _ = m + 2 := hu2_stepB
  exact ⟨hBA_m2, hBA_u2⟩

/--
Track-B helper (`BA`, right): the `(m+3,u2)` pair survives the second
`A`-smoothing on `r3BraidRightStepB`.
-/
private theorem r3BraidRightStepBA_m3_u2_pair
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    let u2 := g.arcNbr[u]!
    (r3BraidRightStepBA g x u w).arcNbr[m + 3]! = u2 ∧
      (r3BraidRightStepBA g x u w).arcNbr[u2]! = m + 3 := by
  let stepB := r3BraidRightStepB g x u w
  let m := g.numHalfEdges
  let u2 := g.arcNbr[u]!
  have hSig := r3BraidRightStepB_signature
    (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hm3_stepB : stepB.arcNbr[m + 3]! = u2 := by
    simpa [stepB, m, u2] using hSig.1
  have hu2_stepB : stepB.arcNbr[u2]! = m + 3 := by
    simpa [stepB, m, u2] using hSig.2.1
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  have hu : u < g.numHalfEdges :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.1
  have hu2_lt_m : u2 < g.numHalfEdges := by
    simpa [u2] using PDGraph.Valid.get_lt hValidG (i := u) hu
  have hbase : (4 * stepB.n) - 4 = m + 4 := by
    simp [stepB, m, r3BraidRightStepB, r3BraidRightGraph, PDGraph.numHalfEdges,
      Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hm3_lt_base : m + 3 < (4 * stepB.n) - 4 := by
    have hm3_lt : m + 3 < m + 4 := Nat.add_lt_add_left (by decide : (3 : Nat) < 4) m
    simpa [hbase] using hm3_lt
  have hu2_lt_base : u2 < (4 * stepB.n) - 4 := by
    have hu2_lt : u2 < m + 4 :=
      Nat.lt_of_lt_of_le hu2_lt_m (Nat.le_add_right _ _)
    simpa [hbase] using hu2_lt
  have hp_m3_lt_base : stepB.arcNbr[m + 3]! < (4 * stepB.n) - 4 := by
    calc
      stepB.arcNbr[m + 3]! = u2 := hm3_stepB
      _ < (4 * stepB.n) - 4 := hu2_lt_base
  have hp_u2_lt_base : stepB.arcNbr[u2]! < (4 * stepB.n) - 4 := by
    calc
      stepB.arcNbr[u2]! = m + 3 := hu2_stepB
      _ < (4 * stepB.n) - 4 := hm3_lt_base
  have hrew_m3 :
      (smoothLastCoreML_rewire stepB.n stepB.arcNbr false)[m + 3]! =
        stepB.arcNbr[m + 3]! := by
    have hget := smoothLastCoreML_rewire_getBang stepB.n stepB.arcNbr false (m + 3) hm3_lt_base
    simpa [hp_m3_lt_base] using hget
  have hrew_u2 :
      (smoothLastCoreML_rewire stepB.n stepB.arcNbr false)[u2]! =
        stepB.arcNbr[u2]! := by
    have hget := smoothLastCoreML_rewire_getBang stepB.n stepB.arcNbr false u2 hu2_lt_base
    simpa [hp_u2_lt_base] using hget
  have hBA_m3 : (r3BraidRightStepBA g x u w).arcNbr[m + 3]! = u2 := by
    calc
      (r3BraidRightStepBA g x u w).arcNbr[m + 3]!
          = (smoothLastCoreML_rewire stepB.n stepB.arcNbr false)[m + 3]! := by
              simp [r3BraidRightStepBA, stepB, smoothLastCoreML]
      _ = stepB.arcNbr[m + 3]! := hrew_m3
      _ = u2 := hm3_stepB
  have hBA_u2 : (r3BraidRightStepBA g x u w).arcNbr[u2]! = m + 3 := by
    calc
      (r3BraidRightStepBA g x u w).arcNbr[u2]!
          = (smoothLastCoreML_rewire stepB.n stepB.arcNbr false)[u2]! := by
              simp [r3BraidRightStepBA, stepB, smoothLastCoreML]
      _ = stepB.arcNbr[u2]! := hrew_u2
      _ = m + 3 := hu2_stepB
  exact ⟨hBA_m3, hBA_u2⟩

/--
Track-B helper (`BB`, left): the `(m+2,u2)` pair survives the second
`B`-smoothing on `r3BraidLeftStepB`.
-/
private theorem r3BraidLeftStepBB_m2_u2_pair
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    let u2 := g.arcNbr[u]!
    (r3BraidLeftStepBB g x u w).arcNbr[m + 2]! = u2 ∧
      (r3BraidLeftStepBB g x u w).arcNbr[u2]! = m + 2 := by
  let stepB := r3BraidLeftStepB g x u w
  let m := g.numHalfEdges
  let u2 := g.arcNbr[u]!
  have hSig := r3BraidLeftStepB_signature
    (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hm2_stepB : stepB.arcNbr[m + 2]! = u2 := by
    simpa [stepB, m, u2] using hSig.1
  have hu2_stepB : stepB.arcNbr[u2]! = m + 2 := by
    simpa [stepB, m, u2] using hSig.2.1
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  have hu : u < g.numHalfEdges :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.1
  have hu2_lt_m : u2 < g.numHalfEdges := by
    simpa [u2] using PDGraph.Valid.get_lt hValidG (i := u) hu
  have hbase : (4 * stepB.n) - 4 = m + 4 := by
    simp [stepB, m, r3BraidLeftStepB, r3BraidLeftGraph, PDGraph.numHalfEdges,
      Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hm2_lt_base : m + 2 < (4 * stepB.n) - 4 := by
    have hm2_lt : m + 2 < m + 4 := Nat.add_lt_add_left (by decide : (2 : Nat) < 4) m
    simpa [hbase] using hm2_lt
  have hu2_lt_base : u2 < (4 * stepB.n) - 4 := by
    have hu2_lt : u2 < m + 4 :=
      Nat.lt_of_lt_of_le hu2_lt_m (Nat.le_add_right _ _)
    simpa [hbase] using hu2_lt
  have hp_m2_lt_base : stepB.arcNbr[m + 2]! < (4 * stepB.n) - 4 := by
    calc
      stepB.arcNbr[m + 2]! = u2 := hm2_stepB
      _ < (4 * stepB.n) - 4 := hu2_lt_base
  have hp_u2_lt_base : stepB.arcNbr[u2]! < (4 * stepB.n) - 4 := by
    calc
      stepB.arcNbr[u2]! = m + 2 := hu2_stepB
      _ < (4 * stepB.n) - 4 := hm2_lt_base
  have hrew_m2 :
      (smoothLastCoreML_rewire stepB.n stepB.arcNbr true)[m + 2]! =
        stepB.arcNbr[m + 2]! := by
    have hget := smoothLastCoreML_rewire_getBang stepB.n stepB.arcNbr true (m + 2) hm2_lt_base
    simpa [hp_m2_lt_base] using hget
  have hrew_u2 :
      (smoothLastCoreML_rewire stepB.n stepB.arcNbr true)[u2]! =
        stepB.arcNbr[u2]! := by
    have hget := smoothLastCoreML_rewire_getBang stepB.n stepB.arcNbr true u2 hu2_lt_base
    simpa [hp_u2_lt_base] using hget
  have hBB_m2 : (r3BraidLeftStepBB g x u w).arcNbr[m + 2]! = u2 := by
    calc
      (r3BraidLeftStepBB g x u w).arcNbr[m + 2]!
          = (smoothLastCoreML_rewire stepB.n stepB.arcNbr true)[m + 2]! := by
              simp [r3BraidLeftStepBB, stepB, smoothLastCoreML]
      _ = stepB.arcNbr[m + 2]! := hrew_m2
      _ = u2 := hm2_stepB
  have hBB_u2 : (r3BraidLeftStepBB g x u w).arcNbr[u2]! = m + 2 := by
    calc
      (r3BraidLeftStepBB g x u w).arcNbr[u2]!
          = (smoothLastCoreML_rewire stepB.n stepB.arcNbr true)[u2]! := by
              simp [r3BraidLeftStepBB, stepB, smoothLastCoreML]
      _ = stepB.arcNbr[u2]! := hrew_u2
      _ = m + 2 := hu2_stepB
  exact ⟨hBB_m2, hBB_u2⟩

/--
Track-B helper (`BB`, right): the `(m+3,u2)` pair survives the second
`B`-smoothing on `r3BraidRightStepB`.
-/
private theorem r3BraidRightStepBB_m3_u2_pair
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    let u2 := g.arcNbr[u]!
    (r3BraidRightStepBB g x u w).arcNbr[m + 3]! = u2 ∧
      (r3BraidRightStepBB g x u w).arcNbr[u2]! = m + 3 := by
  let stepB := r3BraidRightStepB g x u w
  let m := g.numHalfEdges
  let u2 := g.arcNbr[u]!
  have hSig := r3BraidRightStepB_signature
    (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hm3_stepB : stepB.arcNbr[m + 3]! = u2 := by
    simpa [stepB, m, u2] using hSig.1
  have hu2_stepB : stepB.arcNbr[u2]! = m + 3 := by
    simpa [stepB, m, u2] using hSig.2.1
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  have hu : u < g.numHalfEdges :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.1
  have hu2_lt_m : u2 < g.numHalfEdges := by
    simpa [u2] using PDGraph.Valid.get_lt hValidG (i := u) hu
  have hbase : (4 * stepB.n) - 4 = m + 4 := by
    simp [stepB, m, r3BraidRightStepB, r3BraidRightGraph, PDGraph.numHalfEdges,
      Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hm3_lt_base : m + 3 < (4 * stepB.n) - 4 := by
    have hm3_lt : m + 3 < m + 4 := Nat.add_lt_add_left (by decide : (3 : Nat) < 4) m
    simpa [hbase] using hm3_lt
  have hu2_lt_base : u2 < (4 * stepB.n) - 4 := by
    have hu2_lt : u2 < m + 4 :=
      Nat.lt_of_lt_of_le hu2_lt_m (Nat.le_add_right _ _)
    simpa [hbase] using hu2_lt
  have hp_m3_lt_base : stepB.arcNbr[m + 3]! < (4 * stepB.n) - 4 := by
    calc
      stepB.arcNbr[m + 3]! = u2 := hm3_stepB
      _ < (4 * stepB.n) - 4 := hu2_lt_base
  have hp_u2_lt_base : stepB.arcNbr[u2]! < (4 * stepB.n) - 4 := by
    calc
      stepB.arcNbr[u2]! = m + 3 := hu2_stepB
      _ < (4 * stepB.n) - 4 := hm3_lt_base
  have hrew_m3 :
      (smoothLastCoreML_rewire stepB.n stepB.arcNbr true)[m + 3]! =
        stepB.arcNbr[m + 3]! := by
    have hget := smoothLastCoreML_rewire_getBang stepB.n stepB.arcNbr true (m + 3) hm3_lt_base
    simpa [hp_m3_lt_base] using hget
  have hrew_u2 :
      (smoothLastCoreML_rewire stepB.n stepB.arcNbr true)[u2]! =
        stepB.arcNbr[u2]! := by
    have hget := smoothLastCoreML_rewire_getBang stepB.n stepB.arcNbr true u2 hu2_lt_base
    simpa [hp_u2_lt_base] using hget
  have hBB_m3 : (r3BraidRightStepBB g x u w).arcNbr[m + 3]! = u2 := by
    calc
      (r3BraidRightStepBB g x u w).arcNbr[m + 3]!
          = (smoothLastCoreML_rewire stepB.n stepB.arcNbr true)[m + 3]! := by
              simp [r3BraidRightStepBB, stepB, smoothLastCoreML]
      _ = stepB.arcNbr[m + 3]! := hrew_m3
      _ = u2 := hm3_stepB
  have hBB_u2 : (r3BraidRightStepBB g x u w).arcNbr[u2]! = m + 3 := by
    calc
      (r3BraidRightStepBB g x u w).arcNbr[u2]!
          = (smoothLastCoreML_rewire stepB.n stepB.arcNbr true)[u2]! := by
              simp [r3BraidRightStepBB, stepB, smoothLastCoreML]
      _ = stepB.arcNbr[u2]! := hrew_u2
      _ = m + 3 := hu2_stepB
  exact ⟨hBB_m3, hBB_u2⟩

private theorem validate_eq_ok_of_r2RemoveLast_ok
    {g g0 : PDGraph}
    (h : Reidemeister.r2RemoveLast g = .ok g0) :
    PDGraph.validate g = .ok () := by
  cases hvg : PDGraph.validate g with
  | error e =>
      simp [Reidemeister.r2RemoveLast, hvg] at h
  | ok hv =>
      cases hv
      rfl

/--
For a valid left R3 braid output, the first-step `A` branch cannot satisfy
`r2RemoveLast = .ok _` on its last-two-crossings pattern.

This closes the branch-collapse route for the left `A` branch and makes the
remaining R3 closure path explicit: TL3 bridge correspondences.
-/
private theorem r2RemoveLast_ne_ok_of_r3BraidLeftStepA
    {g gL g0 : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    Reidemeister.r2RemoveLast (r3BraidLeftStepA g x u w) ≠ .ok g0 := by
  intro hOk
  let stepA := r3BraidLeftStepA g x u w
  change Reidemeister.r2RemoveLast stepA = .ok g0 at hOk
  let m := g.numHalfEdges
  have hStepA2 : stepA.arcNbr[m + 2]! = m + 6 := by
    have hSig := r3BraidLeftStepA_signature
      (g := g) (gL := gL) (x := x) (u := u) (w := w) h
    simpa [stepA, m] using hSig.1
  cases hvg : PDGraph.validate stepA with
  | error e =>
      simpa [stepA, Reidemeister.r2RemoveLast, hvg] using hOk
  | ok hv =>
      cases hv
      have hnge : 2 ≤ stepA.n := by
        simp [stepA, r3BraidLeftStepA, r3BraidLeftGraph]
      have hnlt : ¬ stepA.n < 2 := Nat.not_lt_of_ge hnge
      have hmA : stepA.numHalfEdges = m + 8 := by
        simp [stepA, m, r3BraidLeftStepA, r3BraidLeftGraph, PDGraph.numHalfEdges,
          Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have hMismatch2 :
          stepA.arcNbr[stepA.numHalfEdges - 8 + 2]! ≠ stepA.numHalfEdges - 4 + 3 := by
        have hsub8 : (m + 8) - 8 = m := Nat.add_sub_cancel m 8
        have h4le8 : 4 ≤ 8 := by
          simpa using (Nat.le_add_left 4 4)
        have hsub4 : (m + 8) - 4 = m + 4 := by
          simpa using (Nat.add_sub_assoc m h4le8)
        have hStepA2' : stepA.arcNbr[stepA.numHalfEdges - 8 + 2]! = m + 6 := by
          simpa [hmA, hsub8, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hStepA2
        have hRhs : stepA.numHalfEdges - 4 + 3 = m + 7 := by
          calc
            stepA.numHalfEdges - 4 + 3 = ((m + 8) - 4) + 3 := by simpa [hmA]
            _ = (m + 4) + 3 := by simpa [hsub4]
            _ = m + (4 + 3) := by simp [Nat.add_assoc]
            _ = m + 7 := by rfl
        intro hEq
        have h67 : m + 6 = m + 7 := by
          calc
            m + 6 = stepA.arcNbr[stepA.numHalfEdges - 8 + 2]! := hStepA2'.symm
            _ = stepA.numHalfEdges - 4 + 3 := hEq
            _ = m + 7 := hRhs
        exact (Nat.ne_of_lt (Nat.lt_succ_self (m + 6))) h67
      have hCond2 :
          ¬stepA.arcNbr[stepA.numHalfEdges - 8 + 2]! = stepA.numHalfEdges - 4 + 3 ∨
            stepA.arcNbr[stepA.numHalfEdges - 4 + 3]! ≠ stepA.numHalfEdges - 8 + 2 :=
        Or.inl hMismatch2
      by_cases hCond1 :
          ¬stepA.arcNbr[stepA.numHalfEdges - 8 + 1]! = stepA.numHalfEdges - 4 ∨
            ¬stepA.arcNbr[stepA.numHalfEdges - 4]! = stepA.numHalfEdges - 8 + 1
      · have hErr :
            (Except.error "r2RemoveLast: internal arc (1↔0) mismatch" : Except String PDGraph) =
              .ok g0 := by
          simpa [Reidemeister.r2RemoveLast, hvg, hnlt, hCond1] using hOk
        cases hErr
      · have hErr :
            (Except.error "r2RemoveLast: internal arc (2↔3) mismatch" : Except String PDGraph) =
              .ok g0 := by
          simpa [Reidemeister.r2RemoveLast, hvg, hnlt, hCond1, hCond2] using hOk
        cases hErr

private theorem r1RemoveLast_neg_ne_ok_of_r3BraidLeftStepA
    {g gL g0 : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    Reidemeister.r1RemoveLast (r3BraidLeftStepA g x u w) .neg ≠ .ok g0 := by
  intro hOk
  let stepA := r3BraidLeftStepA g x u w
  change Reidemeister.r1RemoveLast stepA .neg = .ok g0 at hOk
  let m := g.numHalfEdges
  have hStepA6 : stepA.arcNbr[m + 6]! = m + 2 := by
    have hSig := r3BraidLeftStepA_signature
      (g := g) (gL := gL) (x := x) (u := u) (w := w) h
    simpa [stepA, m] using hSig.2.1
  cases hvg : PDGraph.validate stepA with
  | error e =>
      simpa [stepA, Reidemeister.r1RemoveLast, hvg] using hOk
  | ok hv =>
      cases hv
      have hnge : 1 ≤ stepA.n := by
        simp [stepA, r3BraidLeftStepA, r3BraidLeftGraph]
      have hn0 : stepA.n ≠ 0 := Nat.ne_of_gt hnge
      have hmA : stepA.numHalfEdges = m + 8 := by
        simp [stepA, m, r3BraidLeftStepA, r3BraidLeftGraph, PDGraph.numHalfEdges,
          Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have h4le8 : 4 ≤ 8 := by
        simpa using (Nat.le_add_left 4 4)
      have hsub4 : (m + 8) - 4 = m + 4 := by
        simpa using (Nat.add_sub_assoc m h4le8)
      have hIntBIdx : stepA.numHalfEdges - 4 + 2 = m + 6 := by
        calc
          stepA.numHalfEdges - 4 + 2 = ((m + 8) - 4) + 2 := by simpa [hmA]
          _ = (m + 4) + 2 := by simpa [hsub4]
          _ = m + 6 := by rfl
      have hIntB : stepA.arcNbr[stepA.numHalfEdges - 4 + 2]! = m + 2 := by
        simpa [hIntBIdx, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hStepA6
      have hIntAIdx : stepA.numHalfEdges - 4 + 1 = m + 5 := by
        calc
          stepA.numHalfEdges - 4 + 1 = ((m + 8) - 4) + 1 := by simpa [hmA]
          _ = (m + 4) + 1 := by simpa [hsub4]
          _ = m + 5 := by rfl
      have hMismatch :
          stepA.arcNbr[stepA.numHalfEdges - 4 + 2]! ≠ stepA.numHalfEdges - 4 + 1 := by
        intro hEq
        have h25 : m + 2 = m + 5 := by
          calc
            m + 2 = stepA.arcNbr[stepA.numHalfEdges - 4 + 2]! := hIntB.symm
            _ = stepA.numHalfEdges - 4 + 1 := hEq
            _ = m + 5 := hIntAIdx
        exact (Nat.ne_of_lt (Nat.add_lt_add_left (by decide : (2 : Nat) < 5) m)) h25
      have hCond :
          ¬stepA.arcNbr[stepA.numHalfEdges - 4 + 1]! = stepA.numHalfEdges - 4 + 2 ∨
            ¬stepA.arcNbr[stepA.numHalfEdges - 4 + 2]! = stepA.numHalfEdges - 4 + 1 :=
        Or.inr hMismatch
      have hErr :
          (Except.error "r1RemoveLast: internal loop arc mismatch" : Except String PDGraph) =
            .ok g0 := by
        simpa [Reidemeister.r1RemoveLast, hvg, hn0, hCond] using hOk
      cases hErr

private theorem r3BraidLeftStepA_arc_m_plus_4
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    (r3BraidLeftStepA g x u w).arcNbr[m + 4]! = m + 3 := by
  let m := g.numHalfEdges
  let nB : Nat := g.n + 3
  let arcNbr := (r3BraidLeftGraph g x u w).arcNbr
  have hbase : (4 * nB) - 4 = m + 8 := by
    dsimp [nB, m, PDGraph.numHalfEdges]
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using baseC_eq g.n
  have hm4_lt : m + 4 < (4 * nB - 4) := by
    have : m + 4 < m + 8 := Nat.add_lt_add_left (by decide : (4 : Nat) < 8) m
    simpa [hbase] using this
  have hB0 : (r3BraidLeftGraph g x u w).arcNbr[m + 4]! = m + 3 :=
    arcNbr_r3BraidLeft_baseB0 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hp_lt : arcNbr[m + 4]! < (4 * nB - 4) := by
    have : m + 3 < m + 8 := Nat.add_lt_add_left (by decide : (3 : Nat) < 8) m
    simpa [arcNbr, hB0, hbase] using this
  have hrew :
      (smoothLastCoreML_rewire nB arcNbr false)[m + 4]! = arcNbr[m + 4]! := by
    have hget := smoothLastCoreML_rewire_getBang nB arcNbr false (m + 4) hm4_lt
    simpa [hp_lt] using hget
  change
    (smoothLastCoreML (r3BraidLeftGraph g x u w).freeLoops
      (r3BraidLeftGraph g x u w).n
      (r3BraidLeftGraph g x u w).arcNbr false).2[m + 4]! = m + 3
  simp [smoothLastCoreML]
  have hnB : (r3BraidLeftGraph g x u w).n = nB := by
    simp [nB, r3BraidLeftGraph]
  calc
    (smoothLastCoreML_rewire (r3BraidLeftGraph g x u w).n
      (r3BraidLeftGraph g x u w).arcNbr false)[m + 4]!
        = (smoothLastCoreML_rewire nB arcNbr false)[m + 4]! := by
            simpa [hnB, arcNbr]
    _ = arcNbr[m + 4]! := hrew
    _ = m + 3 := by simpa [arcNbr] using hB0

private theorem r1RemoveLast_pos_ne_ok_of_r3BraidLeftStepA
    {g gL g0 : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    Reidemeister.r1RemoveLast (r3BraidLeftStepA g x u w) .pos ≠ .ok g0 := by
  intro hOk
  let stepA := r3BraidLeftStepA g x u w
  change Reidemeister.r1RemoveLast stepA .pos = .ok g0 at hOk
  let m := g.numHalfEdges
  have hStepA4 : stepA.arcNbr[m + 4]! = m + 3 := by
    simpa [stepA, m] using
      (r3BraidLeftStepA_arc_m_plus_4 (g := g) (gL := gL) (x := x) (u := u) (w := w) h)
  cases hvg : PDGraph.validate stepA with
  | error e =>
      simpa [stepA, Reidemeister.r1RemoveLast, hvg] using hOk
  | ok hv =>
      cases hv
      have hnge : 1 ≤ stepA.n := by
        simp [stepA, r3BraidLeftStepA, r3BraidLeftGraph]
      have hn0 : stepA.n ≠ 0 := Nat.ne_of_gt hnge
      have hmA : stepA.numHalfEdges = m + 8 := by
        simp [stepA, m, r3BraidLeftStepA, r3BraidLeftGraph, PDGraph.numHalfEdges,
          Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have h4le8 : 4 ≤ 8 := by
        simpa using (Nat.le_add_left 4 4)
      have hsub4 : (m + 8) - 4 = m + 4 := by
        simpa using (Nat.add_sub_assoc m h4le8)
      have hIntAIdx : stepA.numHalfEdges - 4 = m + 4 := by
        calc
          stepA.numHalfEdges - 4 = (m + 8) - 4 := by simpa [hmA]
          _ = m + 4 := by simpa [hsub4]
      have hIntA : stepA.arcNbr[stepA.numHalfEdges - 4]! = m + 3 := by
        simpa [hIntAIdx, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hStepA4
      have hIntBIdx : stepA.numHalfEdges - 4 + 1 = m + 5 := by
        calc
          stepA.numHalfEdges - 4 + 1 = ((m + 8) - 4) + 1 := by simpa [hmA]
          _ = (m + 4) + 1 := by simpa [hsub4]
          _ = m + 5 := by rfl
      have hMismatch :
          stepA.arcNbr[stepA.numHalfEdges - 4]! ≠ stepA.numHalfEdges - 4 + 1 := by
        intro hEq
        have h35 : m + 3 = m + 5 := by
          calc
            m + 3 = stepA.arcNbr[stepA.numHalfEdges - 4]! := hIntA.symm
            _ = stepA.numHalfEdges - 4 + 1 := hEq
            _ = m + 5 := hIntBIdx
        exact (Nat.ne_of_lt (Nat.add_lt_add_left (by decide : (3 : Nat) < 5) m)) h35
      have hCond :
          ¬stepA.arcNbr[stepA.numHalfEdges - 4]! = stepA.numHalfEdges - 4 + 1 ∨
            ¬stepA.arcNbr[stepA.numHalfEdges - 4 + 1]! = stepA.numHalfEdges - 4 :=
        Or.inl hMismatch
      have hErr :
          (Except.error "r1RemoveLast: internal loop arc mismatch" : Except String PDGraph) =
            .ok g0 := by
        simpa [Reidemeister.r1RemoveLast, hvg, hn0, hCond] using hOk
      cases hErr

private theorem r2RemoveLast_ne_ok_of_r3BraidLeftStepB
    {g gL g0 : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    Reidemeister.r2RemoveLast (r3BraidLeftStepB g x u w) ≠ .ok g0 := by
  intro hOk
  let stepB := r3BraidLeftStepB g x u w
  change Reidemeister.r2RemoveLast stepB = .ok g0 at hOk
  let m := g.numHalfEdges
  let u2 := g.arcNbr[u]!
  have hu : u < m :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.1
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  have hu2_lt_m : u2 < m := PDGraph.Valid.get_lt hValidG (i := u) hu
  have hStepB2 : stepB.arcNbr[m + 2]! = u2 := by
    have hSig := r3BraidLeftStepB_signature
      (g := g) (gL := gL) (x := x) (u := u) (w := w) h
    simpa [stepB, m, u2] using hSig.1
  cases hvg : PDGraph.validate stepB with
  | error e =>
      simpa [stepB, Reidemeister.r2RemoveLast, hvg] using hOk
  | ok hv =>
      cases hv
      have hnge : 2 ≤ stepB.n := by
        simp [stepB, r3BraidLeftStepB, r3BraidLeftGraph]
      have hnlt : ¬ stepB.n < 2 := Nat.not_lt_of_ge hnge
      have hmA : stepB.numHalfEdges = m + 8 := by
        simp [stepB, m, r3BraidLeftStepB, r3BraidLeftGraph, PDGraph.numHalfEdges,
          Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have hMismatch2 :
          stepB.arcNbr[stepB.numHalfEdges - 8 + 2]! ≠ stepB.numHalfEdges - 4 + 3 := by
        have hsub8 : (m + 8) - 8 = m := Nat.add_sub_cancel m 8
        have h4le8 : 4 ≤ 8 := by
          simpa using (Nat.le_add_left 4 4)
        have hsub4 : (m + 8) - 4 = m + 4 := by
          simpa using (Nat.add_sub_assoc m h4le8)
        have hStepB2' : stepB.arcNbr[stepB.numHalfEdges - 8 + 2]! = u2 := by
          simpa [hmA, hsub8, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hStepB2
        have hRhs : stepB.numHalfEdges - 4 + 3 = m + 7 := by
          calc
            stepB.numHalfEdges - 4 + 3 = ((m + 8) - 4) + 3 := by simpa [hmA]
            _ = (m + 4) + 3 := by simpa [hsub4]
            _ = m + (4 + 3) := by simp [Nat.add_assoc]
            _ = m + 7 := by rfl
        have hu2_lt_m7 : u2 < m + 7 := Nat.lt_of_lt_of_le hu2_lt_m (Nat.le_add_right m 7)
        intro hEq
        have hu2_eq_m7 : u2 = m + 7 := by
          calc
            u2 = stepB.arcNbr[stepB.numHalfEdges - 8 + 2]! := hStepB2'.symm
            _ = stepB.numHalfEdges - 4 + 3 := hEq
            _ = m + 7 := hRhs
        exact (Nat.ne_of_lt hu2_lt_m7) hu2_eq_m7
      have hCond2 :
          ¬stepB.arcNbr[stepB.numHalfEdges - 8 + 2]! = stepB.numHalfEdges - 4 + 3 ∨
            stepB.arcNbr[stepB.numHalfEdges - 4 + 3]! ≠ stepB.numHalfEdges - 8 + 2 :=
        Or.inl hMismatch2
      by_cases hCond1 :
          ¬stepB.arcNbr[stepB.numHalfEdges - 8 + 1]! = stepB.numHalfEdges - 4 ∨
            ¬stepB.arcNbr[stepB.numHalfEdges - 4]! = stepB.numHalfEdges - 8 + 1
      · have hErr :
            (Except.error "r2RemoveLast: internal arc (1↔0) mismatch" : Except String PDGraph) =
              .ok g0 := by
          simpa [Reidemeister.r2RemoveLast, hvg, hnlt, hCond1] using hOk
        cases hErr
      · have hErr :
            (Except.error "r2RemoveLast: internal arc (2↔3) mismatch" : Except String PDGraph) =
              .ok g0 := by
          simpa [Reidemeister.r2RemoveLast, hvg, hnlt, hCond1, hCond2] using hOk
        cases hErr

private theorem r2RemoveLast_ne_ok_of_r3BraidRightStepA
    {g gR g0 : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    Reidemeister.r2RemoveLast (r3BraidRightStepA g x u w) ≠ .ok g0 := by
  intro hOk
  let stepA := r3BraidRightStepA g x u w
  change Reidemeister.r2RemoveLast stepA = .ok g0 at hOk
  let m := g.numHalfEdges
  have hStepA7 : stepA.arcNbr[m + 7]! = m + 3 := by
    have hSig := r3BraidRightStepA_signature
      (g := g) (gR := gR) (x := x) (u := u) (w := w) h
    simpa [stepA, m] using hSig.2.1
  cases hvg : PDGraph.validate stepA with
  | error e =>
      simpa [stepA, Reidemeister.r2RemoveLast, hvg] using hOk
  | ok hv =>
      cases hv
      have hnge : 2 ≤ stepA.n := by
        simp [stepA, r3BraidRightStepA, r3BraidRightGraph]
      have hnlt : ¬ stepA.n < 2 := Nat.not_lt_of_ge hnge
      have hmA : stepA.numHalfEdges = m + 8 := by
        simp [stepA, m, r3BraidRightStepA, r3BraidRightGraph, PDGraph.numHalfEdges,
          Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have hMismatch2 :
          stepA.arcNbr[stepA.numHalfEdges - 4 + 3]! ≠ stepA.numHalfEdges - 8 + 2 := by
        have hsub8 : (m + 8) - 8 = m := Nat.add_sub_cancel m 8
        have h4le8 : 4 ≤ 8 := by
          simpa using (Nat.le_add_left 4 4)
        have hsub4 : (m + 8) - 4 = m + 4 := by
          simpa using (Nat.add_sub_assoc m h4le8)
        have hIdxL : stepA.numHalfEdges - 4 + 3 = m + 7 := by
          calc
            stepA.numHalfEdges - 4 + 3 = ((m + 8) - 4) + 3 := by simpa [hmA]
            _ = (m + 4) + 3 := by simpa [hsub4]
            _ = m + 7 := by omega
        have hStepA7' : stepA.arcNbr[stepA.numHalfEdges - 4 + 3]! = m + 3 := by
          simpa [hIdxL, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hStepA7
        have hRhs : stepA.numHalfEdges - 8 + 2 = m + 2 := by
          calc
            stepA.numHalfEdges - 8 + 2 = ((m + 8) - 8) + 2 := by simpa [hmA]
            _ = m + 2 := by simpa [hsub8, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        intro hEq
        have h32 : m + 3 = m + 2 := by
          calc
            m + 3 = stepA.arcNbr[stepA.numHalfEdges - 4 + 3]! := hStepA7'.symm
            _ = stepA.numHalfEdges - 8 + 2 := hEq
            _ = m + 2 := hRhs
        exact (Nat.ne_of_lt (Nat.lt_succ_self (m + 2))) h32.symm
      have hCond2 :
          ¬stepA.arcNbr[stepA.numHalfEdges - 8 + 2]! = stepA.numHalfEdges - 4 + 3 ∨
            stepA.arcNbr[stepA.numHalfEdges - 4 + 3]! ≠ stepA.numHalfEdges - 8 + 2 :=
        Or.inr hMismatch2
      by_cases hCond1 :
          ¬stepA.arcNbr[stepA.numHalfEdges - 8 + 1]! = stepA.numHalfEdges - 4 ∨
            ¬stepA.arcNbr[stepA.numHalfEdges - 4]! = stepA.numHalfEdges - 8 + 1
      · have hErr :
            (Except.error "r2RemoveLast: internal arc (1↔0) mismatch" : Except String PDGraph) =
              .ok g0 := by
          simpa [Reidemeister.r2RemoveLast, hvg, hnlt, hCond1] using hOk
        cases hErr
      · have hErr :
            (Except.error "r2RemoveLast: internal arc (2↔3) mismatch" : Except String PDGraph) =
              .ok g0 := by
          simpa [Reidemeister.r2RemoveLast, hvg, hnlt, hCond1, hCond2] using hOk
        cases hErr

private theorem r2RemoveLast_ne_ok_of_r3BraidRightStepB
    {g gR g0 : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    Reidemeister.r2RemoveLast (r3BraidRightStepB g x u w) ≠ .ok g0 := by
  intro hOk
  let stepB := r3BraidRightStepB g x u w
  change Reidemeister.r2RemoveLast stepB = .ok g0 at hOk
  let m := g.numHalfEdges
  let x2 := g.arcNbr[x]!
  have hx : x < m :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).1
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  have hx2_lt_m : x2 < m := PDGraph.Valid.get_lt hValidG (i := x) hx
  have hStepB7 : stepB.arcNbr[m + 7]! = x2 := by
    have hSig := r3BraidRightStepB_signature
      (g := g) (gR := gR) (x := x) (u := u) (w := w) h
    simpa [stepB, m, x2] using hSig.2.2.1
  cases hvg : PDGraph.validate stepB with
  | error e =>
      simpa [stepB, Reidemeister.r2RemoveLast, hvg] using hOk
  | ok hv =>
      cases hv
      have hnge : 2 ≤ stepB.n := by
        simp [stepB, r3BraidRightStepB, r3BraidRightGraph]
      have hnlt : ¬ stepB.n < 2 := Nat.not_lt_of_ge hnge
      have hmA : stepB.numHalfEdges = m + 8 := by
        simp [stepB, m, r3BraidRightStepB, r3BraidRightGraph, PDGraph.numHalfEdges,
          Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have hMismatch2 :
          stepB.arcNbr[stepB.numHalfEdges - 4 + 3]! ≠ stepB.numHalfEdges - 8 + 2 := by
        have hsub8 : (m + 8) - 8 = m := Nat.add_sub_cancel m 8
        have h4le8 : 4 ≤ 8 := by
          simpa using (Nat.le_add_left 4 4)
        have hsub4 : (m + 8) - 4 = m + 4 := by
          simpa using (Nat.add_sub_assoc m h4le8)
        have hIdxL : stepB.numHalfEdges - 4 + 3 = m + 7 := by
          calc
            stepB.numHalfEdges - 4 + 3 = ((m + 8) - 4) + 3 := by simpa [hmA]
            _ = (m + 4) + 3 := by simpa [hsub4]
            _ = m + 7 := by omega
        have hStepB7' : stepB.arcNbr[stepB.numHalfEdges - 4 + 3]! = x2 := by
          simpa [hIdxL, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hStepB7
        have hRhs : stepB.numHalfEdges - 8 + 2 = m + 2 := by
          calc
            stepB.numHalfEdges - 8 + 2 = ((m + 8) - 8) + 2 := by simpa [hmA]
            _ = m + 2 := by simpa [hsub8, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        have hx2_lt_m2 : x2 < m + 2 := Nat.lt_of_lt_of_le hx2_lt_m (Nat.le_add_right m 2)
        intro hEq
        have hx2_eq_m2 : x2 = m + 2 := by
          calc
            x2 = stepB.arcNbr[stepB.numHalfEdges - 4 + 3]! := hStepB7'.symm
            _ = stepB.numHalfEdges - 8 + 2 := hEq
            _ = m + 2 := hRhs
        exact (Nat.ne_of_lt hx2_lt_m2) hx2_eq_m2
      have hCond2 :
          ¬stepB.arcNbr[stepB.numHalfEdges - 8 + 2]! = stepB.numHalfEdges - 4 + 3 ∨
            stepB.arcNbr[stepB.numHalfEdges - 4 + 3]! ≠ stepB.numHalfEdges - 8 + 2 :=
        Or.inr hMismatch2
      by_cases hCond1 :
          ¬stepB.arcNbr[stepB.numHalfEdges - 8 + 1]! = stepB.numHalfEdges - 4 ∨
            ¬stepB.arcNbr[stepB.numHalfEdges - 4]! = stepB.numHalfEdges - 8 + 1
      · have hErr :
            (Except.error "r2RemoveLast: internal arc (1↔0) mismatch" : Except String PDGraph) =
              .ok g0 := by
          simpa [Reidemeister.r2RemoveLast, hvg, hnlt, hCond1] using hOk
        cases hErr
      · have hErr :
            (Except.error "r2RemoveLast: internal arc (2↔3) mismatch" : Except String PDGraph) =
              .ok g0 := by
          simpa [Reidemeister.r2RemoveLast, hvg, hnlt, hCond1, hCond2] using hOk
        cases hErr

private theorem r3BraidRightStepA_arc_m_plus_4
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    (r3BraidRightStepA g x u w).arcNbr[m + 4]! = x := by
  let m := g.numHalfEdges
  let nB : Nat := g.n + 3
  let arcNbr := (r3BraidRightGraph g x u w).arcNbr
  have hbase : (4 * nB) - 4 = m + 8 := by
    dsimp [nB, m, PDGraph.numHalfEdges]
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using baseC_eq g.n
  have hm4_lt : m + 4 < (4 * nB - 4) := by
    have : m + 4 < m + 8 := by omega
    simpa [hbase] using this
  have hB0 : (r3BraidRightGraph g x u w).arcNbr[m + 4]! = x :=
    arcNbr_r3BraidRight_baseB0 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hx : x < m :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).1
  have hp_lt : arcNbr[m + 4]! < (4 * nB - 4) := by
    have : x < m + 8 := Nat.lt_of_lt_of_le hx (Nat.le_add_right m 8)
    simpa [arcNbr, hB0, hbase] using this
  have hrew :
      (smoothLastCoreML_rewire nB arcNbr false)[m + 4]! = arcNbr[m + 4]! := by
    have hget := smoothLastCoreML_rewire_getBang nB arcNbr false (m + 4) hm4_lt
    simpa [hp_lt] using hget
  change
    (smoothLastCoreML (r3BraidRightGraph g x u w).freeLoops
      (r3BraidRightGraph g x u w).n
      (r3BraidRightGraph g x u w).arcNbr false).2[m + 4]! = x
  simp [smoothLastCoreML]
  have hnB : (r3BraidRightGraph g x u w).n = nB := by
    simp [nB, r3BraidRightGraph]
  calc
    (smoothLastCoreML_rewire (r3BraidRightGraph g x u w).n
      (r3BraidRightGraph g x u w).arcNbr false)[m + 4]!
        = (smoothLastCoreML_rewire nB arcNbr false)[m + 4]! := by
            simpa [hnB, arcNbr]
    _ = arcNbr[m + 4]! := hrew
    _ = x := by simpa [arcNbr] using hB0

private theorem r3BraidRightStepA_arc_m_plus_6
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    let w2 := g.arcNbr[w]!
    (r3BraidRightStepA g x u w).arcNbr[m + 6]! = w2 := by
  let m := g.numHalfEdges
  let w2 := g.arcNbr[w]!
  let nB : Nat := g.n + 3
  let arcNbr := (r3BraidRightGraph g x u w).arcNbr
  have hbase : (4 * nB) - 4 = m + 8 := by
    dsimp [nB, m, PDGraph.numHalfEdges]
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using baseC_eq g.n
  have hm6_lt : m + 6 < (4 * nB - 4) := by
    have : m + 6 < m + 8 := by omega
    simpa [hbase] using this
  have hB2 : (r3BraidRightGraph g x u w).arcNbr[m + 6]! = w2 :=
    arcNbr_r3BraidRight_baseB2 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  have hw : w < m :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.2
  have hw2_lt : w2 < m := PDGraph.Valid.get_lt hValidG (i := w) hw
  have hp_lt : arcNbr[m + 6]! < (4 * nB - 4) := by
    have : w2 < m + 8 := Nat.lt_of_lt_of_le hw2_lt (Nat.le_add_right m 8)
    simpa [arcNbr, hB2, hbase] using this
  have hrew :
      (smoothLastCoreML_rewire nB arcNbr false)[m + 6]! = arcNbr[m + 6]! := by
    have hget := smoothLastCoreML_rewire_getBang nB arcNbr false (m + 6) hm6_lt
    simpa [hp_lt] using hget
  change
    (smoothLastCoreML (r3BraidRightGraph g x u w).freeLoops
      (r3BraidRightGraph g x u w).n
      (r3BraidRightGraph g x u w).arcNbr false).2[m + 6]! = w2
  simp [smoothLastCoreML]
  have hnB : (r3BraidRightGraph g x u w).n = nB := by
    simp [nB, r3BraidRightGraph]
  calc
    (smoothLastCoreML_rewire (r3BraidRightGraph g x u w).n
      (r3BraidRightGraph g x u w).arcNbr false)[m + 6]!
        = (smoothLastCoreML_rewire nB arcNbr false)[m + 6]! := by
            simpa [hnB, arcNbr]
    _ = arcNbr[m + 6]! := hrew
    _ = w2 := by simpa [arcNbr] using hB2

private theorem r3BraidRightStepB_arc_m_plus_4
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    (r3BraidRightStepB g x u w).arcNbr[m + 4]! = x := by
  let m := g.numHalfEdges
  let nB : Nat := g.n + 3
  let arcNbr := (r3BraidRightGraph g x u w).arcNbr
  have hbase : (4 * nB) - 4 = m + 8 := by
    dsimp [nB, m, PDGraph.numHalfEdges]
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using baseC_eq g.n
  have hm4_lt : m + 4 < (4 * nB - 4) := by
    have : m + 4 < m + 8 := by omega
    simpa [hbase] using this
  have hB0 : (r3BraidRightGraph g x u w).arcNbr[m + 4]! = x :=
    arcNbr_r3BraidRight_baseB0 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hx : x < m :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).1
  have hp_lt : arcNbr[m + 4]! < (4 * nB - 4) := by
    have : x < m + 8 := Nat.lt_of_lt_of_le hx (Nat.le_add_right m 8)
    simpa [arcNbr, hB0, hbase] using this
  have hrew :
      (smoothLastCoreML_rewire nB arcNbr true)[m + 4]! = arcNbr[m + 4]! := by
    have hget := smoothLastCoreML_rewire_getBang nB arcNbr true (m + 4) hm4_lt
    simpa [hp_lt] using hget
  change
    (smoothLastCoreML (r3BraidRightGraph g x u w).freeLoops
      (r3BraidRightGraph g x u w).n
      (r3BraidRightGraph g x u w).arcNbr true).2[m + 4]! = x
  simp [smoothLastCoreML]
  have hnB : (r3BraidRightGraph g x u w).n = nB := by
    simp [nB, r3BraidRightGraph]
  calc
    (smoothLastCoreML_rewire (r3BraidRightGraph g x u w).n
      (r3BraidRightGraph g x u w).arcNbr true)[m + 4]!
        = (smoothLastCoreML_rewire nB arcNbr true)[m + 4]! := by
            simpa [hnB, arcNbr]
    _ = arcNbr[m + 4]! := hrew
    _ = x := by simpa [arcNbr] using hB0

private theorem r3BraidRightStepB_arc_m_plus_6
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    let m := g.numHalfEdges
    let w2 := g.arcNbr[w]!
    (r3BraidRightStepB g x u w).arcNbr[m + 6]! = w2 := by
  let m := g.numHalfEdges
  let w2 := g.arcNbr[w]!
  let nB : Nat := g.n + 3
  let arcNbr := (r3BraidRightGraph g x u w).arcNbr
  have hbase : (4 * nB) - 4 = m + 8 := by
    dsimp [nB, m, PDGraph.numHalfEdges]
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using baseC_eq g.n
  have hm6_lt : m + 6 < (4 * nB - 4) := by
    have : m + 6 < m + 8 := by omega
    simpa [hbase] using this
  have hB2 : (r3BraidRightGraph g x u w).arcNbr[m + 6]! = w2 :=
    arcNbr_r3BraidRight_baseB2 (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  have hw : w < m :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.2
  have hw2_lt : w2 < m := PDGraph.Valid.get_lt hValidG (i := w) hw
  have hp_lt : arcNbr[m + 6]! < (4 * nB - 4) := by
    have : w2 < m + 8 := Nat.lt_of_lt_of_le hw2_lt (Nat.le_add_right m 8)
    simpa [arcNbr, hB2, hbase] using this
  have hrew :
      (smoothLastCoreML_rewire nB arcNbr true)[m + 6]! = arcNbr[m + 6]! := by
    have hget := smoothLastCoreML_rewire_getBang nB arcNbr true (m + 6) hm6_lt
    simpa [hp_lt] using hget
  change
    (smoothLastCoreML (r3BraidRightGraph g x u w).freeLoops
      (r3BraidRightGraph g x u w).n
      (r3BraidRightGraph g x u w).arcNbr true).2[m + 6]! = w2
  simp [smoothLastCoreML]
  have hnB : (r3BraidRightGraph g x u w).n = nB := by
    simp [nB, r3BraidRightGraph]
  calc
    (smoothLastCoreML_rewire (r3BraidRightGraph g x u w).n
      (r3BraidRightGraph g x u w).arcNbr true)[m + 6]!
        = (smoothLastCoreML_rewire nB arcNbr true)[m + 6]! := by
            simpa [hnB, arcNbr]
    _ = arcNbr[m + 6]! := hrew
    _ = w2 := by simpa [arcNbr] using hB2

private theorem r1RemoveLast_pos_ne_ok_of_r3BraidRightStepA
    {g gR g0 : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    Reidemeister.r1RemoveLast (r3BraidRightStepA g x u w) .pos ≠ .ok g0 := by
  intro hOk
  let stepA := r3BraidRightStepA g x u w
  change Reidemeister.r1RemoveLast stepA .pos = .ok g0 at hOk
  let m := g.numHalfEdges
  have hx : x < m :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).1
  have hStepA4 : stepA.arcNbr[m + 4]! = x := by
    simpa [stepA, m] using
      (r3BraidRightStepA_arc_m_plus_4 (g := g) (gR := gR) (x := x) (u := u) (w := w) h)
  cases hvg : PDGraph.validate stepA with
  | error e =>
      simpa [stepA, Reidemeister.r1RemoveLast, hvg] using hOk
  | ok hv =>
      cases hv
      have hnge : 1 ≤ stepA.n := by
        simp [stepA, r3BraidRightStepA, r3BraidRightGraph]
      have hn0 : stepA.n ≠ 0 := Nat.ne_of_gt hnge
      have hmA : stepA.numHalfEdges = m + 8 := by
        simp [stepA, m, r3BraidRightStepA, r3BraidRightGraph, PDGraph.numHalfEdges,
          Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have h4le8 : 4 ≤ 8 := by
        simpa using (Nat.le_add_left 4 4)
      have hsub4 : (m + 8) - 4 = m + 4 := by
        simpa using (Nat.add_sub_assoc m h4le8)
      have hIntAIdx : stepA.numHalfEdges - 4 = m + 4 := by
        calc
          stepA.numHalfEdges - 4 = (m + 8) - 4 := by simpa [hmA]
          _ = m + 4 := by simpa [hsub4]
      have hIntA : stepA.arcNbr[stepA.numHalfEdges - 4]! = x := by
        simpa [hIntAIdx, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hStepA4
      have hIntBIdx : stepA.numHalfEdges - 4 + 1 = m + 5 := by
        calc
          stepA.numHalfEdges - 4 + 1 = ((m + 8) - 4) + 1 := by simpa [hmA]
          _ = (m + 4) + 1 := by simpa [hsub4]
          _ = m + 5 := by rfl
      have hMismatch :
          stepA.arcNbr[stepA.numHalfEdges - 4]! ≠ stepA.numHalfEdges - 4 + 1 := by
        intro hEq
        have hx_eq_m5 : x = m + 5 := by
          calc
            x = stepA.arcNbr[stepA.numHalfEdges - 4]! := hIntA.symm
            _ = stepA.numHalfEdges - 4 + 1 := hEq
            _ = m + 5 := hIntBIdx
        have hx_lt_m5 : x < m + 5 := Nat.lt_of_lt_of_le hx (Nat.le_add_right m 5)
        exact (Nat.ne_of_lt hx_lt_m5) hx_eq_m5
      have hCond :
          ¬stepA.arcNbr[stepA.numHalfEdges - 4]! = stepA.numHalfEdges - 4 + 1 ∨
            ¬stepA.arcNbr[stepA.numHalfEdges - 4 + 1]! = stepA.numHalfEdges - 4 :=
        Or.inl hMismatch
      have hErr :
          (Except.error "r1RemoveLast: internal loop arc mismatch" : Except String PDGraph) =
            .ok g0 := by
        simpa [Reidemeister.r1RemoveLast, hvg, hn0, hCond] using hOk
      cases hErr

private theorem r1RemoveLast_neg_ne_ok_of_r3BraidRightStepA
    {g gR g0 : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    Reidemeister.r1RemoveLast (r3BraidRightStepA g x u w) .neg ≠ .ok g0 := by
  intro hOk
  let stepA := r3BraidRightStepA g x u w
  change Reidemeister.r1RemoveLast stepA .neg = .ok g0 at hOk
  let m := g.numHalfEdges
  let w2 := g.arcNbr[w]!
  have hw : w < m :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.2
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  have hw2_lt_m : w2 < m := PDGraph.Valid.get_lt hValidG (i := w) hw
  have hStepA6 : stepA.arcNbr[m + 6]! = w2 := by
    simpa [stepA, m, w2] using
      (r3BraidRightStepA_arc_m_plus_6 (g := g) (gR := gR) (x := x) (u := u) (w := w) h)
  cases hvg : PDGraph.validate stepA with
  | error e =>
      simpa [stepA, Reidemeister.r1RemoveLast, hvg] using hOk
  | ok hv =>
      cases hv
      have hnge : 1 ≤ stepA.n := by
        simp [stepA, r3BraidRightStepA, r3BraidRightGraph]
      have hn0 : stepA.n ≠ 0 := Nat.ne_of_gt hnge
      have hmA : stepA.numHalfEdges = m + 8 := by
        simp [stepA, m, r3BraidRightStepA, r3BraidRightGraph, PDGraph.numHalfEdges,
          Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have h4le8 : 4 ≤ 8 := by
        simpa using (Nat.le_add_left 4 4)
      have hsub4 : (m + 8) - 4 = m + 4 := by
        simpa using (Nat.add_sub_assoc m h4le8)
      have hIntBIdx : stepA.numHalfEdges - 4 + 2 = m + 6 := by
        calc
          stepA.numHalfEdges - 4 + 2 = ((m + 8) - 4) + 2 := by simpa [hmA]
          _ = (m + 4) + 2 := by simpa [hsub4]
          _ = m + 6 := by rfl
      have hIntB : stepA.arcNbr[stepA.numHalfEdges - 4 + 2]! = w2 := by
        simpa [hIntBIdx, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hStepA6
      have hIntAIdx : stepA.numHalfEdges - 4 + 1 = m + 5 := by
        calc
          stepA.numHalfEdges - 4 + 1 = ((m + 8) - 4) + 1 := by simpa [hmA]
          _ = (m + 4) + 1 := by simpa [hsub4]
          _ = m + 5 := by rfl
      have hMismatch :
          stepA.arcNbr[stepA.numHalfEdges - 4 + 2]! ≠ stepA.numHalfEdges - 4 + 1 := by
        intro hEq
        have hw2_eq_m5 : w2 = m + 5 := by
          calc
            w2 = stepA.arcNbr[stepA.numHalfEdges - 4 + 2]! := hIntB.symm
            _ = stepA.numHalfEdges - 4 + 1 := hEq
            _ = m + 5 := hIntAIdx
        have hw2_lt_m5 : w2 < m + 5 := Nat.lt_of_lt_of_le hw2_lt_m (Nat.le_add_right m 5)
        exact (Nat.ne_of_lt hw2_lt_m5) hw2_eq_m5
      have hCond :
          ¬stepA.arcNbr[stepA.numHalfEdges - 4 + 1]! = stepA.numHalfEdges - 4 + 2 ∨
            ¬stepA.arcNbr[stepA.numHalfEdges - 4 + 2]! = stepA.numHalfEdges - 4 + 1 :=
        Or.inr hMismatch
      have hErr :
          (Except.error "r1RemoveLast: internal loop arc mismatch" : Except String PDGraph) =
            .ok g0 := by
        simpa [Reidemeister.r1RemoveLast, hvg, hn0, hCond] using hOk
      cases hErr

private theorem r1RemoveLast_pos_ne_ok_of_r3BraidRightStepB
    {g gR g0 : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    Reidemeister.r1RemoveLast (r3BraidRightStepB g x u w) .pos ≠ .ok g0 := by
  intro hOk
  let stepB := r3BraidRightStepB g x u w
  change Reidemeister.r1RemoveLast stepB .pos = .ok g0 at hOk
  let m := g.numHalfEdges
  have hx : x < m :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).1
  have hStepB4 : stepB.arcNbr[m + 4]! = x := by
    simpa [stepB, m] using
      (r3BraidRightStepB_arc_m_plus_4 (g := g) (gR := gR) (x := x) (u := u) (w := w) h)
  cases hvg : PDGraph.validate stepB with
  | error e =>
      simpa [stepB, Reidemeister.r1RemoveLast, hvg] using hOk
  | ok hv =>
      cases hv
      have hnge : 1 ≤ stepB.n := by
        simp [stepB, r3BraidRightStepB, r3BraidRightGraph]
      have hn0 : stepB.n ≠ 0 := Nat.ne_of_gt hnge
      have hmA : stepB.numHalfEdges = m + 8 := by
        simp [stepB, m, r3BraidRightStepB, r3BraidRightGraph, PDGraph.numHalfEdges,
          Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have h4le8 : 4 ≤ 8 := by
        simpa using (Nat.le_add_left 4 4)
      have hsub4 : (m + 8) - 4 = m + 4 := by
        simpa using (Nat.add_sub_assoc m h4le8)
      have hIntAIdx : stepB.numHalfEdges - 4 = m + 4 := by
        calc
          stepB.numHalfEdges - 4 = (m + 8) - 4 := by simpa [hmA]
          _ = m + 4 := by simpa [hsub4]
      have hIntA : stepB.arcNbr[stepB.numHalfEdges - 4]! = x := by
        simpa [hIntAIdx, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hStepB4
      have hIntBIdx : stepB.numHalfEdges - 4 + 1 = m + 5 := by
        calc
          stepB.numHalfEdges - 4 + 1 = ((m + 8) - 4) + 1 := by simpa [hmA]
          _ = (m + 4) + 1 := by simpa [hsub4]
          _ = m + 5 := by rfl
      have hMismatch :
          stepB.arcNbr[stepB.numHalfEdges - 4]! ≠ stepB.numHalfEdges - 4 + 1 := by
        intro hEq
        have hx_eq_m5 : x = m + 5 := by
          calc
            x = stepB.arcNbr[stepB.numHalfEdges - 4]! := hIntA.symm
            _ = stepB.numHalfEdges - 4 + 1 := hEq
            _ = m + 5 := hIntBIdx
        have hx_lt_m5 : x < m + 5 := Nat.lt_of_lt_of_le hx (Nat.le_add_right m 5)
        exact (Nat.ne_of_lt hx_lt_m5) hx_eq_m5
      have hCond :
          ¬stepB.arcNbr[stepB.numHalfEdges - 4]! = stepB.numHalfEdges - 4 + 1 ∨
            ¬stepB.arcNbr[stepB.numHalfEdges - 4 + 1]! = stepB.numHalfEdges - 4 :=
        Or.inl hMismatch
      have hErr :
          (Except.error "r1RemoveLast: internal loop arc mismatch" : Except String PDGraph) =
            .ok g0 := by
        simpa [Reidemeister.r1RemoveLast, hvg, hn0, hCond] using hOk
      cases hErr

private theorem r1RemoveLast_neg_ne_ok_of_r3BraidRightStepB
    {g gR g0 : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    Reidemeister.r1RemoveLast (r3BraidRightStepB g x u w) .neg ≠ .ok g0 := by
  intro hOk
  let stepB := r3BraidRightStepB g x u w
  change Reidemeister.r1RemoveLast stepB .neg = .ok g0 at hOk
  let m := g.numHalfEdges
  let w2 := g.arcNbr[w]!
  have hw : w < m :=
    (lt_numHalfEdges_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h).2.2
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  have hw2_lt_m : w2 < m := PDGraph.Valid.get_lt hValidG (i := w) hw
  have hStepB6 : stepB.arcNbr[m + 6]! = w2 := by
    simpa [stepB, m, w2] using
      (r3BraidRightStepB_arc_m_plus_6 (g := g) (gR := gR) (x := x) (u := u) (w := w) h)
  cases hvg : PDGraph.validate stepB with
  | error e =>
      simpa [stepB, Reidemeister.r1RemoveLast, hvg] using hOk
  | ok hv =>
      cases hv
      have hnge : 1 ≤ stepB.n := by
        simp [stepB, r3BraidRightStepB, r3BraidRightGraph]
      have hn0 : stepB.n ≠ 0 := Nat.ne_of_gt hnge
      have hmA : stepB.numHalfEdges = m + 8 := by
        simp [stepB, m, r3BraidRightStepB, r3BraidRightGraph, PDGraph.numHalfEdges,
          Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have h4le8 : 4 ≤ 8 := by
        simpa using (Nat.le_add_left 4 4)
      have hsub4 : (m + 8) - 4 = m + 4 := by
        simpa using (Nat.add_sub_assoc m h4le8)
      have hIntBIdx : stepB.numHalfEdges - 4 + 2 = m + 6 := by
        calc
          stepB.numHalfEdges - 4 + 2 = ((m + 8) - 4) + 2 := by simpa [hmA]
          _ = (m + 4) + 2 := by simpa [hsub4]
          _ = m + 6 := by rfl
      have hIntB : stepB.arcNbr[stepB.numHalfEdges - 4 + 2]! = w2 := by
        simpa [hIntBIdx, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hStepB6
      have hIntAIdx : stepB.numHalfEdges - 4 + 1 = m + 5 := by
        calc
          stepB.numHalfEdges - 4 + 1 = ((m + 8) - 4) + 1 := by simpa [hmA]
          _ = (m + 4) + 1 := by simpa [hsub4]
          _ = m + 5 := by rfl
      have hMismatch :
          stepB.arcNbr[stepB.numHalfEdges - 4 + 2]! ≠ stepB.numHalfEdges - 4 + 1 := by
        intro hEq
        have hw2_eq_m5 : w2 = m + 5 := by
          calc
            w2 = stepB.arcNbr[stepB.numHalfEdges - 4 + 2]! := hIntB.symm
            _ = stepB.numHalfEdges - 4 + 1 := hEq
            _ = m + 5 := hIntAIdx
        have hw2_lt_m5 : w2 < m + 5 := Nat.lt_of_lt_of_le hw2_lt_m (Nat.le_add_right m 5)
        exact (Nat.ne_of_lt hw2_lt_m5) hw2_eq_m5
      have hCond :
          ¬stepB.arcNbr[stepB.numHalfEdges - 4 + 1]! = stepB.numHalfEdges - 4 + 2 ∨
            ¬stepB.arcNbr[stepB.numHalfEdges - 4 + 2]! = stepB.numHalfEdges - 4 + 1 :=
        Or.inr hMismatch
      have hErr :
          (Except.error "r1RemoveLast: internal loop arc mismatch" : Except String PDGraph) =
            .ok g0 := by
        simpa [Reidemeister.r1RemoveLast, hvg, hn0, hCond] using hOk
      cases hErr

private theorem r3BraidLeftStepB_arc_m_plus_4
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    let m := g.numHalfEdges
    (r3BraidLeftStepB g x u w).arcNbr[m + 4]! = m + 3 := by
  let m := g.numHalfEdges
  let nB : Nat := g.n + 3
  let arcNbr := (r3BraidLeftGraph g x u w).arcNbr
  have hbase : (4 * nB) - 4 = m + 8 := by
    dsimp [nB, m, PDGraph.numHalfEdges]
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using baseC_eq g.n
  have hm4_lt : m + 4 < (4 * nB - 4) := by
    have : m + 4 < m + 8 := Nat.add_lt_add_left (by decide : (4 : Nat) < 8) m
    simpa [hbase] using this
  have hB0 : (r3BraidLeftGraph g x u w).arcNbr[m + 4]! = m + 3 :=
    arcNbr_r3BraidLeft_baseB0 (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hp_lt : arcNbr[m + 4]! < (4 * nB - 4) := by
    have : m + 3 < m + 8 := Nat.add_lt_add_left (by decide : (3 : Nat) < 8) m
    simpa [arcNbr, hB0, hbase] using this
  have hrew :
      (smoothLastCoreML_rewire nB arcNbr true)[m + 4]! = arcNbr[m + 4]! := by
    have hget := smoothLastCoreML_rewire_getBang nB arcNbr true (m + 4) hm4_lt
    simpa [hp_lt] using hget
  change
    (smoothLastCoreML (r3BraidLeftGraph g x u w).freeLoops
      (r3BraidLeftGraph g x u w).n
      (r3BraidLeftGraph g x u w).arcNbr true).2[m + 4]! = m + 3
  simp [smoothLastCoreML]
  have hnB : (r3BraidLeftGraph g x u w).n = nB := by
    simp [nB, r3BraidLeftGraph]
  calc
    (smoothLastCoreML_rewire (r3BraidLeftGraph g x u w).n
      (r3BraidLeftGraph g x u w).arcNbr true)[m + 4]!
        = (smoothLastCoreML_rewire nB arcNbr true)[m + 4]! := by
            simpa [hnB, arcNbr]
    _ = arcNbr[m + 4]! := hrew
    _ = m + 3 := by simpa [arcNbr] using hB0

private theorem r1RemoveLast_pos_ne_ok_of_r3BraidLeftStepB
    {g gL g0 : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    Reidemeister.r1RemoveLast (r3BraidLeftStepB g x u w) .pos ≠ .ok g0 := by
  intro hOk
  let stepB := r3BraidLeftStepB g x u w
  change Reidemeister.r1RemoveLast stepB .pos = .ok g0 at hOk
  let m := g.numHalfEdges
  have hStepB4 : stepB.arcNbr[m + 4]! = m + 3 := by
    simpa [stepB, m] using
      (r3BraidLeftStepB_arc_m_plus_4 (g := g) (gL := gL) (x := x) (u := u) (w := w) h)
  cases hvg : PDGraph.validate stepB with
  | error e =>
      simpa [stepB, Reidemeister.r1RemoveLast, hvg] using hOk
  | ok hv =>
      cases hv
      have hnge : 1 ≤ stepB.n := by
        simp [stepB, r3BraidLeftStepB, r3BraidLeftGraph]
      have hn0 : stepB.n ≠ 0 := Nat.ne_of_gt hnge
      have hmA : stepB.numHalfEdges = m + 8 := by
        simp [stepB, m, r3BraidLeftStepB, r3BraidLeftGraph, PDGraph.numHalfEdges,
          Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have h4le8 : 4 ≤ 8 := by
        simpa using (Nat.le_add_left 4 4)
      have hsub4 : (m + 8) - 4 = m + 4 := by
        simpa using (Nat.add_sub_assoc m h4le8)
      have hIntAIdx : stepB.numHalfEdges - 4 = m + 4 := by
        calc
          stepB.numHalfEdges - 4 = (m + 8) - 4 := by simpa [hmA]
          _ = m + 4 := by simpa [hsub4]
      have hIntA : stepB.arcNbr[stepB.numHalfEdges - 4]! = m + 3 := by
        simpa [hIntAIdx, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hStepB4
      have hIntBIdx : stepB.numHalfEdges - 4 + 1 = m + 5 := by
        calc
          stepB.numHalfEdges - 4 + 1 = ((m + 8) - 4) + 1 := by simpa [hmA]
          _ = (m + 4) + 1 := by simpa [hsub4]
          _ = m + 5 := by rfl
      have hMismatch :
          stepB.arcNbr[stepB.numHalfEdges - 4]! ≠ stepB.numHalfEdges - 4 + 1 := by
        intro hEq
        have h35 : m + 3 = m + 5 := by
          calc
            m + 3 = stepB.arcNbr[stepB.numHalfEdges - 4]! := hIntA.symm
            _ = stepB.numHalfEdges - 4 + 1 := hEq
            _ = m + 5 := hIntBIdx
        exact (Nat.ne_of_lt (Nat.add_lt_add_left (by decide : (3 : Nat) < 5) m)) h35
      have hCond :
          ¬stepB.arcNbr[stepB.numHalfEdges - 4]! = stepB.numHalfEdges - 4 + 1 ∨
            ¬stepB.arcNbr[stepB.numHalfEdges - 4 + 1]! = stepB.numHalfEdges - 4 :=
        Or.inl hMismatch
      have hErr :
          (Except.error "r1RemoveLast: internal loop arc mismatch" : Except String PDGraph) =
            .ok g0 := by
        simpa [Reidemeister.r1RemoveLast, hvg, hn0, hCond] using hOk
      cases hErr

private theorem r1RemoveLast_neg_ne_ok_of_r3BraidLeftStepB
    {g gL g0 : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    Reidemeister.r1RemoveLast (r3BraidLeftStepB g x u w) .neg ≠ .ok g0 := by
  intro hOk
  let stepB := r3BraidLeftStepB g x u w
  change Reidemeister.r1RemoveLast stepB .neg = .ok g0 at hOk
  let m := g.numHalfEdges
  let w2 := g.arcNbr[w]!
  have hw : w < m :=
    (lt_numHalfEdges_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h).2.2
  have hvg0 : PDGraph.validate g = .ok () :=
    validate_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hValidG : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok hvg0
  have hw2_lt_m : w2 < m := PDGraph.Valid.get_lt hValidG (i := w) hw
  have hStepB6 : stepB.arcNbr[m + 6]! = w2 := by
    have hSig := r3BraidLeftStepB_signature
      (g := g) (gL := gL) (x := x) (u := u) (w := w) h
    simpa [stepB, m, w2] using hSig.2.2.1
  cases hvg : PDGraph.validate stepB with
  | error e =>
      simpa [stepB, Reidemeister.r1RemoveLast, hvg] using hOk
  | ok hv =>
      cases hv
      have hnge : 1 ≤ stepB.n := by
        simp [stepB, r3BraidLeftStepB, r3BraidLeftGraph]
      have hn0 : stepB.n ≠ 0 := Nat.ne_of_gt hnge
      have hmA : stepB.numHalfEdges = m + 8 := by
        simp [stepB, m, r3BraidLeftStepB, r3BraidLeftGraph, PDGraph.numHalfEdges,
          Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have h4le8 : 4 ≤ 8 := by
        simpa using (Nat.le_add_left 4 4)
      have hsub4 : (m + 8) - 4 = m + 4 := by
        simpa using (Nat.add_sub_assoc m h4le8)
      have hIntBIdx : stepB.numHalfEdges - 4 + 2 = m + 6 := by
        calc
          stepB.numHalfEdges - 4 + 2 = ((m + 8) - 4) + 2 := by simpa [hmA]
          _ = (m + 4) + 2 := by simpa [hsub4]
          _ = m + 6 := by rfl
      have hIntB : stepB.arcNbr[stepB.numHalfEdges - 4 + 2]! = w2 := by
        simpa [hIntBIdx, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hStepB6
      have hIntAIdx : stepB.numHalfEdges - 4 + 1 = m + 5 := by
        calc
          stepB.numHalfEdges - 4 + 1 = ((m + 8) - 4) + 1 := by simpa [hmA]
          _ = (m + 4) + 1 := by simpa [hsub4]
          _ = m + 5 := by rfl
      have hMismatch :
          stepB.arcNbr[stepB.numHalfEdges - 4 + 2]! ≠ stepB.numHalfEdges - 4 + 1 := by
        intro hEq
        have hw2_lt_m5 : w2 < m + 5 := Nat.lt_of_lt_of_le hw2_lt_m (Nat.le_add_right m 5)
        have hw2_eq_m5 : w2 = m + 5 := by
          calc
            w2 = stepB.arcNbr[stepB.numHalfEdges - 4 + 2]! := hIntB.symm
            _ = stepB.numHalfEdges - 4 + 1 := hEq
            _ = m + 5 := hIntAIdx
        exact (Nat.ne_of_lt hw2_lt_m5) hw2_eq_m5
      have hCond :
          ¬stepB.arcNbr[stepB.numHalfEdges - 4 + 1]! = stepB.numHalfEdges - 4 + 2 ∨
            ¬stepB.arcNbr[stepB.numHalfEdges - 4 + 2]! = stepB.numHalfEdges - 4 + 1 :=
        Or.inr hMismatch
      have hErr :
          (Except.error "r1RemoveLast: internal loop arc mismatch" : Except String PDGraph) =
            .ok g0 := by
        simpa [Reidemeister.r1RemoveLast, hvg, hn0, hCond] using hOk
      cases hErr

private theorem validate_r3BraidLeftStepB_of_r3BraidLeft_ok
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    PDGraph.validate (r3BraidLeftStepB g x u w) = .ok () := by
  have hValidL : PDGraph.Valid (r3BraidLeftGraph g x u w) :=
    r3BraidLeftGraph_valid_of_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hnL : 0 < (r3BraidLeftGraph g x u w).n := by
    simp [r3BraidLeftGraph]
  have hValidL0 :
      PDGraph.Valid
        { freeLoops := 0
          n := (r3BraidLeftGraph g x u w).n
          arcNbr := (r3BraidLeftGraph g x u w).arcNbr } := by
    simpa [PDGraph.Valid] using hValidL
  have hSmoothValid :
      PDGraph.Valid
        { freeLoops := 0
          n := (r3BraidLeftGraph g x u w).n - 1
          arcNbr := smoothLastCoreML_rewire (r3BraidLeftGraph g x u w).n
            (r3BraidLeftGraph g x u w).arcNbr true } :=
    smoothLastCoreML_valid
      (n := (r3BraidLeftGraph g x u w).n)
      (arcNbr := (r3BraidLeftGraph g x u w).arcNbr)
      (isB := true) hnL hValidL0
  have hStepValid : PDGraph.Valid (r3BraidLeftStepB g x u w) := by
    simpa [r3BraidLeftStepB, smoothLastCoreML, PDGraph.Valid] using hSmoothValid
  exact PDGraph.validate_eq_ok_of_valid hStepValid

private theorem bracketGraphML_leftStepB_skein_of_r3BraidLeft_ok_closed
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    bracketGraphML (r3BraidLeftStepB g x u w) =
      (do
        let a ← bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
          (r3BraidLeftStepBA g x u w)
        let b ← bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
          (r3BraidLeftStepBB g x u w)
        return (AML * a) + (AinvML * b)) := by
  have hvgB : PDGraph.validate (r3BraidLeftStepB g x u w) = .ok () :=
    validate_r3BraidLeftStepB_of_r3BraidLeft_ok
      (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hr1pB : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidLeftStepB g x u w) .pos ≠ .ok g0 := by
    intro g0 hOk
    exact (r1RemoveLast_pos_ne_ok_of_r3BraidLeftStepB
      (g := g) (gL := gL) (g0 := g0) (x := x) (u := u) (w := w) h) hOk
  have hr1nB : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidLeftStepB g x u w) .neg ≠ .ok g0 := by
    intro g0 hOk
    exact (r1RemoveLast_neg_ne_ok_of_r3BraidLeftStepB
      (g := g) (gL := gL) (g0 := g0) (x := x) (u := u) (w := w) h) hOk
  have hr2B : ∀ g0 : PDGraph,
      Reidemeister.r2RemoveLast (r3BraidLeftStepB g x u w) ≠ .ok g0 := by
    intro g0 hOk
    exact (r2RemoveLast_ne_ok_of_r3BraidLeftStepB
      (g := g) (gL := gL) (g0 := g0) (x := x) (u := u) (w := w) h) hOk
  exact bracketGraphML_leftStepB_skein_of_no_shortcuts
    (g := g) (x := x) (u := u) (w := w) hvgB hr1pB hr1nB hr2B

private theorem validate_r3BraidRightStepA_of_r3BraidRight_ok
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    PDGraph.validate (r3BraidRightStepA g x u w) = .ok () := by
  have hValidR : PDGraph.Valid (r3BraidRightGraph g x u w) :=
    r3BraidRightGraph_valid_of_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hnR : 0 < (r3BraidRightGraph g x u w).n := by
    simp [r3BraidRightGraph]
  have hValidR0 :
      PDGraph.Valid
        { freeLoops := 0
          n := (r3BraidRightGraph g x u w).n
          arcNbr := (r3BraidRightGraph g x u w).arcNbr } := by
    simpa [PDGraph.Valid] using hValidR
  have hSmoothValid :
      PDGraph.Valid
        { freeLoops := 0
          n := (r3BraidRightGraph g x u w).n - 1
          arcNbr := smoothLastCoreML_rewire (r3BraidRightGraph g x u w).n
            (r3BraidRightGraph g x u w).arcNbr false } :=
    smoothLastCoreML_valid
      (n := (r3BraidRightGraph g x u w).n)
      (arcNbr := (r3BraidRightGraph g x u w).arcNbr)
      (isB := false) hnR hValidR0
  have hStepValid : PDGraph.Valid (r3BraidRightStepA g x u w) := by
    simpa [r3BraidRightStepA, smoothLastCoreML, PDGraph.Valid] using hSmoothValid
  exact PDGraph.validate_eq_ok_of_valid hStepValid

private theorem validate_r3BraidRightStepB_of_r3BraidRight_ok
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    PDGraph.validate (r3BraidRightStepB g x u w) = .ok () := by
  have hValidR : PDGraph.Valid (r3BraidRightGraph g x u w) :=
    r3BraidRightGraph_valid_of_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hnR : 0 < (r3BraidRightGraph g x u w).n := by
    simp [r3BraidRightGraph]
  have hValidR0 :
      PDGraph.Valid
        { freeLoops := 0
          n := (r3BraidRightGraph g x u w).n
          arcNbr := (r3BraidRightGraph g x u w).arcNbr } := by
    simpa [PDGraph.Valid] using hValidR
  have hSmoothValid :
      PDGraph.Valid
        { freeLoops := 0
          n := (r3BraidRightGraph g x u w).n - 1
          arcNbr := smoothLastCoreML_rewire (r3BraidRightGraph g x u w).n
            (r3BraidRightGraph g x u w).arcNbr true } :=
    smoothLastCoreML_valid
      (n := (r3BraidRightGraph g x u w).n)
      (arcNbr := (r3BraidRightGraph g x u w).arcNbr)
      (isB := true) hnR hValidR0
  have hStepValid : PDGraph.Valid (r3BraidRightStepB g x u w) := by
    simpa [r3BraidRightStepB, smoothLastCoreML, PDGraph.Valid] using hSmoothValid
  exact PDGraph.validate_eq_ok_of_valid hStepValid

/--
Right-A second-level skein unfolding with `r2` obligation discharged from
executable R3-right success; `r1` obligations remain explicit inputs.
-/
private theorem bracketGraphML_rightStepA_skein_of_r3BraidRight_ok
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hvgA : PDGraph.validate (r3BraidRightStepA g x u w) = .ok ())
    (hr1pA : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidRightStepA g x u w) .pos ≠ .ok g0)
    (hr1nA : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidRightStepA g x u w) .neg ≠ .ok g0) :
    bracketGraphML (r3BraidRightStepA g x u w) =
      (do
        let a ← bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
          (r3BraidRightStepAA g x u w)
        let b ← bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
          (r3BraidRightStepAB g x u w)
        return (AML * a) + (AinvML * b)) := by
  have hr2A : ∀ g0 : PDGraph,
      Reidemeister.r2RemoveLast (r3BraidRightStepA g x u w) ≠ .ok g0 := by
    intro g0 hOk
    exact (r2RemoveLast_ne_ok_of_r3BraidRightStepA
      (g := g) (gR := gR) (g0 := g0) (x := x) (u := u) (w := w) h) hOk
  exact bracketGraphML_rightStepA_skein_of_no_shortcuts
    (g := g) (x := x) (u := u) (w := w) hvgA hr1pA hr1nA hr2A

/--
Right-B second-level skein unfolding with `r2` obligation discharged from
executable R3-right success; `r1` obligations remain explicit inputs.
-/
private theorem bracketGraphML_rightStepB_skein_of_r3BraidRight_ok
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hvgB : PDGraph.validate (r3BraidRightStepB g x u w) = .ok ())
    (hr1pB : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidRightStepB g x u w) .pos ≠ .ok g0)
    (hr1nB : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidRightStepB g x u w) .neg ≠ .ok g0) :
    bracketGraphML (r3BraidRightStepB g x u w) =
      (do
        let a ← bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
          (r3BraidRightStepBA g x u w)
        let b ← bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
          (r3BraidRightStepBB g x u w)
        return (AML * a) + (AinvML * b)) := by
  have hr2B : ∀ g0 : PDGraph,
      Reidemeister.r2RemoveLast (r3BraidRightStepB g x u w) ≠ .ok g0 := by
    intro g0 hOk
    exact (r2RemoveLast_ne_ok_of_r3BraidRightStepB
      (g := g) (gR := gR) (g0 := g0) (x := x) (u := u) (w := w) h) hOk
  exact bracketGraphML_rightStepB_skein_of_no_shortcuts
    (g := g) (x := x) (u := u) (w := w) hvgB hr1pB hr1nB hr2B

private theorem bracketGraphML_rightStepA_skein_of_r3BraidRight_ok_closed
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    bracketGraphML (r3BraidRightStepA g x u w) =
      (do
        let a ← bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
          (r3BraidRightStepAA g x u w)
        let b ← bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
          (r3BraidRightStepAB g x u w)
        return (AML * a) + (AinvML * b)) := by
  have hvgA : PDGraph.validate (r3BraidRightStepA g x u w) = .ok () :=
    validate_r3BraidRightStepA_of_r3BraidRight_ok
      (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hr1pA : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidRightStepA g x u w) .pos ≠ .ok g0 := by
    intro g0 hOk
    exact (r1RemoveLast_pos_ne_ok_of_r3BraidRightStepA
      (g := g) (gR := gR) (g0 := g0) (x := x) (u := u) (w := w) h) hOk
  have hr1nA : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidRightStepA g x u w) .neg ≠ .ok g0 := by
    intro g0 hOk
    exact (r1RemoveLast_neg_ne_ok_of_r3BraidRightStepA
      (g := g) (gR := gR) (g0 := g0) (x := x) (u := u) (w := w) h) hOk
  exact bracketGraphML_rightStepA_skein_of_r3BraidRight_ok
    (g := g) (gR := gR) (x := x) (u := u) (w := w) h hvgA hr1pA hr1nA

private theorem bracketGraphML_rightStepB_skein_of_r3BraidRight_ok_closed
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    bracketGraphML (r3BraidRightStepB g x u w) =
      (do
        let a ← bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
          (r3BraidRightStepBA g x u w)
        let b ← bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
          (r3BraidRightStepBB g x u w)
        return (AML * a) + (AinvML * b)) := by
  have hvgB : PDGraph.validate (r3BraidRightStepB g x u w) = .ok () :=
    validate_r3BraidRightStepB_of_r3BraidRight_ok
      (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hr1pB : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidRightStepB g x u w) .pos ≠ .ok g0 := by
    intro g0 hOk
    exact (r1RemoveLast_pos_ne_ok_of_r3BraidRightStepB
      (g := g) (gR := gR) (g0 := g0) (x := x) (u := u) (w := w) h) hOk
  have hr1nB : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidRightStepB g x u w) .neg ≠ .ok g0 := by
    intro g0 hOk
    exact (r1RemoveLast_neg_ne_ok_of_r3BraidRightStepB
      (g := g) (gR := gR) (g0 := g0) (x := x) (u := u) (w := w) h) hOk
  exact bracketGraphML_rightStepB_skein_of_r3BraidRight_ok
    (g := g) (gR := gR) (x := x) (u := u) (w := w) h hvgB hr1pB hr1nB

private theorem r3SkeinStep_right_two_level_expanded_of_r3BraidRight_ok
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    r3SkeinStep (r3BraidRightGraph g x u w) =
      (do
        let a ←
          (do
            let aa ← bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
              (r3BraidRightStepAA g x u w)
            let ab ← bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
              (r3BraidRightStepAB g x u w)
            return (AML * aa) + (AinvML * ab))
        let b ←
          (do
            let ba ← bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
              (r3BraidRightStepBA g x u w)
            let bb ← bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
              (r3BraidRightStepBB g x u w)
            return (AML * ba) + (AinvML * bb))
        return (AML * a) + (AinvML * b)) := by
  have hcanon := r3SkeinStep_right_canonical_expanded g x u w
  have hvgA : PDGraph.validate (r3BraidRightStepA g x u w) = .ok () :=
    validate_r3BraidRightStepA_of_r3BraidRight_ok
      (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hvgB : PDGraph.validate (r3BraidRightStepB g x u w) = .ok () :=
    validate_r3BraidRightStepB_of_r3BraidRight_ok
      (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hAaux :
      bracketGraphMLAux ((r3BraidRightGraph g x u w).n - 1) (r3BraidRightStepA g x u w) =
        bracketGraphML (r3BraidRightStepA g x u w) := by
    have hAuxEq :
        bracketGraphMLAux (r3BraidRightStepA g x u w).n (r3BraidRightStepA g x u w) =
          bracketGraphML (r3BraidRightStepA g x u w) := by
      simp [bracketGraphML, hvgA]
    calc
      bracketGraphMLAux ((r3BraidRightGraph g x u w).n - 1) (r3BraidRightStepA g x u w)
          = bracketGraphMLAux (r3BraidRightStepA g x u w).n (r3BraidRightStepA g x u w) := by
              simp [r3BraidRightStepA, r3BraidRightGraph]
      _ = bracketGraphML (r3BraidRightStepA g x u w) := hAuxEq
  have hBaux :
      bracketGraphMLAux ((r3BraidRightGraph g x u w).n - 1) (r3BraidRightStepB g x u w) =
        bracketGraphML (r3BraidRightStepB g x u w) := by
    have hAuxEq :
        bracketGraphMLAux (r3BraidRightStepB g x u w).n (r3BraidRightStepB g x u w) =
          bracketGraphML (r3BraidRightStepB g x u w) := by
      simp [bracketGraphML, hvgB]
    calc
      bracketGraphMLAux ((r3BraidRightGraph g x u w).n - 1) (r3BraidRightStepB g x u w)
          = bracketGraphMLAux (r3BraidRightStepB g x u w).n (r3BraidRightStepB g x u w) := by
              simp [r3BraidRightStepB, r3BraidRightGraph]
      _ = bracketGraphML (r3BraidRightStepB g x u w) := hAuxEq
  have hAclosed := bracketGraphML_rightStepA_skein_of_r3BraidRight_ok_closed
    (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  have hBclosed := bracketGraphML_rightStepB_skein_of_r3BraidRight_ok_closed
    (g := g) (gR := gR) (x := x) (u := u) (w := w) h
  calc
    r3SkeinStep (r3BraidRightGraph g x u w)
        = (do
            let a ← bracketGraphMLAux ((r3BraidRightGraph g x u w).n - 1)
              (r3BraidRightStepA g x u w)
            let b ← bracketGraphMLAux ((r3BraidRightGraph g x u w).n - 1)
              (r3BraidRightStepB g x u w)
            return (AML * a) + (AinvML * b)) := hcanon
    _ = (do
          let a ← bracketGraphML (r3BraidRightStepA g x u w)
          let b ← bracketGraphML (r3BraidRightStepB g x u w)
          return (AML * a) + (AinvML * b)) := by simp [hAaux, hBaux]
    _ = (do
          let a ←
            (do
              let aa ← bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
                (r3BraidRightStepAA g x u w)
              let ab ← bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
                (r3BraidRightStepAB g x u w)
              return (AML * aa) + (AinvML * ab))
          let b ←
            (do
              let ba ← bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
                (r3BraidRightStepBA g x u w)
              let bb ← bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
                (r3BraidRightStepBB g x u w)
              return (AML * ba) + (AinvML * bb))
          return (AML * a) + (AinvML * b)) := by simp [hAclosed, hBclosed]

private theorem r2RemoveLast_err_of_r3BraidLeftStepA_ok
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    ∃ e, Reidemeister.r2RemoveLast (r3BraidLeftStepA g x u w) = .error e := by
  cases hr2 : Reidemeister.r2RemoveLast (r3BraidLeftStepA g x u w) with
  | ok g0 =>
      exact False.elim
        ((r2RemoveLast_ne_ok_of_r3BraidLeftStepA
          (g := g) (gL := gL) (g0 := g0) (x := x) (u := u) (w := w) h) hr2)
  | error e =>
      exact ⟨e, rfl⟩

/--
Left-A second-level skein unfolding with the `r2` no-shortcut obligation
discharged from executable R3 success.
-/
private theorem bracketGraphML_leftStepA_skein_of_r3BraidLeft_ok
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hvgA : PDGraph.validate (r3BraidLeftStepA g x u w) = .ok ())
    (hr1pA : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidLeftStepA g x u w) .pos ≠ .ok g0)
    (hr1nA : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidLeftStepA g x u w) .neg ≠ .ok g0) :
    bracketGraphML (r3BraidLeftStepA g x u w) =
      (do
        let a ← bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAA g x u w)
        let b ← bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAB g x u w)
        return (AML * a) + (AinvML * b)) := by
  have hr2A : ∀ g0 : PDGraph,
      Reidemeister.r2RemoveLast (r3BraidLeftStepA g x u w) ≠ .ok g0 := by
    intro g0 hOk
    exact (r2RemoveLast_ne_ok_of_r3BraidLeftStepA
      (g := g) (gL := gL) (g0 := g0) (x := x) (u := u) (w := w) h) hOk
  exact bracketGraphML_leftStepA_skein_of_no_shortcuts
    (g := g) (x := x) (u := u) (w := w) hvgA hr1pA hr1nA hr2A

/--
Left-A second-level skein unfolding with `r2` and `r1/.neg` obligations
discharged from executable R3 success.
-/
private theorem bracketGraphML_leftStepA_skein_of_r3BraidLeft_ok_reduced
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hvgA : PDGraph.validate (r3BraidLeftStepA g x u w) = .ok ())
    (hr1pA : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidLeftStepA g x u w) .pos ≠ .ok g0) :
    bracketGraphML (r3BraidLeftStepA g x u w) =
      (do
        let a ← bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAA g x u w)
        let b ← bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAB g x u w)
        return (AML * a) + (AinvML * b)) := by
  have hr1nA : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidLeftStepA g x u w) .neg ≠ .ok g0 := by
    intro g0 hOk
    exact (r1RemoveLast_neg_ne_ok_of_r3BraidLeftStepA
      (g := g) (gL := gL) (g0 := g0) (x := x) (u := u) (w := w) h) hOk
  exact bracketGraphML_leftStepA_skein_of_r3BraidLeft_ok
    (g := g) (gL := gL) (x := x) (u := u) (w := w) h hvgA hr1pA hr1nA

/--
Left-A second-level skein unfolding with all no-shortcut obligations discharged
from executable R3 success plus validation of `leftStepA`.
-/
private theorem bracketGraphML_leftStepA_skein_of_r3BraidLeft_ok_min
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hvgA : PDGraph.validate (r3BraidLeftStepA g x u w) = .ok ()) :
    bracketGraphML (r3BraidLeftStepA g x u w) =
      (do
        let a ← bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAA g x u w)
        let b ← bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAB g x u w)
        return (AML * a) + (AinvML * b)) := by
  have hr1pA : ∀ g0 : PDGraph,
      Reidemeister.r1RemoveLast (r3BraidLeftStepA g x u w) .pos ≠ .ok g0 := by
    intro g0 hOk
    exact (r1RemoveLast_pos_ne_ok_of_r3BraidLeftStepA
      (g := g) (gL := gL) (g0 := g0) (x := x) (u := u) (w := w) h) hOk
  exact bracketGraphML_leftStepA_skein_of_r3BraidLeft_ok_reduced
    (g := g) (gL := gL) (x := x) (u := u) (w := w) h hvgA hr1pA

private theorem validate_r3BraidLeftStepA_of_r3BraidLeft_ok
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    PDGraph.validate (r3BraidLeftStepA g x u w) = .ok () := by
  have hValidL : PDGraph.Valid (r3BraidLeftGraph g x u w) :=
    r3BraidLeftGraph_valid_of_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hnL : 0 < (r3BraidLeftGraph g x u w).n := by
    simp [r3BraidLeftGraph]
  have hValidL0 :
      PDGraph.Valid
        { freeLoops := 0
          n := (r3BraidLeftGraph g x u w).n
          arcNbr := (r3BraidLeftGraph g x u w).arcNbr } := by
    simpa [PDGraph.Valid] using hValidL
  have hSmoothValid :
      PDGraph.Valid
        { freeLoops := 0
          n := (r3BraidLeftGraph g x u w).n - 1
          arcNbr := smoothLastCoreML_rewire (r3BraidLeftGraph g x u w).n
            (r3BraidLeftGraph g x u w).arcNbr false } :=
    smoothLastCoreML_valid
      (n := (r3BraidLeftGraph g x u w).n)
      (arcNbr := (r3BraidLeftGraph g x u w).arcNbr)
      (isB := false) hnL hValidL0
  have hStepValid : PDGraph.Valid (r3BraidLeftStepA g x u w) := by
    simpa [r3BraidLeftStepA, smoothLastCoreML, PDGraph.Valid] using hSmoothValid
  exact PDGraph.validate_eq_ok_of_valid hStepValid

/--
Left-A second-level skein decomposition with all side obligations discharged from
R3-left executable success.
-/
private theorem bracketGraphML_leftStepA_skein_of_r3BraidLeft_ok_closed
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    bracketGraphML (r3BraidLeftStepA g x u w) =
      (do
        let a ← bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAA g x u w)
        let b ← bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAB g x u w)
        return (AML * a) + (AinvML * b)) := by
  have hvgA : PDGraph.validate (r3BraidLeftStepA g x u w) = .ok () :=
    validate_r3BraidLeftStepA_of_r3BraidLeft_ok
      (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  exact bracketGraphML_leftStepA_skein_of_r3BraidLeft_ok_min
    (g := g) (gL := gL) (x := x) (u := u) (w := w) h hvgA

private theorem r3SkeinStep_left_two_level_expanded_of_r3BraidLeft_ok
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    r3SkeinStep (r3BraidLeftGraph g x u w) =
      (do
        let a ←
          (do
            let aa ← bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
              (r3BraidLeftStepAA g x u w)
            let ab ← bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
              (r3BraidLeftStepAB g x u w)
            return (AML * aa) + (AinvML * ab))
        let b ←
          (do
            let ba ← bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
              (r3BraidLeftStepBA g x u w)
            let bb ← bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
              (r3BraidLeftStepBB g x u w)
            return (AML * ba) + (AinvML * bb))
        return (AML * a) + (AinvML * b)) := by
  have hcanon := r3SkeinStep_left_canonical_expanded g x u w
  have hvgA : PDGraph.validate (r3BraidLeftStepA g x u w) = .ok () :=
    validate_r3BraidLeftStepA_of_r3BraidLeft_ok
      (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hvgB : PDGraph.validate (r3BraidLeftStepB g x u w) = .ok () :=
    validate_r3BraidLeftStepB_of_r3BraidLeft_ok
      (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hAaux :
      bracketGraphMLAux ((r3BraidLeftGraph g x u w).n - 1) (r3BraidLeftStepA g x u w) =
        bracketGraphML (r3BraidLeftStepA g x u w) := by
    have hAuxEq :
        bracketGraphMLAux (r3BraidLeftStepA g x u w).n (r3BraidLeftStepA g x u w) =
          bracketGraphML (r3BraidLeftStepA g x u w) := by
      simp [bracketGraphML, hvgA]
    calc
      bracketGraphMLAux ((r3BraidLeftGraph g x u w).n - 1) (r3BraidLeftStepA g x u w)
          = bracketGraphMLAux (r3BraidLeftStepA g x u w).n (r3BraidLeftStepA g x u w) := by
              simp [r3BraidLeftStepA, r3BraidLeftGraph]
      _ = bracketGraphML (r3BraidLeftStepA g x u w) := hAuxEq
  have hBaux :
      bracketGraphMLAux ((r3BraidLeftGraph g x u w).n - 1) (r3BraidLeftStepB g x u w) =
        bracketGraphML (r3BraidLeftStepB g x u w) := by
    have hAuxEq :
        bracketGraphMLAux (r3BraidLeftStepB g x u w).n (r3BraidLeftStepB g x u w) =
          bracketGraphML (r3BraidLeftStepB g x u w) := by
      simp [bracketGraphML, hvgB]
    calc
      bracketGraphMLAux ((r3BraidLeftGraph g x u w).n - 1) (r3BraidLeftStepB g x u w)
          = bracketGraphMLAux (r3BraidLeftStepB g x u w).n (r3BraidLeftStepB g x u w) := by
              simp [r3BraidLeftStepB, r3BraidLeftGraph]
      _ = bracketGraphML (r3BraidLeftStepB g x u w) := hAuxEq
  have hAclosed := bracketGraphML_leftStepA_skein_of_r3BraidLeft_ok_closed
    (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  have hBclosed := bracketGraphML_leftStepB_skein_of_r3BraidLeft_ok_closed
    (g := g) (gL := gL) (x := x) (u := u) (w := w) h
  calc
    r3SkeinStep (r3BraidLeftGraph g x u w)
        = (do
            let a ← bracketGraphMLAux ((r3BraidLeftGraph g x u w).n - 1)
              (r3BraidLeftStepA g x u w)
            let b ← bracketGraphMLAux ((r3BraidLeftGraph g x u w).n - 1)
              (r3BraidLeftStepB g x u w)
            return (AML * a) + (AinvML * b)) := hcanon
    _ = (do
          let a ← bracketGraphML (r3BraidLeftStepA g x u w)
          let b ← bracketGraphML (r3BraidLeftStepB g x u w)
          return (AML * a) + (AinvML * b)) := by simp [hAaux, hBaux]
    _ = (do
          let a ←
            (do
              let aa ← bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
                (r3BraidLeftStepAA g x u w)
              let ab ← bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
                (r3BraidLeftStepAB g x u w)
              return (AML * aa) + (AinvML * ab))
          let b ←
            (do
              let ba ← bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
                (r3BraidLeftStepBA g x u w)
              let bb ← bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
                (r3BraidLeftStepBB g x u w)
              return (AML * ba) + (AinvML * bb))
          return (AML * a) + (AinvML * b)) := by simp [hAclosed, hBclosed]

private def r3SkeinStepLeftTwoLevelExpr
    (g : PDGraph) (x u w : Nat) : Except String PolyML := do
  let a ←
    (do
      let aa ← bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
        (r3BraidLeftStepAA g x u w)
      let ab ← bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
        (r3BraidLeftStepAB g x u w)
      return (AML * aa) + (AinvML * ab))
  let b ←
    (do
      let ba ← bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
        (r3BraidLeftStepBA g x u w)
      let bb ← bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
        (r3BraidLeftStepBB g x u w)
      return (AML * ba) + (AinvML * bb))
  return (AML * a) + (AinvML * b)

private def r3SkeinStepRightTwoLevelExpr
    (g : PDGraph) (x u w : Nat) : Except String PolyML := do
  let a ←
    (do
      let aa ← bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
        (r3BraidRightStepAA g x u w)
      let ab ← bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
        (r3BraidRightStepAB g x u w)
      return (AML * aa) + (AinvML * ab))
  let b ←
    (do
      let ba ← bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
        (r3BraidRightStepBA g x u w)
      let bb ← bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
        (r3BraidRightStepBB g x u w)
      return (AML * ba) + (AinvML * bb))
  return (AML * a) + (AinvML * b)

/--
Public alias for the left canonical two-level bridge expression.
-/
def r3SkeinStepLeftTwoLevelBridgeExpr
    (g : PDGraph) (x u w : Nat) : Except String PolyML :=
  r3SkeinStepLeftTwoLevelExpr g x u w

/--
Public alias for the right canonical two-level bridge expression.
-/
def r3SkeinStepRightTwoLevelBridgeExpr
    (g : PDGraph) (x u w : Nat) : Except String PolyML :=
  r3SkeinStepRightTwoLevelExpr g x u w

/--
Left TL endpoint target in explicit expanded evaluator form.
-/
private def tlWordLeftExpandedTarget
    (fuel : Nat) (g : PDGraph) (x u w : Nat) : Except String PolyML := do
  let pid ← TL3Context.evalBasis fuel g x u w .id
  let pe1 ← TL3Context.evalBasis fuel g x u w .e1
  let pe2 ← TL3Context.evalBasis fuel g x u w .e2
  let pe1e2 ← TL3Context.evalBasis fuel g x u w .e1e2
  let pe2e1 ← TL3Context.evalBasis fuel g x u w .e2e1
  return (R3.tlWordLeft.coeff .id) * pid
    + (R3.tlWordLeft.coeff .e1) * pe1
    + (R3.tlWordLeft.coeff .e2) * pe2
    + (R3.tlWordLeft.coeff .e1e2) * pe1e2
    + (R3.tlWordLeft.coeff .e2e1) * pe2e1

/--
Right TL endpoint target in explicit expanded evaluator form.
-/
private def tlWordRightExpandedTarget
    (fuel : Nat) (g : PDGraph) (x u w : Nat) : Except String PolyML := do
  let pid ← TL3Context.evalBasis fuel g x u w .id
  let pe1 ← TL3Context.evalBasis fuel g x u w .e1
  let pe2 ← TL3Context.evalBasis fuel g x u w .e2
  let pe1e2 ← TL3Context.evalBasis fuel g x u w .e1e2
  let pe2e1 ← TL3Context.evalBasis fuel g x u w .e2e1
  return (R3.tlWordRight.coeff .id) * pid
    + (R3.tlWordRight.coeff .e1) * pe1
    + (R3.tlWordRight.coeff .e2) * pe2
    + (R3.tlWordRight.coeff .e1e2) * pe1e2
    + (R3.tlWordRight.coeff .e2e1) * pe2e1

/--
Expanded C.2 bridge witness in explicit basis-expanded target form.
-/
def R3TwoLevelExpandedBridgeWitness
    (fuel : Nat) (g : PDGraph) (x u w : Nat) : Prop :=
  (r3SkeinStepLeftTwoLevelExpr g x u w =
      tlWordLeftExpandedTarget fuel g x u w) ∧
    (r3SkeinStepRightTwoLevelExpr g x u w =
      tlWordRightExpandedTarget fuel g x u w)

private theorem left_two_level_bridge_of_expanded_target
    {g : PDGraph} {x u w fuel : Nat}
    (h :
      r3SkeinStepLeftTwoLevelExpr g x u w =
        tlWordLeftExpandedTarget fuel g x u w) :
    r3SkeinStepLeftTwoLevelExpr g x u w =
      TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft := by
  calc
    r3SkeinStepLeftTwoLevelExpr g x u w
        = tlWordLeftExpandedTarget fuel g x u w := h
    _ = TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft := by
          simp [tlWordLeftExpandedTarget, TL3Context.evalTL3Expr]

private theorem right_two_level_bridge_of_expanded_target
    {g : PDGraph} {x u w fuel : Nat}
    (h :
      r3SkeinStepRightTwoLevelExpr g x u w =
        tlWordRightExpandedTarget fuel g x u w) :
    r3SkeinStepRightTwoLevelExpr g x u w =
      TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight := by
  calc
    r3SkeinStepRightTwoLevelExpr g x u w
        = tlWordRightExpandedTarget fuel g x u w := h
    _ = TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight := by
          simp [tlWordRightExpandedTarget, TL3Context.evalTL3Expr]

private theorem two_level_bridges_of_expanded_witness
    {g : PDGraph} {x u w fuel : Nat}
    (hExp : R3TwoLevelExpandedBridgeWitness fuel g x u w) :
    (r3SkeinStepLeftTwoLevelExpr g x u w =
      TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft) ∧
      (r3SkeinStepRightTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) := by
  rcases hExp with ⟨hLeftExp, hRightExp⟩
  exact ⟨left_two_level_bridge_of_expanded_target
      (g := g) (x := x) (u := u) (w := w) (fuel := fuel) hLeftExp,
    right_two_level_bridge_of_expanded_target
      (g := g) (x := x) (u := u) (w := w) (fuel := fuel) hRightExp⟩

private theorem expanded_witness_of_two_level_bridges
    {g : PDGraph} {x u w fuel : Nat}
    (h :
      (r3SkeinStepLeftTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft) ∧
        (r3SkeinStepRightTwoLevelExpr g x u w =
          TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight)) :
    R3TwoLevelExpandedBridgeWitness fuel g x u w := by
  rcases h with ⟨hLeftBridge, hRightBridge⟩
  refine ⟨?_, ?_⟩
  · calc
      r3SkeinStepLeftTwoLevelExpr g x u w
          = TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft := hLeftBridge
      _ = tlWordLeftExpandedTarget fuel g x u w := by
            simp [tlWordLeftExpandedTarget, TL3Context.evalTL3Expr]
  · calc
      r3SkeinStepRightTwoLevelExpr g x u w
          = TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight := hRightBridge
      _ = tlWordRightExpandedTarget fuel g x u w := by
            simp [tlWordRightExpandedTarget, TL3Context.evalTL3Expr]

private theorem expanded_witness_iff_two_level_bridges
    {g : PDGraph} {x u w fuel : Nat} :
    R3TwoLevelExpandedBridgeWitness fuel g x u w ↔
      ((r3SkeinStepLeftTwoLevelExpr g x u w =
          TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft) ∧
        (r3SkeinStepRightTwoLevelExpr g x u w =
          TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight)) := by
  constructor
  · intro hExp
    exact two_level_bridges_of_expanded_witness
      (g := g) (x := x) (u := u) (w := w) (fuel := fuel) hExp
  · intro h
    exact expanded_witness_of_two_level_bridges
      (g := g) (x := x) (u := u) (w := w) (fuel := fuel) h

private theorem r3SkeinStep_left_two_level_expr_of_r3BraidLeft_ok
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    r3SkeinStep (r3BraidLeftGraph g x u w) = r3SkeinStepLeftTwoLevelExpr g x u w := by
  simpa [r3SkeinStepLeftTwoLevelExpr] using
    (r3SkeinStep_left_two_level_expanded_of_r3BraidLeft_ok
      (g := g) (gL := gL) (x := x) (u := u) (w := w) h)

private theorem r3SkeinStep_right_two_level_expr_of_r3BraidRight_ok
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    r3SkeinStep (r3BraidRightGraph g x u w) = r3SkeinStepRightTwoLevelExpr g x u w := by
  simpa [r3SkeinStepRightTwoLevelExpr] using
    (r3SkeinStep_right_two_level_expanded_of_r3BraidRight_ok
      (g := g) (gR := gR) (x := x) (u := u) (w := w) h)

private theorem r3SkeinStep_left_eq_tl3_of_two_level_bridge
    {g gL : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hBridge :
      r3SkeinStepLeftTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft) :
    r3SkeinStep (r3BraidLeftGraph g x u w) =
      TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft := by
  calc
    r3SkeinStep (r3BraidLeftGraph g x u w) = r3SkeinStepLeftTwoLevelExpr g x u w :=
      r3SkeinStep_left_two_level_expr_of_r3BraidLeft_ok
        (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft
    _ = TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft := hBridge

private theorem r3SkeinStep_right_eq_tl3_of_two_level_bridge
    {g gR : PDGraph} {x u w fuel : Nat}
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hBridge :
      r3SkeinStepRightTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    r3SkeinStep (r3BraidRightGraph g x u w) =
      TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight := by
  calc
    r3SkeinStep (r3BraidRightGraph g x u w) = r3SkeinStepRightTwoLevelExpr g x u w :=
      r3SkeinStep_right_two_level_expr_of_r3BraidRight_ok
        (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight
    _ = TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight := hBridge

private theorem r3SkeinStep_canonical_eq_of_two_level_tl3_bridges
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hLeftBridge :
      r3SkeinStepLeftTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft)
    (hRightBridge :
      r3SkeinStepRightTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    r3SkeinStep (r3BraidLeftGraph g x u w) =
      r3SkeinStep (r3BraidRightGraph g x u w) := by
  calc
    r3SkeinStep (r3BraidLeftGraph g x u w)
        = r3SkeinStepLeftTwoLevelExpr g x u w :=
          r3SkeinStep_left_two_level_expr_of_r3BraidLeft_ok
            (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft
    _ = TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft := hLeftBridge
    _ = TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight :=
      R3.evalTL3Expr_braid_relation fuel g x u w
    _ = r3SkeinStepRightTwoLevelExpr g x u w := hRightBridge.symm
    _ = r3SkeinStep (r3BraidRightGraph g x u w) := by
          simpa using
            (r3SkeinStep_right_two_level_expr_of_r3BraidRight_ok
              (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight).symm

/--
Direct two-level closure primitive:
if the four second-level leaf evaluations agree pairwise between left and
right braid gadgets, then the canonical two-level skein expressions agree.
-/
private theorem two_level_expr_eq_of_leaf_equalities
    {g : PDGraph} {x u w : Nat}
    (hAA :
      bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAA g x u w) =
        bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
          (r3BraidRightStepAA g x u w))
    (hAB :
      bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAB g x u w) =
        bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
          (r3BraidRightStepAB g x u w))
    (hBA :
      bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
          (r3BraidLeftStepBA g x u w) =
        bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
          (r3BraidRightStepBA g x u w))
    (hBB :
      bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
          (r3BraidLeftStepBB g x u w) =
        bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
          (r3BraidRightStepBB g x u w)) :
    r3SkeinStepLeftTwoLevelExpr g x u w =
      r3SkeinStepRightTwoLevelExpr g x u w := by
  simp [r3SkeinStepLeftTwoLevelExpr, r3SkeinStepRightTwoLevelExpr,
    hAA, hAB, hBA, hBB]

/--
Canonical R3 one-step skein equality from four explicit second-level leaf
equalities (AA/AB/BA/BB), without TL endpoint assumptions.
-/
private theorem r3SkeinStep_canonical_eq_of_two_level_leaf_equalities
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hAA :
      bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAA g x u w) =
        bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
          (r3BraidRightStepAA g x u w))
    (hAB :
      bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAB g x u w) =
        bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
          (r3BraidRightStepAB g x u w))
    (hBA :
      bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
          (r3BraidLeftStepBA g x u w) =
        bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
          (r3BraidRightStepBA g x u w))
    (hBB :
      bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
          (r3BraidLeftStepBB g x u w) =
        bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
          (r3BraidRightStepBB g x u w)) :
    r3SkeinStep (r3BraidLeftGraph g x u w) =
      r3SkeinStep (r3BraidRightGraph g x u w) := by
  calc
    r3SkeinStep (r3BraidLeftGraph g x u w)
        = r3SkeinStepLeftTwoLevelExpr g x u w :=
          r3SkeinStep_left_two_level_expr_of_r3BraidLeft_ok
            (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft
    _ = r3SkeinStepRightTwoLevelExpr g x u w :=
        two_level_expr_eq_of_leaf_equalities
          (g := g) (x := x) (u := u) (w := w)
          hAA hAB hBA hBB
    _ = r3SkeinStep (r3BraidRightGraph g x u w) := by
          simpa using
            (r3SkeinStep_right_two_level_expr_of_r3BraidRight_ok
              (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight).symm

private theorem no_left_branch_r2_collapse_of_r3BraidLeft_ok
    {g gL : PDGraph} {x u w : Nat} :
    Reidemeister.r3BraidLeft g x u w = .ok gL →
      ¬∃ gA0 gB0 : PDGraph,
        Reidemeister.r2RemoveLast (r3BraidLeftStepA g x u w) = .ok gA0 ∧
        Reidemeister.r2RemoveLast (r3BraidLeftStepB g x u w) = .ok gB0 := by
  intro hLeft hCollapse
  rcases hCollapse with ⟨_gA0, gB0, _hLA, hLB⟩
  exact (r2RemoveLast_ne_ok_of_r3BraidLeftStepB (g := g) (gL := gL) (g0 := gB0)
    (x := x) (u := u) (w := w) hLeft) hLB

private theorem canonical_branch_r2_collapse_unreachable_of_r3BraidLeft_ok
    {g gL : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    ¬∃ gA0 gB0 : PDGraph,
      Reidemeister.r2RemoveLast (r3BraidLeftStepA g x u w) = .ok gA0 ∧
      Reidemeister.r2RemoveLast (r3BraidLeftStepB g x u w) = .ok gB0 ∧
      Reidemeister.r2RemoveLast (r3BraidRightStepA g x u w) = .ok gA0 ∧
      Reidemeister.r2RemoveLast (r3BraidRightStepB g x u w) = .ok gB0 := by
  intro hAll
  rcases hAll with ⟨gA0, gB0, hLA, hLB, _hRA, _hRB⟩
  exact (no_left_branch_r2_collapse_of_r3BraidLeft_ok (g := g) (gL := gL)
    (x := x) (u := u) (w := w) hLeft) ⟨gA0, gB0, hLA, hLB⟩

/--
Public blocker theorem: the canonical four-branch `r2RemoveLast` collapse
premise used in the alternative R3 closure route is unreachable whenever the
left executable R3 constructor succeeds.
-/
theorem r3_canonical_branch_r2_collapse_unreachable
    {g gL : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    ¬∃ gA0 gB0 : PDGraph,
      Reidemeister.r2RemoveLast (r3BraidLeftStepA g x u w) = .ok gA0 ∧
      Reidemeister.r2RemoveLast (r3BraidLeftStepB g x u w) = .ok gB0 ∧
      Reidemeister.r2RemoveLast (r3BraidRightStepA g x u w) = .ok gA0 ∧
      Reidemeister.r2RemoveLast (r3BraidRightStepB g x u w) = .ok gB0 :=
  canonical_branch_r2_collapse_unreachable_of_r3BraidLeft_ok
    (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft

/--
Canonical R3 one-step equality from branch-level R2 collapses.

This isolates the remaining unconditional R3 gap to proving four concrete
`r2RemoveLast` obligations on the first-step branch graphs.
-/
private theorem r3SkeinStep_canonical_eq_of_branch_r2_collapse
    {g : PDGraph} {x u w : Nat} {gA0 gB0 : PDGraph}
    (hLA : Reidemeister.r2RemoveLast (r3BraidLeftStepA g x u w) = .ok gA0)
    (hLB : Reidemeister.r2RemoveLast (r3BraidLeftStepB g x u w) = .ok gB0)
    (hRA : Reidemeister.r2RemoveLast (r3BraidRightStepA g x u w) = .ok gA0)
    (hRB : Reidemeister.r2RemoveLast (r3BraidRightStepB g x u w) = .ok gB0) :
    r3SkeinStep (r3BraidLeftGraph g x u w) =
      r3SkeinStep (r3BraidRightGraph g x u w) := by
  have hvgLA : PDGraph.validate (r3BraidLeftStepA g x u w) = .ok () :=
    validate_eq_ok_of_r2RemoveLast_ok hLA
  have hvgLB : PDGraph.validate (r3BraidLeftStepB g x u w) = .ok () :=
    validate_eq_ok_of_r2RemoveLast_ok hLB
  have hvgRA : PDGraph.validate (r3BraidRightStepA g x u w) = .ok () :=
    validate_eq_ok_of_r2RemoveLast_ok hRA
  have hvgRB : PDGraph.validate (r3BraidRightStepB g x u w) = .ok () :=
    validate_eq_ok_of_r2RemoveLast_ok hRB

  have hLA_aux :
      bracketGraphMLAux ((r3BraidLeftGraph g x u w).n - 1) (r3BraidLeftStepA g x u w) =
        bracketGraphML gA0 := by
    have hAuxEq :
        bracketGraphMLAux (r3BraidLeftStepA g x u w).n (r3BraidLeftStepA g x u w) =
          bracketGraphML (r3BraidLeftStepA g x u w) := by
      simp [bracketGraphML, hvgLA]
    calc
      bracketGraphMLAux ((r3BraidLeftGraph g x u w).n - 1) (r3BraidLeftStepA g x u w)
          = bracketGraphMLAux (r3BraidLeftStepA g x u w).n (r3BraidLeftStepA g x u w) := by
              simp [r3BraidLeftStepA, r3BraidLeftGraph]
      _ = bracketGraphML (r3BraidLeftStepA g x u w) := hAuxEq
      _ = bracketGraphML gA0 := Kauffman.bracketGraphML_r2RemoveLast_ok hLA

  have hLB_aux :
      bracketGraphMLAux ((r3BraidLeftGraph g x u w).n - 1) (r3BraidLeftStepB g x u w) =
        bracketGraphML gB0 := by
    have hAuxEq :
        bracketGraphMLAux (r3BraidLeftStepB g x u w).n (r3BraidLeftStepB g x u w) =
          bracketGraphML (r3BraidLeftStepB g x u w) := by
      simp [bracketGraphML, hvgLB]
    calc
      bracketGraphMLAux ((r3BraidLeftGraph g x u w).n - 1) (r3BraidLeftStepB g x u w)
          = bracketGraphMLAux (r3BraidLeftStepB g x u w).n (r3BraidLeftStepB g x u w) := by
              simp [r3BraidLeftStepB, r3BraidLeftGraph]
      _ = bracketGraphML (r3BraidLeftStepB g x u w) := hAuxEq
      _ = bracketGraphML gB0 := Kauffman.bracketGraphML_r2RemoveLast_ok hLB

  have hRA_aux :
      bracketGraphMLAux ((r3BraidRightGraph g x u w).n - 1) (r3BraidRightStepA g x u w) =
        bracketGraphML gA0 := by
    have hAuxEq :
        bracketGraphMLAux (r3BraidRightStepA g x u w).n (r3BraidRightStepA g x u w) =
          bracketGraphML (r3BraidRightStepA g x u w) := by
      simp [bracketGraphML, hvgRA]
    calc
      bracketGraphMLAux ((r3BraidRightGraph g x u w).n - 1) (r3BraidRightStepA g x u w)
          = bracketGraphMLAux (r3BraidRightStepA g x u w).n (r3BraidRightStepA g x u w) := by
              simp [r3BraidRightStepA, r3BraidRightGraph]
      _ = bracketGraphML (r3BraidRightStepA g x u w) := hAuxEq
      _ = bracketGraphML gA0 := Kauffman.bracketGraphML_r2RemoveLast_ok hRA

  have hRB_aux :
      bracketGraphMLAux ((r3BraidRightGraph g x u w).n - 1) (r3BraidRightStepB g x u w) =
        bracketGraphML gB0 := by
    have hAuxEq :
        bracketGraphMLAux (r3BraidRightStepB g x u w).n (r3BraidRightStepB g x u w) =
          bracketGraphML (r3BraidRightStepB g x u w) := by
      simp [bracketGraphML, hvgRB]
    calc
      bracketGraphMLAux ((r3BraidRightGraph g x u w).n - 1) (r3BraidRightStepB g x u w)
          = bracketGraphMLAux (r3BraidRightStepB g x u w).n (r3BraidRightStepB g x u w) := by
              simp [r3BraidRightStepB, r3BraidRightGraph]
      _ = bracketGraphML (r3BraidRightStepB g x u w) := hAuxEq
      _ = bracketGraphML gB0 := Kauffman.bracketGraphML_r2RemoveLast_ok hRB

  change
    (do
      let a ← bracketGraphMLAux ((r3BraidLeftGraph g x u w).n - 1) (r3BraidLeftStepA g x u w)
      let b ← bracketGraphMLAux ((r3BraidLeftGraph g x u w).n - 1) (r3BraidLeftStepB g x u w)
      return (AML * a) + (AinvML * b)) =
    (do
      let a ← bracketGraphMLAux ((r3BraidRightGraph g x u w).n - 1) (r3BraidRightStepA g x u w)
      let b ← bracketGraphMLAux ((r3BraidRightGraph g x u w).n - 1) (r3BraidRightStepB g x u w)
      return (AML * a) + (AinvML * b))
  simp [r3SkeinStep, hLA_aux, hLB_aux, hRA_aux, hRB_aux]

/--
Reduction lemma: any endpoint-level `r3SkeinStep` equality obligation for the
executable R3 braid constructors is equivalent to a single canonical equality
on the fixed braid-output graphs.

This isolates the remaining R3 gap to the canonical target
`r3SkeinStep (r3BraidLeftGraph ...) = r3SkeinStep (r3BraidRightGraph ...)`.
-/
private theorem r3SkeinStep_eq_iff_canonical_r3_outputs
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR) :
    r3SkeinStep gL = r3SkeinStep gR ↔
      r3SkeinStep (r3BraidLeftGraph g x u w) =
        r3SkeinStep (r3BraidRightGraph g x u w) := by
  have hgL : gL = r3BraidLeftGraph g x u w :=
    r3BraidLeft_eq_gOut (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft
  have hgR : gR = r3BraidRightGraph g x u w :=
    r3BraidRight_eq_gOut (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight
  constructor
  · intro h
    simpa [hgL, hgR] using h
  · intro h
    simpa [hgL, hgR] using h

/--
Endpoint-level reduction principle for R3 one-step skein equality.

Use this when the canonical braid-output equality has been established
independently (e.g. via TL3 context + braid relation).
-/
private theorem r3SkeinStep_eq_of_canonical_r3_outputs
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hCanonical :
      r3SkeinStep (r3BraidLeftGraph g x u w) =
        r3SkeinStep (r3BraidRightGraph g x u w)) :
    r3SkeinStep gL = r3SkeinStep gR := by
  exact (r3SkeinStep_eq_iff_canonical_r3_outputs
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
    hLeft hRight).2 hCanonical

/--
Canonical R3 skein equality from TL3 bridge correspondences.

If each canonical braid-output one-step skein value is identified with the corresponding TL3
context evaluation (`σ₁σ₂σ₁` on the left and `σ₂σ₁σ₂` on the right), equality follows from the
TL3 braid relation.
-/
private theorem r3SkeinStep_canonical_eq_of_tl3_bridge
    {g : PDGraph} {x u w fuel : Nat}
    (hLeftTL :
      r3SkeinStep (r3BraidLeftGraph g x u w) =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft)
    (hRightTL :
      r3SkeinStep (r3BraidRightGraph g x u w) =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    r3SkeinStep (r3BraidLeftGraph g x u w) =
      r3SkeinStep (r3BraidRightGraph g x u w) := by
  calc
    r3SkeinStep (r3BraidLeftGraph g x u w)
        = TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft := hLeftTL
    _ = TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight :=
      R3.evalTL3Expr_braid_relation (fuel := fuel) (g := g) (x := x) (u := u) (w := w)
    _ = r3SkeinStep (r3BraidRightGraph g x u w) := hRightTL.symm

/--
Public bridge form of theorem-level R3 invariance.

This discharges endpoint equality without a direct `hStepEq` hypothesis, assuming the two
canonical TL3 bridge correspondences needed to connect one-step skein values to TL3 context
evaluation.
-/
theorem bracketGraphML_r3_invariant_of_tl3_bridge
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hLeftTL :
      r3SkeinStep (r3BraidLeftGraph g x u w) =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft)
    (hRightTL :
      r3SkeinStep (r3BraidRightGraph g x u w) =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    bracketGraphML gL = bracketGraphML gR := by
  have hCanonical :
      r3SkeinStep (r3BraidLeftGraph g x u w) =
        r3SkeinStep (r3BraidRightGraph g x u w) :=
    r3SkeinStep_canonical_eq_of_tl3_bridge
      (g := g) (x := x) (u := u) (w := w) (fuel := fuel) hLeftTL hRightTL
  have hStepEq : r3SkeinStep gL = r3SkeinStep gR :=
    r3SkeinStep_eq_of_canonical_r3_outputs
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
      hLeft hRight hCanonical
  calc
    bracketGraphML gL = r3SkeinStep gL := by
      simpa [r3SkeinStep] using
        R3.bracketGraphML_skein_of_r3BraidLeft_ok
          (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft
    _ = r3SkeinStep gR := hStepEq
    _ = bracketGraphML gR := by
      simpa [r3SkeinStep] using
        (R3.bracketGraphML_skein_of_r3BraidRight_ok
          (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight).symm

/--
Endpoint-level skein-step equality from TL3 bridge hypotheses.

This theorem exposes the equality core needed for downstream invariance
bridges without requiring callers to mention canonical internal braid-gadget
names.
-/
theorem r3SkeinStep_eq_of_tl3_bridge_endpoints
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hLeftTL :
      r3SkeinStep gL =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft)
    (hRightTL :
      r3SkeinStep gR =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    r3SkeinStep gL = r3SkeinStep gR := by
  have hgL : gL = r3BraidLeftGraph g x u w :=
    r3BraidLeft_eq_gOut (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft
  have hgR : gR = r3BraidRightGraph g x u w :=
    r3BraidRight_eq_gOut (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight
  have hLeftCanonical :
      r3SkeinStep (r3BraidLeftGraph g x u w) =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft := by
    simpa [hgL] using hLeftTL
  have hRightCanonical :
      r3SkeinStep (r3BraidRightGraph g x u w) =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight := by
    simpa [hgR] using hRightTL
  have hCanonical :
      r3SkeinStep (r3BraidLeftGraph g x u w) =
        r3SkeinStep (r3BraidRightGraph g x u w) :=
    r3SkeinStep_canonical_eq_of_tl3_bridge
      (g := g) (x := x) (u := u) (w := w) (fuel := fuel)
      hLeftCanonical hRightCanonical
  exact r3SkeinStep_eq_of_canonical_r3_outputs
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
    hLeft hRight hCanonical

/--
Endpoint-level skein-step equality from two-level TL bridge obligations.

This is the narrowed C.2 interface: once left/right two-level branch
expressions are identified with TL endpoint evaluations, endpoint skein-step
equality follows immediately.
-/
theorem r3SkeinStep_eq_of_two_level_tl3_bridges_endpoints
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hLeftBridge :
      r3SkeinStepLeftTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft)
    (hRightBridge :
      r3SkeinStepRightTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    r3SkeinStep gL = r3SkeinStep gR := by
  have hCanonical :
      r3SkeinStep (r3BraidLeftGraph g x u w) =
        r3SkeinStep (r3BraidRightGraph g x u w) :=
    r3SkeinStep_canonical_eq_of_two_level_tl3_bridges
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
      hLeft hRight hLeftBridge hRightBridge
  exact r3SkeinStep_eq_of_canonical_r3_outputs
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
    hLeft hRight hCanonical

/--
Public alias form of endpoint skein-step equality from two-level TL bridge
obligations.
-/
theorem r3SkeinStep_eq_of_two_level_tl3_bridge_expr_endpoints
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hLeftBridge :
      r3SkeinStepLeftTwoLevelBridgeExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft)
    (hRightBridge :
      r3SkeinStepRightTwoLevelBridgeExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    r3SkeinStep gL = r3SkeinStep gR := by
  simpa [r3SkeinStepLeftTwoLevelBridgeExpr, r3SkeinStepRightTwoLevelBridgeExpr] using
    (r3SkeinStep_eq_of_two_level_tl3_bridges_endpoints
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
      hLeft hRight hLeftBridge hRightBridge)

/--
Endpoint-level skein-step equality from direct equality of the canonical
two-level bridge expressions.

This gives a single-obligation closure route: prove
`r3SkeinStepLeftTwoLevelBridgeExpr = r3SkeinStepRightTwoLevelBridgeExpr`.
-/
theorem r3SkeinStep_eq_of_two_level_bridge_expr_eq_endpoints
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hTwoEq :
      r3SkeinStepLeftTwoLevelBridgeExpr g x u w =
        r3SkeinStepRightTwoLevelBridgeExpr g x u w) :
    r3SkeinStep gL = r3SkeinStep gR := by
  have hCanonical :
      r3SkeinStep (r3BraidLeftGraph g x u w) =
        r3SkeinStep (r3BraidRightGraph g x u w) := by
    calc
      r3SkeinStep (r3BraidLeftGraph g x u w)
          = r3SkeinStepLeftTwoLevelExpr g x u w :=
            r3SkeinStep_left_two_level_expr_of_r3BraidLeft_ok
              (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft
      _ = r3SkeinStepRightTwoLevelExpr g x u w := by
            simpa [r3SkeinStepLeftTwoLevelBridgeExpr, r3SkeinStepRightTwoLevelBridgeExpr] using hTwoEq
      _ = r3SkeinStep (r3BraidRightGraph g x u w) := by
            simpa using
              (r3SkeinStep_right_two_level_expr_of_r3BraidRight_ok
                (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight).symm
  exact r3SkeinStep_eq_of_canonical_r3_outputs
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
    hLeft hRight hCanonical

/--
Endpoint-level skein-step equality from an expanded two-level bridge witness.

This keeps the bridge obligations in explicit basis-expanded form and
eliminates to the canonical two-level bridge pair internally.
-/
theorem r3SkeinStep_eq_of_two_level_expanded_bridges_endpoints
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hExpanded : R3TwoLevelExpandedBridgeWitness fuel g x u w) :
    r3SkeinStep gL = r3SkeinStep gR := by
  have hPair :
      (r3SkeinStepLeftTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft) ∧
      (r3SkeinStepRightTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :=
    (expanded_witness_iff_two_level_bridges
      (g := g) (x := x) (u := u) (w := w) (fuel := fuel)).1 hExpanded
  exact r3SkeinStep_eq_of_two_level_tl3_bridges_endpoints
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
    hLeft hRight hPair.1 hPair.2

/--
Endpoint-level bracket invariance from an expanded two-level bridge witness.
-/
theorem bracketGraphML_r3_invariant_of_two_level_expanded_bridges_endpoints
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hExpanded : R3TwoLevelExpandedBridgeWitness fuel g x u w) :
    bracketGraphML gL = bracketGraphML gR := by
  have hStepEq : r3SkeinStep gL = r3SkeinStep gR :=
    r3SkeinStep_eq_of_two_level_expanded_bridges_endpoints
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
      hLeft hRight hExpanded
  calc
    bracketGraphML gL = r3SkeinStep gL := by
      simpa [r3SkeinStep] using
        R3.bracketGraphML_skein_of_r3BraidLeft_ok
          (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft
    _ = r3SkeinStep gR := hStepEq
    _ = bracketGraphML gR := by
      simpa [r3SkeinStep] using
        (R3.bracketGraphML_skein_of_r3BraidRight_ok
          (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight).symm

/--
Endpoint `r3SkeinStep` equality from explicit second-level leaf equalities.

This is a direct C.2 closure route independent of TL endpoint assumptions:
it factors through canonical outputs using
`r3SkeinStep_canonical_eq_of_two_level_leaf_equalities`.
-/
theorem r3SkeinStep_eq_of_two_level_leaf_equalities_endpoints
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hAA :
      bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAA g x u w) =
        bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
          (r3BraidRightStepAA g x u w))
    (hAB :
      bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAB g x u w) =
        bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
          (r3BraidRightStepAB g x u w))
    (hBA :
      bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
          (r3BraidLeftStepBA g x u w) =
        bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
          (r3BraidRightStepBA g x u w))
    (hBB :
      bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
          (r3BraidLeftStepBB g x u w) =
        bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
          (r3BraidRightStepBB g x u w)) :
    r3SkeinStep gL = r3SkeinStep gR := by
  have hCanonical :
      r3SkeinStep (r3BraidLeftGraph g x u w) =
        r3SkeinStep (r3BraidRightGraph g x u w) :=
    r3SkeinStep_canonical_eq_of_two_level_leaf_equalities
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
      hLeft hRight hAA hAB hBA hBB
  exact r3SkeinStep_eq_of_canonical_r3_outputs
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
    hLeft hRight hCanonical

/--
`AA` leaf equality in aux-fuel form is equivalent to bracket-form equality.
-/
private theorem leaf_eval_AA_eq_iff_bracket_eq
    {g : PDGraph} {x u w : Nat} :
    (bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
        (r3BraidLeftStepAA g x u w) =
      bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
        (r3BraidRightStepAA g x u w)) ↔
      (bracketGraphML (r3BraidLeftStepAA g x u w) =
        bracketGraphML (r3BraidRightStepAA g x u w)) := by
  have hFuelL :
      (r3BraidLeftStepA g x u w).n - 1 =
        (r3BraidLeftStepAA g x u w).n := by
    simp [r3BraidLeftStepA, r3BraidLeftStepAA, r3BraidLeftGraph]
  have hFuelR :
      (r3BraidRightStepA g x u w).n - 1 =
        (r3BraidRightStepAA g x u w).n := by
    simp [r3BraidRightStepA, r3BraidRightStepAA, r3BraidRightGraph]
  constructor <;> intro h <;>
    simpa [bracketGraphML, hFuelL, hFuelR] using h

/-- `AB` leaf: aux-fuel equality is equivalent to bracket-form equality. -/
private theorem leaf_eval_AB_eq_iff_bracket_eq
    {g : PDGraph} {x u w : Nat} :
    (bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
        (r3BraidLeftStepAB g x u w) =
      bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
        (r3BraidRightStepAB g x u w)) ↔
      (bracketGraphML (r3BraidLeftStepAB g x u w) =
        bracketGraphML (r3BraidRightStepAB g x u w)) := by
  have hFuelL :
      (r3BraidLeftStepA g x u w).n - 1 =
        (r3BraidLeftStepAB g x u w).n := by
    simp [r3BraidLeftStepA, r3BraidLeftStepAB, r3BraidLeftGraph]
  have hFuelR :
      (r3BraidRightStepA g x u w).n - 1 =
        (r3BraidRightStepAB g x u w).n := by
    simp [r3BraidRightStepA, r3BraidRightStepAB, r3BraidRightGraph]
  constructor <;> intro h <;>
    simpa [bracketGraphML, hFuelL, hFuelR] using h

/-- `BA` leaf: aux-fuel equality is equivalent to bracket-form equality. -/
private theorem leaf_eval_BA_eq_iff_bracket_eq
    {g : PDGraph} {x u w : Nat} :
    (bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
        (r3BraidLeftStepBA g x u w) =
      bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
        (r3BraidRightStepBA g x u w)) ↔
      (bracketGraphML (r3BraidLeftStepBA g x u w) =
        bracketGraphML (r3BraidRightStepBA g x u w)) := by
  have hFuelL :
      (r3BraidLeftStepB g x u w).n - 1 =
        (r3BraidLeftStepBA g x u w).n := by
    simp [r3BraidLeftStepB, r3BraidLeftStepBA, r3BraidLeftGraph]
  have hFuelR :
      (r3BraidRightStepB g x u w).n - 1 =
        (r3BraidRightStepBA g x u w).n := by
    simp [r3BraidRightStepB, r3BraidRightStepBA, r3BraidRightGraph]
  constructor <;> intro h <;>
    simpa [bracketGraphML, hFuelL, hFuelR] using h

/-- `BB` leaf: aux-fuel equality is equivalent to bracket-form equality. -/
private theorem leaf_eval_BB_eq_iff_bracket_eq
    {g : PDGraph} {x u w : Nat} :
    (bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
        (r3BraidLeftStepBB g x u w) =
      bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
        (r3BraidRightStepBB g x u w)) ↔
      (bracketGraphML (r3BraidLeftStepBB g x u w) =
        bracketGraphML (r3BraidRightStepBB g x u w)) := by
  have hFuelL :
      (r3BraidLeftStepB g x u w).n - 1 =
        (r3BraidLeftStepBB g x u w).n := by
    simp [r3BraidLeftStepB, r3BraidLeftStepBB, r3BraidLeftGraph]
  have hFuelR :
      (r3BraidRightStepB g x u w).n - 1 =
        (r3BraidRightStepBB g x u w).n := by
    simp [r3BraidRightStepB, r3BraidRightStepBB, r3BraidRightGraph]
  constructor <;> intro h <;>
    simpa [bracketGraphML, hFuelL, hFuelR] using h

/--
Endpoint `r3SkeinStep` equality from bracket-form second-level leaf equalities.

This is the normalized S0.2 target shape used by the remaining closure work.
-/
theorem r3SkeinStep_eq_of_two_level_bracket_leaf_equalities_endpoints
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hAA :
      bracketGraphML (r3BraidLeftStepAA g x u w) =
        bracketGraphML (r3BraidRightStepAA g x u w))
    (hAB :
      bracketGraphML (r3BraidLeftStepAB g x u w) =
        bracketGraphML (r3BraidRightStepAB g x u w))
    (hBA :
      bracketGraphML (r3BraidLeftStepBA g x u w) =
        bracketGraphML (r3BraidRightStepBA g x u w))
    (hBB :
      bracketGraphML (r3BraidLeftStepBB g x u w) =
        bracketGraphML (r3BraidRightStepBB g x u w)) :
    r3SkeinStep gL = r3SkeinStep gR := by
  have hAA' :
      bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAA g x u w) =
        bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
          (r3BraidRightStepAA g x u w) :=
    (leaf_eval_AA_eq_iff_bracket_eq (g := g) (x := x) (u := u) (w := w)).2 hAA
  have hAB' :
      bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
          (r3BraidLeftStepAB g x u w) =
        bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
          (r3BraidRightStepAB g x u w) :=
    (leaf_eval_AB_eq_iff_bracket_eq (g := g) (x := x) (u := u) (w := w)).2 hAB
  have hBA' :
      bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
          (r3BraidLeftStepBA g x u w) =
        bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
          (r3BraidRightStepBA g x u w) :=
    (leaf_eval_BA_eq_iff_bracket_eq (g := g) (x := x) (u := u) (w := w)).2 hBA
  have hBB' :
      bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
          (r3BraidLeftStepBB g x u w) =
        bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
          (r3BraidRightStepBB g x u w) :=
    (leaf_eval_BB_eq_iff_bracket_eq (g := g) (x := x) (u := u) (w := w)).2 hBB
  exact r3SkeinStep_eq_of_two_level_leaf_equalities_endpoints
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
    hLeft hRight hAA' hAB' hBA' hBB'

/--
Convert equality of the `AA` leaf graphs into equality of the corresponding
leaf evaluations used in `r3SkeinStepLeft/RightTwoLevelExpr`.
-/
private theorem leaf_eval_AA_eq_of_graph_eq
    {g : PDGraph} {x u w : Nat}
    (hAAgraph : r3BraidLeftStepAA g x u w = r3BraidRightStepAA g x u w) :
    bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
        (r3BraidLeftStepAA g x u w) =
      bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
        (r3BraidRightStepAA g x u w) := by
  have hFuel :
      (r3BraidLeftStepA g x u w).n - 1 =
        (r3BraidRightStepA g x u w).n - 1 := by
    simp [r3BraidLeftStepA, r3BraidRightStepA, r3BraidLeftGraph, r3BraidRightGraph]
  calc
    bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
        (r3BraidLeftStepAA g x u w)
        =
      bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
        (r3BraidLeftStepAA g x u w) := by
          simpa [hFuel]
    _ =
      bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
        (r3BraidRightStepAA g x u w) := by
          simpa [hAAgraph]

/-- Graph-equality to leaf-evaluation equality converter for `AB`. -/
private theorem leaf_eval_AB_eq_of_graph_eq
    {g : PDGraph} {x u w : Nat}
    (hABgraph : r3BraidLeftStepAB g x u w = r3BraidRightStepAB g x u w) :
    bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
        (r3BraidLeftStepAB g x u w) =
      bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
        (r3BraidRightStepAB g x u w) := by
  have hFuel :
      (r3BraidLeftStepA g x u w).n - 1 =
        (r3BraidRightStepA g x u w).n - 1 := by
    simp [r3BraidLeftStepA, r3BraidRightStepA, r3BraidLeftGraph, r3BraidRightGraph]
  calc
    bracketGraphMLAux ((r3BraidLeftStepA g x u w).n - 1)
        (r3BraidLeftStepAB g x u w)
        =
      bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
        (r3BraidLeftStepAB g x u w) := by
          simpa [hFuel]
    _ =
      bracketGraphMLAux ((r3BraidRightStepA g x u w).n - 1)
        (r3BraidRightStepAB g x u w) := by
          simpa [hABgraph]

/-- Graph-equality to leaf-evaluation equality converter for `BA`. -/
private theorem leaf_eval_BA_eq_of_graph_eq
    {g : PDGraph} {x u w : Nat}
    (hBAgraph : r3BraidLeftStepBA g x u w = r3BraidRightStepBA g x u w) :
    bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
        (r3BraidLeftStepBA g x u w) =
      bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
        (r3BraidRightStepBA g x u w) := by
  have hFuel :
      (r3BraidLeftStepB g x u w).n - 1 =
        (r3BraidRightStepB g x u w).n - 1 := by
    simp [r3BraidLeftStepB, r3BraidRightStepB, r3BraidLeftGraph, r3BraidRightGraph]
  calc
    bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
        (r3BraidLeftStepBA g x u w)
        =
      bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
        (r3BraidLeftStepBA g x u w) := by
          simpa [hFuel]
    _ =
      bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
        (r3BraidRightStepBA g x u w) := by
          simpa [hBAgraph]

/-- Graph-equality to leaf-evaluation equality converter for `BB`. -/
private theorem leaf_eval_BB_eq_of_graph_eq
    {g : PDGraph} {x u w : Nat}
    (hBBgraph : r3BraidLeftStepBB g x u w = r3BraidRightStepBB g x u w) :
    bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
        (r3BraidLeftStepBB g x u w) =
      bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
        (r3BraidRightStepBB g x u w) := by
  have hFuel :
      (r3BraidLeftStepB g x u w).n - 1 =
        (r3BraidRightStepB g x u w).n - 1 := by
    simp [r3BraidLeftStepB, r3BraidRightStepB, r3BraidLeftGraph, r3BraidRightGraph]
  calc
    bracketGraphMLAux ((r3BraidLeftStepB g x u w).n - 1)
        (r3BraidLeftStepBB g x u w)
        =
      bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
        (r3BraidLeftStepBB g x u w) := by
          simpa [hFuel]
    _ =
      bracketGraphMLAux ((r3BraidRightStepB g x u w).n - 1)
        (r3BraidRightStepBB g x u w) := by
          simpa [hBBgraph]

/--
Definitional reduction of the `AA` leaf-graph equality into explicit
second-smoothing obligations on the left/right first-step `A` branches.
-/
private theorem r3BraidStepAA_graph_eq_iff_rewire_delta
    (g : PDGraph) (x u w : Nat) :
    r3BraidLeftStepAA g x u w = r3BraidRightStepAA g x u w ↔
      (let leftA := r3BraidLeftStepA g x u w
       let rightA := r3BraidRightStepA g x u w
       leftA.freeLoops + smoothLastCoreML_deltaLoops leftA.n leftA.arcNbr false =
         rightA.freeLoops + smoothLastCoreML_deltaLoops rightA.n rightA.arcNbr false ∧
         (leftA.n - 1 = rightA.n - 1 ∧
           smoothLastCoreML_rewire leftA.n leftA.arcNbr false =
             smoothLastCoreML_rewire rightA.n rightA.arcNbr false)) := by
  simp [r3BraidLeftStepAA, r3BraidRightStepAA, smoothLastCoreML]

private theorem r3BraidStepA_fuel_eq
    (g : PDGraph) (x u w : Nat) :
    (r3BraidLeftStepA g x u w).n - 1 = (r3BraidRightStepA g x u w).n - 1 := by
  simp [r3BraidLeftStepA, r3BraidRightStepA, r3BraidLeftGraph, r3BraidRightGraph]

/--
Fuel-index simplified form of `r3BraidStepAA_graph_eq_iff_rewire_delta`.
-/
private theorem r3BraidStepAA_graph_eq_iff_rewire_delta_core
    (g : PDGraph) (x u w : Nat) :
    r3BraidLeftStepAA g x u w = r3BraidRightStepAA g x u w ↔
      ((let leftA := r3BraidLeftStepA g x u w
        let rightA := r3BraidRightStepA g x u w
        leftA.freeLoops + smoothLastCoreML_deltaLoops leftA.n leftA.arcNbr false =
          rightA.freeLoops + smoothLastCoreML_deltaLoops rightA.n rightA.arcNbr false)) ∧
      ((let leftA := r3BraidLeftStepA g x u w
        let rightA := r3BraidRightStepA g x u w
        smoothLastCoreML_rewire leftA.n leftA.arcNbr false =
          smoothLastCoreML_rewire rightA.n rightA.arcNbr false)) := by
  constructor
  · intro hEq
    rcases (r3BraidStepAA_graph_eq_iff_rewire_delta g x u w).1 hEq with
      ⟨hDelta, _hFuel, hRewire⟩
    exact ⟨hDelta, hRewire⟩
  · intro hCore
    rcases hCore with ⟨hDelta, hRewire⟩
    exact (r3BraidStepAA_graph_eq_iff_rewire_delta g x u w).2
      ⟨hDelta, r3BraidStepA_fuel_eq g x u w, hRewire⟩

private def aaTrackCounterexampleGraph : PDGraph :=
  { freeLoops := 0
    n := 2
    arcNbr := #[1, 0, 3, 2, 5, 4, 7, 6] }

/--
Concrete counterexample: endpoint success does **not** imply `AA` leaf-graph equality.

This rules out the over-strong Track-A closure attempt that tries to derive
`r3BraidLeftStepAA = r3BraidRightStepAA` directly from endpoint success.
-/
private theorem aaTrackCounterexample_AA_not_equal :
    r3BraidLeftStepAA aaTrackCounterexampleGraph 0 2 4 ≠
      r3BraidRightStepAA aaTrackCounterexampleGraph 0 2 4 := by
  have hL0 :
      (r3BraidLeftStepAA aaTrackCounterexampleGraph 0 2 4).arcNbr[0]! = 8 := by
    native_decide
  have hR0 :
      (r3BraidRightStepAA aaTrackCounterexampleGraph 0 2 4).arcNbr[0]! = 10 := by
    native_decide
  intro hEq
  have h08 : (8 : Nat) = 10 := by
    simpa [hL0, hR0] using congrArg (fun g => g.arcNbr[0]!) hEq
  exact Nat.ne_of_lt (by decide : (8 : Nat) < 10) h08

private theorem aaTrackCounterexample_AB_not_equal :
    r3BraidLeftStepAB aaTrackCounterexampleGraph 0 2 4 ≠
      r3BraidRightStepAB aaTrackCounterexampleGraph 0 2 4 := by
  have hNe0 :
      (r3BraidLeftStepAB aaTrackCounterexampleGraph 0 2 4).arcNbr[0]! ≠
        (r3BraidRightStepAB aaTrackCounterexampleGraph 0 2 4).arcNbr[0]! := by
    native_decide
  intro hEq
  exact hNe0 (by simpa using congrArg (fun g => g.arcNbr[0]!) hEq)

private theorem aaTrackCounterexample_BA_not_equal :
    r3BraidLeftStepBA aaTrackCounterexampleGraph 0 2 4 ≠
      r3BraidRightStepBA aaTrackCounterexampleGraph 0 2 4 := by
  have hNe0 :
      (r3BraidLeftStepBA aaTrackCounterexampleGraph 0 2 4).arcNbr[0]! ≠
        (r3BraidRightStepBA aaTrackCounterexampleGraph 0 2 4).arcNbr[0]! := by
    native_decide
  intro hEq
  exact hNe0 (by simpa using congrArg (fun g => g.arcNbr[0]!) hEq)

private theorem aaTrackCounterexample_BB_not_equal :
    r3BraidLeftStepBB aaTrackCounterexampleGraph 0 2 4 ≠
      r3BraidRightStepBB aaTrackCounterexampleGraph 0 2 4 := by
  have hNe0 :
      (r3BraidLeftStepBB aaTrackCounterexampleGraph 0 2 4).arcNbr[0]! ≠
        (r3BraidRightStepBB aaTrackCounterexampleGraph 0 2 4).arcNbr[0]! := by
    native_decide
  intro hEq
  exact hNe0 (by simpa using congrArg (fun g => g.arcNbr[0]!) hEq)

/--
Executable (LaurentPoly) bracket comparator used for concrete diagnostics on
the AA-track counterexample witness.
-/
private def execBracketEqBool (g1 g2 : PDGraph) : Bool :=
  match bracketGraph g1, bracketGraph g2 with
  | .ok p1, .ok p2 => decide (p1 = p2)
  | _, _ => false

/--
Concrete diagnostic theorem:
on `aaTrackCounterexampleGraph`, direct left/right leafwise executable bracket
equalities all fail for AA/AB/BA/BB.
-/
private theorem aaTrackCounterexample_leaf_executable_bracket_pairwise_fail :
    execBracketEqBool
      (r3BraidLeftStepAA aaTrackCounterexampleGraph 0 2 4)
      (r3BraidRightStepAA aaTrackCounterexampleGraph 0 2 4) = false ∧
    execBracketEqBool
      (r3BraidLeftStepAB aaTrackCounterexampleGraph 0 2 4)
      (r3BraidRightStepAB aaTrackCounterexampleGraph 0 2 4) = false ∧
    execBracketEqBool
      (r3BraidLeftStepBA aaTrackCounterexampleGraph 0 2 4)
      (r3BraidRightStepBA aaTrackCounterexampleGraph 0 2 4) = false ∧
    execBracketEqBool
      (r3BraidLeftStepBB aaTrackCounterexampleGraph 0 2 4)
      (r3BraidRightStepBB aaTrackCounterexampleGraph 0 2 4) = false := by
  native_decide

/--
Concrete diagnostic theorem:
despite leafwise pairwise failures on the same witness, the full endpoint R3
executable bracket remains invariant.
-/
private def aaTrackCounterexample_endpoint_execBracketEqBool : Bool :=
  match Reidemeister.r3BraidLeft aaTrackCounterexampleGraph 0 2 4,
    Reidemeister.r3BraidRight aaTrackCounterexampleGraph 0 2 4 with
  | .ok gL, .ok gR => execBracketEqBool gL gR
  | _, _ => false

private theorem aaTrackCounterexample_endpoint_executable_bracket_equal :
    aaTrackCounterexample_endpoint_execBracketEqBool = true := by
  native_decide

/--
Concrete executable counterexample candidate for the *unconditional* endpoint
R3 claim.

For this graph and `(x,u,w) = (0,2,4)`, both braid constructors return `.ok`,
but executable endpoint bracket equality fails. This indicates missing
side-conditions in the unconditional statement.
-/
private def r3ExecutableFailureCounterexampleGraph : PDGraph :=
  { freeLoops := 0
    n := 2
    arcNbr := #[1, 0, 5, 4, 3, 2, 7, 6] }

private def r3ExecutableFailure_endpoints_ok_bool : Bool :=
  match Reidemeister.r3BraidLeft r3ExecutableFailureCounterexampleGraph 0 2 4,
    Reidemeister.r3BraidRight r3ExecutableFailureCounterexampleGraph 0 2 4 with
  | .ok _, .ok _ => true
  | _, _ => false

private theorem r3ExecutableFailure_endpoints_ok :
    r3ExecutableFailure_endpoints_ok_bool = true := by
  native_decide

private def r3ExecutableFailure_endpoint_execBracketEqBool : Bool :=
  match Reidemeister.r3BraidLeft r3ExecutableFailureCounterexampleGraph 0 2 4,
    Reidemeister.r3BraidRight r3ExecutableFailureCounterexampleGraph 0 2 4 with
  | .ok gL, .ok gR => execBracketEqBool gL gR
  | _, _ => false

private theorem r3ExecutableFailure_endpoint_executable_bracket_neq :
    r3ExecutableFailure_endpoint_execBracketEqBool = false := by
  native_decide

/--
Definitional reduction of the `AB` leaf-graph equality into explicit
second-smoothing obligations on the left/right first-step `A` branches.
-/
private theorem r3BraidStepAB_graph_eq_iff_rewire_delta
    (g : PDGraph) (x u w : Nat) :
    r3BraidLeftStepAB g x u w = r3BraidRightStepAB g x u w ↔
      (let leftA := r3BraidLeftStepA g x u w
       let rightA := r3BraidRightStepA g x u w
       leftA.freeLoops + smoothLastCoreML_deltaLoops leftA.n leftA.arcNbr true =
         rightA.freeLoops + smoothLastCoreML_deltaLoops rightA.n rightA.arcNbr true ∧
         (leftA.n - 1 = rightA.n - 1 ∧
           smoothLastCoreML_rewire leftA.n leftA.arcNbr true =
             smoothLastCoreML_rewire rightA.n rightA.arcNbr true)) := by
  simp [r3BraidLeftStepAB, r3BraidRightStepAB, smoothLastCoreML]

/--
Definitional reduction of the `BA` leaf-graph equality into explicit
second-smoothing obligations on the left/right first-step `B` branches.
-/
private theorem r3BraidStepBA_graph_eq_iff_rewire_delta
    (g : PDGraph) (x u w : Nat) :
    r3BraidLeftStepBA g x u w = r3BraidRightStepBA g x u w ↔
      (let leftB := r3BraidLeftStepB g x u w
       let rightB := r3BraidRightStepB g x u w
       leftB.freeLoops + smoothLastCoreML_deltaLoops leftB.n leftB.arcNbr false =
         rightB.freeLoops + smoothLastCoreML_deltaLoops rightB.n rightB.arcNbr false ∧
         (leftB.n - 1 = rightB.n - 1 ∧
           smoothLastCoreML_rewire leftB.n leftB.arcNbr false =
             smoothLastCoreML_rewire rightB.n rightB.arcNbr false)) := by
  simp [r3BraidLeftStepBA, r3BraidRightStepBA, smoothLastCoreML]

/--
Definitional reduction of the `BB` leaf-graph equality into explicit
second-smoothing obligations on the left/right first-step `B` branches.
-/
private theorem r3BraidStepBB_graph_eq_iff_rewire_delta
    (g : PDGraph) (x u w : Nat) :
    r3BraidLeftStepBB g x u w = r3BraidRightStepBB g x u w ↔
      (let leftB := r3BraidLeftStepB g x u w
       let rightB := r3BraidRightStepB g x u w
       leftB.freeLoops + smoothLastCoreML_deltaLoops leftB.n leftB.arcNbr true =
         rightB.freeLoops + smoothLastCoreML_deltaLoops rightB.n rightB.arcNbr true ∧
         (leftB.n - 1 = rightB.n - 1 ∧
           smoothLastCoreML_rewire leftB.n leftB.arcNbr true =
             smoothLastCoreML_rewire rightB.n rightB.arcNbr true)) := by
  simp [r3BraidLeftStepBB, r3BraidRightStepBB, smoothLastCoreML]

/--
Endpoint `r3SkeinStep` equality from equality of the four second-level leaf
graphs (`AA/AB/BA/BB`).
-/
theorem r3SkeinStep_eq_of_two_level_leaf_graph_equalities_endpoints
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hAAgraph : r3BraidLeftStepAA g x u w = r3BraidRightStepAA g x u w)
    (hABgraph : r3BraidLeftStepAB g x u w = r3BraidRightStepAB g x u w)
    (hBAgraph : r3BraidLeftStepBA g x u w = r3BraidRightStepBA g x u w)
    (hBBgraph : r3BraidLeftStepBB g x u w = r3BraidRightStepBB g x u w) :
    r3SkeinStep gL = r3SkeinStep gR := by
  exact r3SkeinStep_eq_of_two_level_leaf_equalities_endpoints
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
    hLeft hRight
    (leaf_eval_AA_eq_of_graph_eq (g := g) (x := x) (u := u) (w := w) hAAgraph)
    (leaf_eval_AB_eq_of_graph_eq (g := g) (x := x) (u := u) (w := w) hABgraph)
    (leaf_eval_BA_eq_of_graph_eq (g := g) (x := x) (u := u) (w := w) hBAgraph)
    (leaf_eval_BB_eq_of_graph_eq (g := g) (x := x) (u := u) (w := w) hBBgraph)

/--
Convert a left endpoint TL bridge hypothesis into the corresponding
left two-level bridge obligation.
-/
theorem left_two_level_bridge_of_tl3_endpoint
    {g gL : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hLeftTL :
      r3SkeinStep gL =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft) :
    r3SkeinStepLeftTwoLevelExpr g x u w =
      TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft := by
  have hgL : gL = r3BraidLeftGraph g x u w :=
    r3BraidLeft_eq_gOut (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft
  have hCanonical :
      r3SkeinStep (r3BraidLeftGraph g x u w) =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft := by
    simpa [hgL] using hLeftTL
  calc
    r3SkeinStepLeftTwoLevelExpr g x u w
        = r3SkeinStep (r3BraidLeftGraph g x u w) := by
            simpa using
              (r3SkeinStep_left_two_level_expr_of_r3BraidLeft_ok
                (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft).symm
    _ = TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft := hCanonical

/--
Convert a right endpoint TL bridge hypothesis into the corresponding
right two-level bridge obligation.
-/
theorem right_two_level_bridge_of_tl3_endpoint
    {g gR : PDGraph} {x u w fuel : Nat}
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hRightTL :
      r3SkeinStep gR =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    r3SkeinStepRightTwoLevelExpr g x u w =
      TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight := by
  have hgR : gR = r3BraidRightGraph g x u w :=
    r3BraidRight_eq_gOut (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight
  have hCanonical :
      r3SkeinStep (r3BraidRightGraph g x u w) =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight := by
    simpa [hgR] using hRightTL
  calc
    r3SkeinStepRightTwoLevelExpr g x u w
        = r3SkeinStep (r3BraidRightGraph g x u w) := by
            simpa using
              (r3SkeinStep_right_two_level_expr_of_r3BraidRight_ok
                (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight).symm
    _ = TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight := hCanonical

/--
Recover a left endpoint TL bridge hypothesis from a left two-level bridge
obligation.
-/
theorem left_tl_endpoint_of_two_level_bridge
    {g gL : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hLeftBridge :
      r3SkeinStepLeftTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft) :
    r3SkeinStep gL =
      TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft := by
  have hgL : gL = r3BraidLeftGraph g x u w :=
    r3BraidLeft_eq_gOut (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft
  have hCanonical :
      r3SkeinStep (r3BraidLeftGraph g x u w) =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft :=
    r3SkeinStep_left_eq_tl3_of_two_level_bridge
      (g := g) (gL := gL) (x := x) (u := u) (w := w) (fuel := fuel)
      hLeft hLeftBridge
  simpa [hgL] using hCanonical

/--
Recover a right endpoint TL bridge hypothesis from a right two-level bridge
obligation.
-/
theorem right_tl_endpoint_of_two_level_bridge
    {g gR : PDGraph} {x u w fuel : Nat}
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hRightBridge :
      r3SkeinStepRightTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    r3SkeinStep gR =
      TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight := by
  have hgR : gR = r3BraidRightGraph g x u w :=
    r3BraidRight_eq_gOut (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight
  have hCanonical :
      r3SkeinStep (r3BraidRightGraph g x u w) =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight :=
    r3SkeinStep_right_eq_tl3_of_two_level_bridge
      (g := g) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
      hRight hRightBridge
  simpa [hgR] using hCanonical

/--
Endpoint TL bridge obligations and two-level bridge obligations are equivalent
under fixed R3 braid endpoint identities.
-/
theorem tl3_endpoint_pair_iff_two_level_bridge_pair
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR) :
    ((r3SkeinStep gL =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft) ∧
      (r3SkeinStep gR =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight)) ↔
    ((r3SkeinStepLeftTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft) ∧
      (r3SkeinStepRightTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight)) := by
  constructor
  · intro hPair
    rcases hPair with ⟨hLeftTL, hRightTL⟩
    exact ⟨left_two_level_bridge_of_tl3_endpoint
        (g := g) (gL := gL) (x := x) (u := u) (w := w) (fuel := fuel)
        hLeft hLeftTL,
      right_two_level_bridge_of_tl3_endpoint
        (g := g) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
        hRight hRightTL⟩
  · intro hPair
    rcases hPair with ⟨hLeftBridge, hRightBridge⟩
    exact ⟨left_tl_endpoint_of_two_level_bridge
        (g := g) (gL := gL) (x := x) (u := u) (w := w) (fuel := fuel)
        hLeft hLeftBridge,
      right_tl_endpoint_of_two_level_bridge
        (g := g) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
        hRight hRightBridge⟩

/--
Endpoint-level TL3 bridge form of R3 invariance.

This variant keeps the bridge hypotheses in terms of the actual braid endpoints
`gL`/`gR`, avoiding exposure of internal canonical gadget names in downstream
modules.
-/
theorem bracketGraphML_r3_invariant_of_tl3_bridge_endpoints
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hLeftTL :
      r3SkeinStep gL =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft)
    (hRightTL :
      r3SkeinStep gR =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    bracketGraphML gL = bracketGraphML gR := by
  have hStepEq : r3SkeinStep gL = r3SkeinStep gR :=
    r3SkeinStep_eq_of_tl3_bridge_endpoints
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
      hLeft hRight hLeftTL hRightTL
  calc
    bracketGraphML gL = r3SkeinStep gL := by
      simpa [r3SkeinStep] using
        R3.bracketGraphML_skein_of_r3BraidLeft_ok
          (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft
    _ = r3SkeinStep gR := hStepEq
    _ = bracketGraphML gR := by
      simpa [r3SkeinStep] using
        (R3.bracketGraphML_skein_of_r3BraidRight_ok
          (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight).symm

/--
Endpoint-level bracket invariance from two-level TL bridge obligations.
-/
theorem bracketGraphML_r3_invariant_of_two_level_tl3_bridges_endpoints
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hLeftBridge :
      r3SkeinStepLeftTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft)
    (hRightBridge :
      r3SkeinStepRightTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    bracketGraphML gL = bracketGraphML gR := by
  have hStepEq : r3SkeinStep gL = r3SkeinStep gR :=
    r3SkeinStep_eq_of_two_level_tl3_bridges_endpoints
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
      hLeft hRight hLeftBridge hRightBridge
  calc
    bracketGraphML gL = r3SkeinStep gL := by
      simpa [r3SkeinStep] using
        R3.bracketGraphML_skein_of_r3BraidLeft_ok
          (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft
    _ = r3SkeinStep gR := hStepEq
    _ = bracketGraphML gR := by
      simpa [r3SkeinStep] using
        (R3.bracketGraphML_skein_of_r3BraidRight_ok
          (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight).symm

/--
Public alias form of theorem-level R3 invariance from two-level TL bridge
obligations.
-/
theorem bracketGraphML_r3_invariant_of_two_level_tl3_bridge_expr_endpoints
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hLeftBridge :
      r3SkeinStepLeftTwoLevelBridgeExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft)
    (hRightBridge :
      r3SkeinStepRightTwoLevelBridgeExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    bracketGraphML gL = bracketGraphML gR := by
  simpa [r3SkeinStepLeftTwoLevelBridgeExpr, r3SkeinStepRightTwoLevelBridgeExpr] using
    (bracketGraphML_r3_invariant_of_two_level_tl3_bridges_endpoints
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
      hLeft hRight hLeftBridge hRightBridge)

/--
Endpoint-level bracket invariance from direct equality of canonical two-level
bridge expressions.
-/
theorem bracketGraphML_r3_invariant_of_two_level_bridge_expr_eq_endpoints
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hTwoEq :
      r3SkeinStepLeftTwoLevelBridgeExpr g x u w =
        r3SkeinStepRightTwoLevelBridgeExpr g x u w) :
    bracketGraphML gL = bracketGraphML gR := by
  have hStepEq : r3SkeinStep gL = r3SkeinStep gR :=
    r3SkeinStep_eq_of_two_level_bridge_expr_eq_endpoints
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
      hLeft hRight hTwoEq
  calc
    bracketGraphML gL = r3SkeinStep gL := by
      simpa [r3SkeinStep] using
        R3.bracketGraphML_skein_of_r3BraidLeft_ok
          (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft
    _ = r3SkeinStep gR := hStepEq
    _ = bracketGraphML gR := by
      simpa [r3SkeinStep] using
        (R3.bracketGraphML_skein_of_r3BraidRight_ok
          (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight).symm

/--
Endpoint-level bracket invariance from equality of the four second-level
leaf graphs (`AA/AB/BA/BB`).
-/
theorem bracketGraphML_r3_invariant_of_two_level_leaf_graph_equalities_endpoints
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hAAgraph : r3BraidLeftStepAA g x u w = r3BraidRightStepAA g x u w)
    (hABgraph : r3BraidLeftStepAB g x u w = r3BraidRightStepAB g x u w)
    (hBAgraph : r3BraidLeftStepBA g x u w = r3BraidRightStepBA g x u w)
    (hBBgraph : r3BraidLeftStepBB g x u w = r3BraidRightStepBB g x u w) :
    bracketGraphML gL = bracketGraphML gR := by
  have hStepEq : r3SkeinStep gL = r3SkeinStep gR :=
    r3SkeinStep_eq_of_two_level_leaf_graph_equalities_endpoints
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
      hLeft hRight hAAgraph hABgraph hBAgraph hBBgraph
  calc
    bracketGraphML gL = r3SkeinStep gL := by
      simpa [r3SkeinStep] using
        R3.bracketGraphML_skein_of_r3BraidLeft_ok
          (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft
    _ = r3SkeinStep gR := hStepEq
    _ = bracketGraphML gR := by
      simpa [r3SkeinStep] using
        (R3.bracketGraphML_skein_of_r3BraidRight_ok
          (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight).symm

/-- Public endpoint: left R3 braid output rewrites to the one-step skein evaluator. -/
theorem bracketGraphML_r3BraidLeft_eq_skeinStep
    {g gL : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidLeft g x u w = .ok gL) :
    bracketGraphML gL = r3SkeinStep gL := by
  simpa [r3SkeinStep] using R3.bracketGraphML_skein_of_r3BraidLeft_ok (g := g) (gL := gL) (x := x) (u := u) (w := w) h

/-- Public endpoint: right R3 braid output rewrites to the one-step skein evaluator. -/
theorem bracketGraphML_r3BraidRight_eq_skeinStep
    {g gR : PDGraph} {x u w : Nat}
    (h : Reidemeister.r3BraidRight g x u w = .ok gR) :
    bracketGraphML gR = r3SkeinStep gR := by
  simpa [r3SkeinStep] using R3.bracketGraphML_skein_of_r3BraidRight_ok (g := g) (gR := gR) (x := x) (u := u) (w := w) h

/--
Public theorem-level R3 bracket endpoint (no axioms):
if the one-step skein evaluators agree on the two braid endpoints, then the
Mathlib bracket signatures agree.
-/
theorem bracketGraphML_r3_invariant_of_skeinStep_eq
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hStepEq : r3SkeinStep gL = r3SkeinStep gR) :
    bracketGraphML gL = bracketGraphML gR := by
  calc
    bracketGraphML gL = r3SkeinStep gL := bracketGraphML_r3BraidLeft_eq_skeinStep (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft
    _ = r3SkeinStep gR := hStepEq
    _ = bracketGraphML gR := (bracketGraphML_r3BraidRight_eq_skeinStep (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight).symm

/--
Endpoint equality bridge: for R3 braid outputs, one-step skein-step equality is
equivalent to bracket-signature equality.
-/
theorem r3SkeinStep_eq_iff_bracketGraphML_eq
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR) :
    r3SkeinStep gL = r3SkeinStep gR ↔
      bracketGraphML gL = bracketGraphML gR := by
  constructor
  · intro hStepEq
    exact bracketGraphML_r3_invariant_of_skeinStep_eq
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
      hLeft hRight hStepEq
  · intro hBracketEq
    calc
      r3SkeinStep gL = bracketGraphML gL := by
        simpa using
          (bracketGraphML_r3BraidLeft_eq_skeinStep
            (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft).symm
      _ = bracketGraphML gR := hBracketEq
      _ = r3SkeinStep gR := by
        simpa using
          (bracketGraphML_r3BraidRight_eq_skeinStep
            (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight)

/--
Endpoint one-step skein-step equality from bracket-signature equality.
-/
theorem r3SkeinStep_eq_of_bracketGraphML_eq
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hBracketEq : bracketGraphML gL = bracketGraphML gR) :
    r3SkeinStep gL = r3SkeinStep gR :=
  (r3SkeinStep_eq_iff_bracketGraphML_eq
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
    hLeft hRight).2 hBracketEq

/--
Unified bridge witness for theorem-level R3 endpoint invariance.

Callers may supply either:
1. a direct endpoint skein-step equality witness, or
2. endpoint TL3 bridge correspondences at some fuel.
-/
def R3SkeinBridgeWitness
    (g gL gR : PDGraph) (x u w : Nat) : Prop :=
  (r3SkeinStep gL = r3SkeinStep gR) ∨
    ∃ fuel : Nat,
      r3SkeinStep gL =
          TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft ∧
        r3SkeinStep gR =
          TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight

/--
Bundled C.2 witness: both two-level bridge obligations at some fuel.
-/
def R3TwoLevelBridgeWitness
    (g : PDGraph) (x u w : Nat) : Prop :=
  ∃ fuel : Nat,
    r3SkeinStepLeftTwoLevelBridgeExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft ∧
      r3SkeinStepRightTwoLevelBridgeExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight

/-- Constructor: direct skein-step equality gives an R3 bridge witness. -/
theorem r3SkeinBridgeWitness_of_skeinStep_eq
    {g gL gR : PDGraph} {x u w : Nat}
    (hStepEq : r3SkeinStep gL = r3SkeinStep gR) :
    R3SkeinBridgeWitness g gL gR x u w :=
  Or.inl hStepEq

/-- Constructor: endpoint TL3 bridge correspondences give an R3 bridge witness. -/
theorem r3SkeinBridgeWitness_of_tl3_bridge_endpoints
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeftTL :
      r3SkeinStep gL =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft)
    (hRightTL :
      r3SkeinStep gR =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    R3SkeinBridgeWitness g gL gR x u w :=
  Or.inr ⟨fuel, hLeftTL, hRightTL⟩

/--
Constructor: two-level TL bridge obligations induce an R3 bridge witness.
-/
theorem r3SkeinBridgeWitness_of_two_level_tl3_bridges_endpoints
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hLeftBridge :
      r3SkeinStepLeftTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft)
    (hRightBridge :
      r3SkeinStepRightTwoLevelExpr g x u w =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    R3SkeinBridgeWitness g gL gR x u w :=
  Or.inl (r3SkeinStep_eq_of_two_level_tl3_bridges_endpoints
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
    hLeft hRight hLeftBridge hRightBridge)

/--
Constructor: an expanded two-level bridge witness induces an
`R3SkeinBridgeWitness`.
-/
theorem r3SkeinBridgeWitness_of_two_level_expanded_bridges_endpoints
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hExpanded : R3TwoLevelExpandedBridgeWitness fuel g x u w) :
    R3SkeinBridgeWitness g gL gR x u w :=
  Or.inl (r3SkeinStep_eq_of_two_level_expanded_bridges_endpoints
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
    hLeft hRight hExpanded)

/--
Constructor: explicit second-level leaf-graph equalities (`AA/AB/BA/BB`)
induce an `R3SkeinBridgeWitness`.
-/
theorem r3SkeinBridgeWitness_of_two_level_leaf_graph_equalities_endpoints
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hAAgraph : r3BraidLeftStepAA g x u w = r3BraidRightStepAA g x u w)
    (hABgraph : r3BraidLeftStepAB g x u w = r3BraidRightStepAB g x u w)
    (hBAgraph : r3BraidLeftStepBA g x u w = r3BraidRightStepBA g x u w)
    (hBBgraph : r3BraidLeftStepBB g x u w = r3BraidRightStepBB g x u w) :
    R3SkeinBridgeWitness g gL gR x u w :=
  Or.inl (r3SkeinStep_eq_of_two_level_leaf_graph_equalities_endpoints
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
    hLeft hRight hAAgraph hABgraph hBAgraph hBBgraph)

/--
Constructor: direct equality of the canonical two-level bridge expressions
induces an `R3SkeinBridgeWitness`.
-/
theorem r3SkeinBridgeWitness_of_two_level_bridge_expr_eq_endpoints
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hTwoEq :
      r3SkeinStepLeftTwoLevelBridgeExpr g x u w =
        r3SkeinStepRightTwoLevelBridgeExpr g x u w) :
    R3SkeinBridgeWitness g gL gR x u w :=
  Or.inl (r3SkeinStep_eq_of_two_level_bridge_expr_eq_endpoints
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
    hLeft hRight hTwoEq)

/--
Constructor: a bundled two-level bridge witness induces an `R3SkeinBridgeWitness`.
-/
theorem r3SkeinBridgeWitness_of_two_level_bridge_witness
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hTwo : R3TwoLevelBridgeWitness g x u w) :
    R3SkeinBridgeWitness g gL gR x u w := by
  rcases hTwo with ⟨fuel, hLeftBridge, hRightBridge⟩
  exact r3SkeinBridgeWitness_of_two_level_tl3_bridges_endpoints
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
    hLeft hRight
    (by simpa [r3SkeinStepLeftTwoLevelBridgeExpr] using hLeftBridge)
    (by simpa [r3SkeinStepRightTwoLevelBridgeExpr] using hRightBridge)

/--
Scoped endpoint closure from a bundled two-level bridge witness.

This is the constructive replacement for the over-strong unconditional target:
endpoint equality is derived only once a concrete bridge witness exists.
-/
theorem r3SkeinStep_eq_of_two_level_bridge_witness_endpoints
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hTwo : R3TwoLevelBridgeWitness g x u w) :
    r3SkeinStep gL = r3SkeinStep gR := by
  rcases hTwo with ⟨fuel, hLeftBridge, hRightBridge⟩
  exact r3SkeinStep_eq_of_two_level_tl3_bridges_endpoints
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
    hLeft hRight
    (by simpa [r3SkeinStepLeftTwoLevelBridgeExpr] using hLeftBridge)
    (by simpa [r3SkeinStepRightTwoLevelBridgeExpr] using hRightBridge)

/--
Scoped endpoint bracket invariance from a bundled two-level bridge witness.
-/
theorem bracketGraphML_r3_invariant_of_two_level_bridge_witness_endpoints
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hTwo : R3TwoLevelBridgeWitness g x u w) :
    bracketGraphML gL = bracketGraphML gR := by
  rcases hTwo with ⟨fuel, hLeftBridge, hRightBridge⟩
  exact bracketGraphML_r3_invariant_of_two_level_tl3_bridges_endpoints
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
    hLeft hRight
    (by simpa [r3SkeinStepLeftTwoLevelBridgeExpr] using hLeftBridge)
    (by simpa [r3SkeinStepRightTwoLevelBridgeExpr] using hRightBridge)

/--
Left endpoint adapter: any TL3 bridge equality stated on `bracketGraphML` can be
reused as the corresponding `r3SkeinStep` bridge equality.
-/
theorem r3SkeinStep_left_eq_tl3_of_bracketGraphML_left_eq_tl3
    {g gL : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hLeftBracketTL :
      bracketGraphML gL =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft) :
    r3SkeinStep gL =
      TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft := by
  calc
    r3SkeinStep gL = bracketGraphML gL := by
      simpa using
        (bracketGraphML_r3BraidLeft_eq_skeinStep
          (g := g) (gL := gL) (x := x) (u := u) (w := w) hLeft).symm
    _ = TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft := hLeftBracketTL

/--
Right endpoint adapter: any TL3 bridge equality stated on `bracketGraphML` can
be reused as the corresponding `r3SkeinStep` bridge equality.
-/
theorem r3SkeinStep_right_eq_tl3_of_bracketGraphML_right_eq_tl3
    {g gR : PDGraph} {x u w fuel : Nat}
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hRightBracketTL :
      bracketGraphML gR =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    r3SkeinStep gR =
      TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight := by
  calc
    r3SkeinStep gR = bracketGraphML gR := by
      simpa using
        (bracketGraphML_r3BraidRight_eq_skeinStep
          (g := g) (gR := gR) (x := x) (u := u) (w := w) hRight).symm
    _ = TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight := hRightBracketTL

/--
Constructor: endpoint TL3 bridge correspondences stated at the
`bracketGraphML` level induce an R3 bridge witness.
-/
theorem r3SkeinBridgeWitness_of_bracketGraphML_tl3_endpoints
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hLeftBracketTL :
      bracketGraphML gL =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft)
    (hRightBracketTL :
      bracketGraphML gR =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    R3SkeinBridgeWitness g gL gR x u w := by
  exact r3SkeinBridgeWitness_of_tl3_bridge_endpoints
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
    (r3SkeinStep_left_eq_tl3_of_bracketGraphML_left_eq_tl3
      (g := g) (gL := gL) (x := x) (u := u) (w := w) (fuel := fuel)
      hLeft hLeftBracketTL)
    (r3SkeinStep_right_eq_tl3_of_bracketGraphML_right_eq_tl3
      (g := g) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
      hRight hRightBracketTL)

/--
Constructor: endpoint bracket-signature equality yields an R3 bridge witness.

This uses the endpoint equivalence
`r3SkeinStep_eq_iff_bracketGraphML_eq` for R3 braid outputs.
-/
theorem r3SkeinBridgeWitness_of_bracketGraphML_eq
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hBracketEq : bracketGraphML gL = bracketGraphML gR) :
    R3SkeinBridgeWitness g gL gR x u w :=
  Or.inl (r3SkeinStep_eq_of_bracketGraphML_eq
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
    hLeft hRight hBracketEq)

/--
Endpoint one-step skein equality is equivalent to having a unified bridge witness.
-/
theorem r3SkeinStep_eq_iff_bridge_witness
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR) :
    r3SkeinStep gL = r3SkeinStep gR ↔
      R3SkeinBridgeWitness g gL gR x u w := by
  constructor
  · intro hStepEq
    exact r3SkeinBridgeWitness_of_skeinStep_eq
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) hStepEq
  · intro hBridge
    rcases hBridge with hStepEq | ⟨fuel, hLeftTL, hRightTL⟩
    · exact hStepEq
    · exact r3SkeinStep_eq_of_tl3_bridge_endpoints
        (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
        hLeft hRight hLeftTL hRightTL

/--
Endpoint-level skein-step equality extracted from a unified bridge witness.
-/
theorem r3SkeinStep_eq_of_bridge_witness
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hBridge : R3SkeinBridgeWitness g gL gR x u w) :
    r3SkeinStep gL = r3SkeinStep gR := by
  rcases hBridge with hStepEq | ⟨fuel, hLeftTL, hRightTL⟩
  · exact hStepEq
  · exact r3SkeinStep_eq_of_tl3_bridge_endpoints
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
      hLeft hRight hLeftTL hRightTL

/--
Unified theorem-level R3 bracket endpoint.

This theorem gives a single entry point with a disjunctive bridge witness, so
proof search can choose either the direct skein-step route or the TL3 endpoint
bridge route and still reach the same bracket invariance conclusion.
-/
theorem bracketGraphML_r3_invariant_of_bridge_witness
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hBridge : R3SkeinBridgeWitness g gL gR x u w) :
    bracketGraphML gL = bracketGraphML gR := by
  rcases hBridge with hStepEq | ⟨fuel, hLeftTL, hRightTL⟩
  · exact bracketGraphML_r3_invariant_of_skeinStep_eq
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
      hLeft hRight hStepEq
  · exact bracketGraphML_r3_invariant_of_tl3_bridge_endpoints
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
      hLeft hRight hLeftTL hRightTL

/--
Endpoint bracket-signature equality is equivalent to having a unified bridge witness.
-/
theorem bracketGraphML_eq_iff_bridge_witness
    {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR) :
    bracketGraphML gL = bracketGraphML gR ↔
      R3SkeinBridgeWitness g gL gR x u w := by
  constructor
  · intro hBracketEq
    exact r3SkeinBridgeWitness_of_bracketGraphML_eq
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
      hLeft hRight hBracketEq
  · intro hBridge
    exact bracketGraphML_r3_invariant_of_bridge_witness
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
      hLeft hRight hBridge

/--
Global reduction: the unconditional endpoint `r3SkeinStep` goal is equivalent
to pointwise bridge-witness construction.
-/
theorem r3SkeinStep_unconditional_goal_iff_bridge_witness_goal :
    (∀ {g gL gR : PDGraph} {x u w : Nat},
      Reidemeister.r3BraidLeft g x u w = .ok gL →
      Reidemeister.r3BraidRight g x u w = .ok gR →
      r3SkeinStep gL = r3SkeinStep gR) ↔
    (∀ {g gL gR : PDGraph} {x u w : Nat},
      Reidemeister.r3BraidLeft g x u w = .ok gL →
      Reidemeister.r3BraidRight g x u w = .ok gR →
      R3SkeinBridgeWitness g gL gR x u w) := by
  constructor
  · intro h g gL gR x u w hLeft hRight
    exact (r3SkeinStep_eq_iff_bridge_witness
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
      hLeft hRight).1 (h hLeft hRight)
  · intro h g gL gR x u w hLeft hRight
    exact (r3SkeinStep_eq_iff_bridge_witness
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
      hLeft hRight).2 (h hLeft hRight)

/--
Global reduction: the unconditional endpoint bracket-invariance goal is
equivalent to pointwise bridge-witness construction.
-/
theorem bracketGraphML_unconditional_goal_iff_bridge_witness_goal :
    (∀ {g gL gR : PDGraph} {x u w : Nat},
      Reidemeister.r3BraidLeft g x u w = .ok gL →
      Reidemeister.r3BraidRight g x u w = .ok gR →
      bracketGraphML gL = bracketGraphML gR) ↔
    (∀ {g gL gR : PDGraph} {x u w : Nat},
      Reidemeister.r3BraidLeft g x u w = .ok gL →
      Reidemeister.r3BraidRight g x u w = .ok gR →
      R3SkeinBridgeWitness g gL gR x u w) := by
  constructor
  · intro h g gL gR x u w hLeft hRight
    exact (bracketGraphML_eq_iff_bridge_witness
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
      hLeft hRight).1 (h hLeft hRight)
  · intro h g gL gR x u w hLeft hRight
    exact (bracketGraphML_eq_iff_bridge_witness
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
      hLeft hRight).2 (h hLeft hRight)

/--
Direct endpoint skein-step equality from TL3 bridge correspondences stated
at the `bracketGraphML` level.
-/
theorem r3SkeinStep_eq_of_bracketGraphML_tl3_bridge_endpoints
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hLeftBracketTL :
      bracketGraphML gL =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft)
    (hRightBracketTL :
      bracketGraphML gR =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    r3SkeinStep gL = r3SkeinStep gR := by
  exact r3SkeinStep_eq_of_bridge_witness
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
    hLeft hRight
    (r3SkeinBridgeWitness_of_bracketGraphML_tl3_endpoints
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
      hLeft hRight hLeftBracketTL hRightBracketTL)

/--
Direct R3 bracket invariance from TL3 bridge correspondences stated at the
`bracketGraphML` level.
-/
theorem bracketGraphML_r3_invariant_of_bracketGraphML_tl3_bridge_endpoints
    {g gL gR : PDGraph} {x u w fuel : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hLeftBracketTL :
      bracketGraphML gL =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordLeft)
    (hRightBracketTL :
      bracketGraphML gR =
        TL3Context.evalTL3Expr fuel g x u w R3.tlWordRight) :
    bracketGraphML gL = bracketGraphML gR := by
  exact bracketGraphML_r3_invariant_of_bridge_witness
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
    hLeft hRight
    (r3SkeinBridgeWitness_of_bracketGraphML_tl3_endpoints
      (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w) (fuel := fuel)
      hLeft hRight hLeftBracketTL hRightBracketTL)

end

end Kauffman

end Knot
end Topology
end HeytingLean
