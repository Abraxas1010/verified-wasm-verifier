import HeytingLean.ModalCategorySets.Propositional.Frames

namespace HeytingLean.ModalCategorySets.Framework

open HeytingLean.ModalCategorySets.Propositional

universe u

/-- Finite equality-pattern states are setoids on `Fin n`. -/
abbrev FinPartition (n : Nat) := Setoid (Fin n)

/-- `P` refines `Q` when every equality forced by `P` is also forced by `Q`. -/
def Refines {n : Nat} (P Q : FinPartition n) : Prop :=
  ∀ i j, P.r i j → Q.r i j

theorem refines_refl {n : Nat} (P : FinPartition n) : Refines P P := by
  unfold Refines
  intro i j hij
  exact hij

theorem refines_trans {n : Nat} {P Q R : FinPartition n}
    (hPQ : Refines P Q) (hQR : Refines Q R) :
    Refines P R := by
  unfold Refines at *
  intro i j hij
  exact hQR i j (hPQ i j hij)

theorem refines_antisymm {n : Nat} {P Q : FinPartition n}
    (hPQ : Refines P Q) (hQP : Refines Q P) :
    P = Q := by
  exact Setoid.ext fun i j => Iff.intro (hPQ i j) (hQP i j)

instance instLEFinPartition (n : Nat) : LE (FinPartition n) where
  le := Refines

instance instPartialOrderFinPartition (n : Nat) : PartialOrder (FinPartition n) where
  le := Refines
  le_refl := refines_refl
  le_trans := fun _ _ _ => refines_trans
  le_antisymm := fun _ _ => refines_antisymm

/-- The indiscrete partition on `Fin n`. -/
def indiscretePartition (n : Nat) : FinPartition n where
  r _ _ := True
  iseqv := by
    refine Equivalence.mk ?_ ?_ ?_
    · intro i
      trivial
    · intro i j hij
      trivial
    · intro i j k hij hjk
      trivial

theorem refines_indiscretePartition {n : Nat} (P : FinPartition n) :
    Refines P (indiscretePartition n) := by
  intro i j hij
  trivial

/-- The partition lattice frame ordered by refinement. -/
def partitionFrame (n : Nat) : Frame (FinPartition n) where
  rel P Q := Refines P Q

theorem partitionFrame_reflexive (n : Nat) :
    Reflexive (partitionFrame n) := by
  intro P
  exact refines_refl P

theorem partitionFrame_transitive (n : Nat) :
    Transitive (partitionFrame n) := by
  intro P Q R hPQ hQR
  exact refines_trans hPQ hQR

theorem partitionFrame_directed (n : Nat) :
    ∀ w u v, (partitionFrame n).rel w u → (partitionFrame n).rel w v →
      ∃ z, (partitionFrame n).rel u z ∧ (partitionFrame n).rel v z := by
  intro P Q R hPQ hPR
  refine Exists.intro (indiscretePartition n) ?_
  exact And.intro (refines_indiscretePartition Q) (refines_indiscretePartition R)

/-- Equality pattern induced by a tuple of values. -/
def kernelPartition {α : Type u} {n : Nat} (xs : Fin n → α) : FinPartition n where
  r i j := xs i = xs j
  iseqv := by
    refine Equivalence.mk ?_ ?_ ?_
    · intro i
      rfl
    · intro i j hij
      exact Eq.symm hij
    · intro i j k hij hjk
      exact Eq.trans hij hjk

/-- Finite prepartition states add a bounded cluster index on top of a partition. -/
structure PrepartitionState (n m : Nat) where
  partition : FinPartition n
  extraIndex : Fin (m + 1)

/-- Accessibility in the prepartition frame only depends on refinement of the partition component. -/
def prepartitionFrame (n m : Nat) : Frame (PrepartitionState n m) where
  rel s t := Refines s.partition t.partition

/-- Top state in the bounded prepartition frame: indiscrete partition, cluster index `0`. -/
def prepartitionTop (n m : Nat) : PrepartitionState n m where
  partition := indiscretePartition n
  extraIndex := Fin.mk 0 (Nat.succ_pos _)

theorem prepartitionFrame_reflexive (n m : Nat) :
    Reflexive (prepartitionFrame n m) := by
  intro s
  exact refines_refl s.partition

theorem prepartitionFrame_transitive (n m : Nat) :
    Transitive (prepartitionFrame n m) := by
  intro s t u hst htu
  exact refines_trans hst htu

theorem prepartitionFrame_directed (n m : Nat) :
    ∀ w u v, (prepartitionFrame n m).rel w u → (prepartitionFrame n m).rel w v →
      ∃ z, (prepartitionFrame n m).rel u z ∧ (prepartitionFrame n m).rel v z := by
  intro s t u hst hsu
  refine Exists.intro (prepartitionTop n m) ?_
  exact And.intro (refines_indiscretePartition t.partition) (refines_indiscretePartition u.partition)

/-- Distinguished root partition: all parameters remain pairwise distinct. -/
def discretePartition (n : Nat) : FinPartition n :=
  kernelPartition (fun i : Fin n => i)

/-- Root state in the bounded prepartition frame: discrete partition, cluster index `0`. -/
def prepartitionRoot (n m : Nat) : PrepartitionState n m where
  partition := discretePartition n
  extraIndex := Fin.mk 0 (Nat.succ_pos _)

/-- The finite lollipop frame: one root node accessing a cluster. -/
inductive LollipopState (m : Nat)
  | root
  | cluster (i : Fin (m + 1))

/-- Accessibility relation for the finite lollipop control frame. -/
def lollipopFrame (m : Nat) : Frame (LollipopState m) where
  rel s t :=
    match s with
    | .root => True
    | .cluster _ =>
        match t with
        | .root => False
        | .cluster _ => True

theorem lollipopFrame_reflexive (m : Nat) :
    Reflexive (lollipopFrame m) := by
  intro s
  cases s <;> simp [lollipopFrame]

theorem lollipopFrame_transitive (m : Nat) :
    Transitive (lollipopFrame m) := by
  intro s t u hst htu
  cases s <;> cases t <;> cases u <;> simp [lollipopFrame] at *

/-- The designated root world of the lollipop frame. -/
def lollipopRoot (m : Nat) : LollipopState m := .root

/-- The finite linear order used for finite surjective sentential rows. -/
def surjectionLineFrame (n : Nat) : Frame (Fin n) where
  rel i j := i ≤ j

theorem surjectionLineFrame_reflexive (n : Nat) :
    Reflexive (surjectionLineFrame n) := by
  intro i
  change i ≤ i
  simp

theorem surjectionLineFrame_transitive (n : Nat) :
    Transitive (surjectionLineFrame n) := by
  intro i j k hij hjk
  change i ≤ k
  simpa using (show i.1 ≤ k.1 from Nat.le_trans hij hjk)

/-- Sentential surjective rows use the root of the nonempty finite linear-order frame. -/
def surjectionLineRoot (n : Nat) : Fin (n + 1) := 0

end HeytingLean.ModalCategorySets.Framework
