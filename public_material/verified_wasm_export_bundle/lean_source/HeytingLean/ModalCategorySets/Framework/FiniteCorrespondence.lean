import HeytingLean.ModalCategorySets.Framework.FiniteStateFrames
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace HeytingLean.ModalCategorySets.Framework

open scoped Classical

universe u

abbrev PartitionWorld {n : Nat} (P : FinPartition n) := Quotient P

def partitionTuple {n : Nat} (P : FinPartition n) : Fin n → PartitionWorld P :=
  fun i => Quotient.mk P i

theorem kernelPartition_partitionTuple {n : Nat} (P : FinPartition n) :
    kernelPartition (partitionTuple P) = P := by
  ext i j
  change Quotient.mk P i = Quotient.mk P j ↔ P.r i j
  exact Quotient.eq

def quotientMapOfRefines {n : Nat} {P Q : FinPartition n} (hPQ : Refines P Q) :
    PartitionWorld P → PartitionWorld Q :=
  Quotient.map' id (by
    intro i j hij
    exact hPQ i j hij)

@[simp] theorem quotientMapOfRefines_tuple {n : Nat} {P Q : FinPartition n}
    (hPQ : Refines P Q) (i : Fin n) :
    quotientMapOfRefines hPQ (partitionTuple P i) = partitionTuple Q i := by
  rfl

theorem quotientMapOfRefines_surjective {n : Nat} {P Q : FinPartition n}
    (hPQ : Refines P Q) :
    Function.Surjective (quotientMapOfRefines hPQ) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro i
  exact Exists.intro (Quotient.mk P i) rfl

def PartitionTupleMap {n : Nat} {P Q : FinPartition n}
    (f : PartitionWorld P → PartitionWorld Q) : Prop :=
  ∀ i, f (partitionTuple P i) = partitionTuple Q i

theorem refines_of_partitionTuple_map {n : Nat} {P Q : FinPartition n}
    {f : PartitionWorld P → PartitionWorld Q}
    (hf : PartitionTupleMap f) :
    Refines P Q := by
  intro i j hij
  have hEq : partitionTuple P i = partitionTuple P j := Quot.sound hij
  have hEq' : partitionTuple Q i = partitionTuple Q j := by
    calc
      partitionTuple Q i = f (partitionTuple P i) := (hf i).symm
      _ = f (partitionTuple P j) := by simp [hEq]
      _ = partitionTuple Q j := hf j
  exact Quotient.exact hEq'

theorem exists_surjective_partition_map_iff_refines {n : Nat} {P Q : FinPartition n} :
    Nonempty {f : PartitionWorld P → PartitionWorld Q //
      Function.Surjective f ∧ PartitionTupleMap f} ↔
      Refines P Q := by
  constructor
  · rintro ⟨⟨f, -, hf⟩⟩
    exact refines_of_partitionTuple_map hf
  · intro hPQ
    refine ⟨Subtype.mk (quotientMapOfRefines hPQ) ?_⟩
    exact And.intro (quotientMapOfRefines_surjective hPQ) (quotientMapOfRefines_tuple hPQ)

abbrev PrepartitionWorld {n : Nat} (P : FinPartition n) (k : Nat) :=
  PartitionWorld P ⊕ Fin k

def prepartitionTuple {n k : Nat} (P : FinPartition n) : Fin n → PrepartitionWorld P k :=
  fun i => Sum.inl (partitionTuple P i)

theorem kernelPartition_prepartitionTuple {n k : Nat} (P : FinPartition n) :
    kernelPartition (prepartitionTuple (k := k) P) = P := by
  ext i j
  change Sum.inl (Quotient.mk P i) = Sum.inl (Quotient.mk P j) ↔ P.r i j
  simp [Quotient.eq]

def prepartitionAnchor {n : Nat} (hn : 0 < n) (Q : FinPartition n) (l : Nat) :
    PrepartitionWorld Q l :=
  Sum.inl (partitionTuple Q (Fin.mk 0 hn))

def prepartitionMapOfRefines {n k l : Nat} (hn : 0 < n) {P Q : FinPartition n}
    (hPQ : Refines P Q) :
    PrepartitionWorld P k → PrepartitionWorld Q l
  | Sum.inl q => Sum.inl (quotientMapOfRefines hPQ q)
  | Sum.inr _ => prepartitionAnchor hn Q l

@[simp] theorem prepartitionMapOfRefines_tuple {n k l : Nat} (hn : 0 < n)
    {P Q : FinPartition n} (hPQ : Refines P Q) (i : Fin n) :
    prepartitionMapOfRefines (k := k) (l := l) hn hPQ (prepartitionTuple (k := k) P i) =
      prepartitionTuple (k := l) Q i := by
  rfl

def PrepartitionTupleMap {n k l : Nat} {P Q : FinPartition n}
    (f : PrepartitionWorld P k → PrepartitionWorld Q l) : Prop :=
  ∀ i, f (prepartitionTuple (k := k) P i) = prepartitionTuple (k := l) Q i

theorem refines_of_prepartitionTuple_map {n k l : Nat} {P Q : FinPartition n}
    {f : PrepartitionWorld P k → PrepartitionWorld Q l}
    (hf : PrepartitionTupleMap f) :
    Refines P Q := by
  intro i j hij
  have hEq : prepartitionTuple (k := k) P i = prepartitionTuple (k := k) P j := by
    exact congrArg Sum.inl (Quot.sound hij)
  have hEq' : prepartitionTuple (k := l) Q i = prepartitionTuple (k := l) Q j := by
    calc
      prepartitionTuple (k := l) Q i = f (prepartitionTuple (k := k) P i) := (hf i).symm
      _ = f (prepartitionTuple (k := k) P j) := by simp [hEq]
      _ = prepartitionTuple (k := l) Q j := hf j
  exact Quotient.exact (Sum.inl.inj hEq')

theorem exists_prepartition_map_iff_refines {n k l : Nat} (hn : 0 < n)
    {P Q : FinPartition n} :
    Nonempty {f : PrepartitionWorld P k → PrepartitionWorld Q l // PrepartitionTupleMap f} ↔
      Refines P Q := by
  constructor
  · rintro ⟨⟨f, hf⟩⟩
    exact refines_of_prepartitionTuple_map hf
  · intro hPQ
    refine ⟨Subtype.mk (prepartitionMapOfRefines (k := k) (l := l) hn hPQ) ?_⟩
    exact prepartitionMapOfRefines_tuple (k := k) (l := l) hn hPQ

end HeytingLean.ModalCategorySets.Framework
