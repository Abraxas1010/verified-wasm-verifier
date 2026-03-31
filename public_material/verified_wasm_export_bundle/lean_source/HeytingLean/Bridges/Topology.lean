import HeytingLean.Contracts.RoundTrip
import HeytingLean.Logic.StageSemantics
import HeytingLean.Logic.Dialectic
import HeytingLean.Epistemic.Occam

/-!
# Topology bridge

The topology bridge interprets the nucleus `R` as inducing a topology where
`R.Omega` (the fixed points) forms the lattice of "closed sets" in the
nucleus-induced topology.

## Key insight

A Heyting nucleus `R : α → α` is INFLATIONARY (x ≤ R x), like a closure operator:
- `R x ≥ x` (inflationary / superset)
- `R (R x) = R x` (idempotent)
- `R (x ⊓ y) = R x ⊓ R y` (preserves finite meets)

The fixed points `R.Omega` correspond to "closed sets" in this interpretation.

## Architecture

This bridge uses the same carrier structure as Graph (the ambient algebra `α`),
providing a topological interpretation of the nucleus operations.

```
R.Omega ≅ Closed Sets (nucleus-fixed points)
   │
   │ encode: extract underlying α value
   │ decode: apply R to get fixed point
   │
   └──► Carrier = α
```

The round-trip property `decode(encode(a)) = a` holds because elements of
`R.Omega` are already fixed points: `R (a : α) = (a : α)`.
-/

namespace HeytingLean
namespace Bridges
namespace Topology

open HeytingLean.Contracts
open HeytingLean.LoF
open HeytingLean.Epistemic

universe u

section
variable (α : Type u) [PrimaryAlgebra α]

open scoped Classical

/-- Topology bridge model: interprets the nucleus as inducing a topology.

The carrier is `α` itself. The nucleus `R` acts as a closure operator,
and `R.Omega` contains exactly the closed sets (R-fixed points). -/
structure Model where
  R : Reentry α

namespace Model

variable {α : Type u} [PrimaryAlgebra α]

/-- The carrier is the ambient Heyting algebra. -/
def Carrier (_M : Model α) : Type u := α

/-- Encode a closed set (R-fixed point) into the carrier.
This extracts the underlying element. -/
noncomputable def encode (M : Model α) (a : M.R.Omega) : M.Carrier :=
  (a : α)

/-- Decode a carrier element by taking its closure.
This produces an R-fixed point (closed set). -/
noncomputable def decode (M : Model α) (x : M.Carrier) : M.R.Omega :=
  Reentry.Omega.mk (R := M.R) (M.R x) (M.R.idempotent _)

/-- The round-trip contract for the topology bridge.

The key proof: for any R-fixed point `a`, we have `R (a : α) = (a : α)`,
so `decode(encode(a)) = Omega.mk (R a) _ = a`. -/
noncomputable def contract (M : Model α) : RoundTrip (R := M.R) M.Carrier where
  encode := M.encode
  decode := M.decode
  round := by
    intro a
    apply Subtype.ext
    simp [encode, decode]

/-- The closure operator on the carrier (the nucleus R itself).
This is the topological interpretation of the nucleus. -/
def closure (M : Model α) (x : α) : α :=
  M.R x

/-- Closure is inflationary: x ≤ cl(x). -/
lemma closure_inflationary (M : Model α) (x : α) :
    x ≤ M.closure x :=
  M.R.le_apply x

/-- Closure is idempotent: cl(cl(x)) = cl(x). -/
@[simp] lemma closure_idempotent (M : Model α) (x : α) :
    M.closure (M.closure x) = M.closure x := by
  simp only [closure, M.R.idempotent]

/-- Closure preserves finite meets (intersections). -/
@[simp] lemma closure_inf (M : Model α) (x y : α) :
    M.closure (x ⊓ y) = M.closure x ⊓ M.closure y := by
  simp only [closure, M.R.map_inf]

/-- An element is "closed" if it equals its closure. -/
def isClosed (M : Model α) (x : α) : Prop :=
  M.closure x = x

/-- R-fixed points are exactly the closed sets. -/
lemma isClosed_iff_fixed (M : Model α) (x : α) :
    M.isClosed x ↔ M.R x = x :=
  Iff.rfl

/-- Encoded elements are always closed. -/
lemma encode_isClosed (M : Model α) (a : M.R.Omega) :
    M.isClosed (M.encode a) :=
  Reentry.Omega.apply_coe (R := M.R) a

/-- Logical shadow: the interiorized value through the contract. -/
noncomputable def logicalShadow (M : Model α) : M.Carrier → α :=
  interiorized (R := M.R) M.contract

@[simp] lemma logicalShadow_encode (M : Model α) (a : M.R.Omega) :
    M.logicalShadow (M.contract.encode a) = M.R a := by
  unfold logicalShadow
  exact interiorized_id (R := M.R) (C := M.contract) a

@[simp] lemma logicalShadow_encode' (M : Model α) (a : M.R.Omega) :
    M.logicalShadow (M.encode a) = M.R a := by
  change M.logicalShadow (M.contract.encode a) = M.R a
  exact logicalShadow_encode (M := M) (a := a)

@[simp] lemma decode_encode (M : Model α) (a : M.R.Omega) :
    M.decode (M.contract.encode a) = a := by
  change (M.contract.decode (M.contract.encode a)) = a
  exact M.contract.round a

lemma encode_eulerBoundary (M : Model α) :
    M.encode M.R.eulerBoundary = M.R.primordial := by
  simp [Model.encode, Reentry.eulerBoundary_eq_process, Reentry.process_coe]

/-- Closure of intersection is closed. -/
lemma isClosed_closure_inf (M : Model α) (x y : α) :
    M.isClosed (M.closure (x ⊓ y)) := by
  simp only [isClosed, closure_idempotent]

/-- Stage-style MV addition lifted to the topology carrier. -/
noncomputable def stageMvAdd (M : Model α) :
    M.Carrier → M.Carrier → M.Carrier :=
  fun x y =>
    M.encode
      (HeytingLean.Logic.Stage.DialParam.mvAdd
        (P := HeytingLean.Logic.Modal.DialParam.base M.R)
        (M.decode x) (M.decode y))

/-- Stage-style effect compatibility on the topology carrier. -/
def stageEffectCompatible (M : Model α) (x y : M.Carrier) : Prop :=
  HeytingLean.Logic.Stage.DialParam.effectCompatible
    (P := HeytingLean.Logic.Modal.DialParam.base M.R)
    (M.decode x) (M.decode y)

/-- Stage-style partial effect addition on the topology carrier. -/
noncomputable def stageEffectAdd?
    (M : Model α) (x y : M.Carrier) : Option M.Carrier :=
  (HeytingLean.Logic.Stage.DialParam.effectAdd?
      (P := HeytingLean.Logic.Modal.DialParam.base M.R)
      (M.decode x) (M.decode y)).map M.encode

/-- Stage-style orthocomplement lifted to the topology carrier. -/
noncomputable def stageOrthocomplement (M : Model α) :
    M.Carrier → M.Carrier :=
  fun x =>
    M.encode
      (HeytingLean.Logic.Stage.DialParam.orthocomplement
        (P := HeytingLean.Logic.Modal.DialParam.base M.R)
        (M.decode x))

/-- Stage-style Heyting implication lifted to the topology carrier. -/
noncomputable def stageHimp (M : Model α) :
    M.Carrier → M.Carrier → M.Carrier :=
  fun x y =>
    M.encode ((M.decode x) ⇨ (M.decode y))

/-- Stage-style collapse (at ladder index `n`) on the topology carrier. -/
noncomputable def stageCollapseAt (M : Model α) (n : ℕ) :
    M.Carrier → M.Carrier :=
  fun x =>
    M.encode
      (HeytingLean.Logic.Stage.DialParam.collapseAtOmega
        (α := α) (R := M.R) n (M.decode x))

/-- Stage-style expansion (at ladder index `n`) on the topology carrier. -/
noncomputable def stageExpandAt (M : Model α) (n : ℕ) :
    M.Carrier → M.Carrier :=
  fun x =>
    M.encode
      (HeytingLean.Logic.Stage.DialParam.expandAtOmega
        (α := α) (R := M.R) n (M.decode x))

/-- Stage-style Occam reduction lifted to the topology carrier (via the contract). -/
noncomputable def stageOccam (M : Model α) :
    M.Carrier → M.Carrier :=
  Contracts.stageOccam (R := M.R) (C := M.contract)

variable {α : Type u} [PrimaryAlgebra α]

@[simp] theorem stageMvAdd_encode (M : Model α) (a b : M.R.Omega) :
    M.stageMvAdd
        (M.contract.encode a) (M.contract.encode b)
      =
        M.encode
          (HeytingLean.Logic.Stage.DialParam.mvAdd
            (P := HeytingLean.Logic.Modal.DialParam.base M.R) a b) := by
  classical
  simp [Model.stageMvAdd, Model.decode_encode]

@[simp] theorem stageEffectCompatible_encode (M : Model α) (a b : M.R.Omega) :
    M.stageEffectCompatible
        (M.contract.encode a) (M.contract.encode b) ↔
      HeytingLean.Logic.Stage.DialParam.effectCompatible
        (P := HeytingLean.Logic.Modal.DialParam.base M.R) a b := by
  simp [Model.stageEffectCompatible, Model.decode_encode]

@[simp] theorem stageEffectAdd_encode (M : Model α) (a b : M.R.Omega) :
    M.stageEffectAdd?
        (M.contract.encode a) (M.contract.encode b)
      =
        (HeytingLean.Logic.Stage.DialParam.effectAdd?
            (P := HeytingLean.Logic.Modal.DialParam.base M.R) a b).map
          M.encode := by
  classical
  simp [Model.stageEffectAdd?, Model.decode_encode]

@[simp] theorem stageOrthocomplement_encode (M : Model α) (a : M.R.Omega) :
    M.stageOrthocomplement (M.contract.encode a)
      =
        M.encode
          (HeytingLean.Logic.Stage.DialParam.orthocomplement
            (P := HeytingLean.Logic.Modal.DialParam.base M.R) a) := by
  classical
  simp [Model.stageOrthocomplement, Model.decode_encode]

@[simp] lemma stageHimp_encode (M : Model α) (a b : M.R.Omega) :
    M.stageHimp
        (M.contract.encode a) (M.contract.encode b)
      =
        M.encode (a ⇨ b) := by
  classical
  simp [Model.stageHimp, Model.decode_encode]

@[simp] lemma stageCollapseAt_encode (M : Model α) (n : ℕ)
    (a : M.R.Omega) :
    M.stageCollapseAt n (M.contract.encode a)
      =
        M.encode
          (HeytingLean.Logic.Stage.DialParam.collapseAtOmega
            (α := α) (R := M.R) n a) := by
  classical
  simp [Model.stageCollapseAt, Model.decode_encode]

@[simp] lemma stageExpandAt_encode (M : Model α) (n : ℕ)
    (a : M.R.Omega) :
    M.stageExpandAt n (M.contract.encode a)
      =
        M.encode
          (HeytingLean.Logic.Stage.DialParam.expandAtOmega
            (α := α) (R := M.R) n a) := by
  classical
  simp [Model.stageExpandAt, Model.decode_encode]

@[simp] lemma stageOccam_encode (M : Model α) (a : M.R.Omega) :
    M.stageOccam (M.contract.encode a) =
      M.contract.encode
        (Reentry.Omega.mk (R := M.R)
          (Epistemic.occam (R := M.R) (a : α))
          (Epistemic.occam_idempotent (R := M.R) (a := (a : α)))) := by
  classical
  unfold Model.stageOccam
  exact
    HeytingLean.Contracts.stageOccam_encode
      (R := M.R) (C := M.contract) a

@[simp] lemma logicalShadow_stageMvAdd_encode (M : Model α) (a b : M.R.Omega) :
    M.logicalShadow
        (M.stageMvAdd (M.contract.encode a) (M.contract.encode b))
      =
        M.R
          (HeytingLean.Logic.Stage.DialParam.mvAdd
            (P := HeytingLean.Logic.Modal.DialParam.base M.R) a b) := by
  classical
  simp [stageMvAdd_encode, Model.logicalShadow_encode']

@[simp] theorem logicalShadow_stageEffectAdd_encode (M : Model α) (a b : M.R.Omega) :
    (M.stageEffectAdd?
        (M.contract.encode a) (M.contract.encode b)).map M.logicalShadow
      =
        (HeytingLean.Logic.Stage.DialParam.effectAdd?
            (P := HeytingLean.Logic.Modal.DialParam.base M.R) a b).map
          (fun u => (u : α)) := by
  classical
  unfold Model.stageEffectAdd?
  cases h :
      HeytingLean.Logic.Stage.DialParam.effectAdd?
        (P := HeytingLean.Logic.Modal.DialParam.base M.R) a b with
  | none =>
      simp [h]
  | some u =>
      simp [h, Model.logicalShadow_encode', Reentry.Omega.apply_coe]

@[simp] lemma logicalShadow_stageOrthocomplement_encode
    (M : Model α) (a : M.R.Omega) :
    M.logicalShadow (M.stageOrthocomplement (M.contract.encode a)) =
      M.R
        (HeytingLean.Logic.Stage.DialParam.orthocomplement
          (P := HeytingLean.Logic.Modal.DialParam.base M.R) a) := by
  classical
  simp [stageOrthocomplement_encode, Model.logicalShadow_encode']

@[simp] lemma logicalShadow_stageHimp_encode
    (M : Model α) (a b : M.R.Omega) :
    M.logicalShadow
        (M.stageHimp (M.contract.encode a) (M.contract.encode b)) =
      M.R (a ⇨ b) := by
  classical
  simp [stageHimp_encode, Model.logicalShadow_encode']

@[simp] lemma logicalShadow_stageCollapseAt_encode
    (M : Model α) (n : ℕ) (a : M.R.Omega) :
    M.logicalShadow
        (M.stageCollapseAt n (M.contract.encode a)) =
      M.R
        (HeytingLean.Logic.Modal.DialParam.collapseAt
          (α := α) (R := M.R) n (a : α)) := by
  classical
  simp [Model.logicalShadow_encode']

@[simp] lemma logicalShadow_stageExpandAt_encode
    (M : Model α) (n : ℕ) (a : M.R.Omega) :
    M.logicalShadow
        (M.stageExpandAt n (M.contract.encode a)) =
      M.R
        (HeytingLean.Logic.Modal.DialParam.expandAt
          (α := α) (R := M.R) n (a : α)) := by
  classical
  simp [Model.logicalShadow_encode']

-- Dialectic synthesis: topology bridge hook
@[simp] lemma encode_synthOmega (M : Model α) (T A : M.R.Omega) :
    M.encode (HeytingLean.Logic.Dialectic.synthOmega (R := M.R) T A) =
      M.R ((T : α) ⊔ (A : α)) := by
  classical
  simp [Model.encode, HeytingLean.Logic.Dialectic.synthOmega,
    HeytingLean.Logic.Dialectic.synth]

end Model

end

end Topology
end Bridges
end HeytingLean
