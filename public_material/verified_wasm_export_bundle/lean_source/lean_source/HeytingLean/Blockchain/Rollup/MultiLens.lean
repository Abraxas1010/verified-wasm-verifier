import HeytingLean.LoF.Nucleus
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.Lens.Class
import HeytingLean.Crypto.Lens.Semantics
import HeytingLean.Crypto.Lens.Transport
import HeytingLean.Blockchain.Rollup.StateTransition
import HeytingLean.Bridges.Tensor
import HeytingLean.Bridges.Graph
import HeytingLean.Bridges.Clifford

/-!
# Rollup Multi-Lens — Encoders and Verifiers

Defines a lens-agnostic verifier over `Lens R`, and specialisations to the
Tensor/Graph/Clifford bridges via their RoundTrip contracts.
-/

namespace HeytingLean
namespace Blockchain
namespace Rollup

open HeytingLean.LoF
open HeytingLean.Crypto
open HeytingLean.Crypto.Lens

universe u v

variable {α : Type u} [PrimaryAlgebra α] {R : Reentry α}

namespace Spec

variable {n : ℕ}

/-- Lift a core environment to a lens environment via the RoundTrip encoder. -/
def envL (S : Spec (R := R) n) (L : Lens (R := R))
    (s₁ s₂ : S.State) : L.EnvL n :=
  fun i => L.enc ((S.env s₁ s₂) i)

/-- Lens-side value obtained by evaluating the transition form using lens ops. -/
def valueL (S : Spec (R := R) n) (L : Lens (R := R))
    (s₁ s₂ : S.State) : L.Carrier :=
  Lens.Form.evalL (L := L) (S.transitionForm s₁ s₂) (envL (R := R) (S := S) L s₁ s₂)

/-- Verifier over an arbitrary lens: decode the lens evaluation and demand ⊤ in Ω_R. -/
def verifyWith (S : Spec (R := R) n) (L : Lens (R := R))
    (s₁ s₂ : S.State) : Prop :=
  L.dec (valueL (R := R) (S := S) L s₁ s₂) = (⊤ : R.Omega)

end Spec

namespace Verify

variable {n : ℕ}

/-- Tensor specialisation of the verifier.
    The model's nucleus must match the spec's nucleus. -/
def tensor (S : Spec (R := R) n)
    (M : HeytingLean.Bridges.Tensor.Model α)
    (hR : M.R = R := by rfl)
    (s₁ s₂ : S.State) : Prop :=
  S.verifyWith (hR ▸ Lens.Instances.tensor (α := α) M) s₁ s₂

/-- Graph specialisation of the verifier.
    The model's nucleus must match the spec's nucleus. -/
def graph (S : Spec (R := R) n)
    (M : HeytingLean.Bridges.Graph.Model α)
    (hR : M.R = R := by rfl)
    (s₁ s₂ : S.State) : Prop :=
  S.verifyWith (hR ▸ Lens.Instances.graph (α := α) M) s₁ s₂

/-- Clifford specialisation of the verifier.
    The model's nucleus must match the spec's nucleus. -/
def clifford (S : Spec (R := R) n)
    (M : HeytingLean.Bridges.Clifford.Model α)
    (hR : M.R = R := by rfl)
    (s₁ s₂ : S.State) : Prop :=
  S.verifyWith (hR ▸ Lens.Instances.clifford (α := α) M) s₁ s₂

end Verify

/-! Cross-lens equivalence via RoundTrip transport
    (dec ∘ evalL = evalΩ ∘ dec) and decode-encode = id. -/

namespace Spec

variable {n : ℕ}

theorem verifyWith_iff_validTransition (S : Spec (R := R) n)
    (L : Lens (R := R)) (s₁ s₂ : S.State) :
    S.verifyWith L s₁ s₂ ↔ S.validTransition s₁ s₂ := by
  -- Use the transport lemma to show dec ∘ evalL ∘ enc = evalΩ
  have htransport :=
    Lens.transport (L := L)
      (φ := S.transitionForm s₁ s₂)
      (ρ := S.env s₁ s₂)
  -- Unfold definitions and apply transport
  unfold Spec.verifyWith Spec.valueL Spec.envL Spec.validTransition
  rw [htransport]

end Spec

namespace Verify

variable {n : ℕ}

theorem tensor_iff_graph (S : Spec (R := R) n)
    (MT : HeytingLean.Bridges.Tensor.Model α)
    (MG : HeytingLean.Bridges.Graph.Model α)
    (hMT : MT.R = R := by rfl)
    (hMG : MG.R = R := by rfl)
    (s₁ s₂ : S.State) :
    Verify.tensor (R := R) S MT hMT s₁ s₂ ↔ Verify.graph (R := R) S MG hMG s₁ s₂ := by
  have ht := Spec.verifyWith_iff_validTransition (R := R) (S := S)
      (L := hMT ▸ Lens.Instances.tensor (α := α) MT) s₁ s₂
  have hg := Spec.verifyWith_iff_validTransition (R := R) (S := S)
      (L := hMG ▸ Lens.Instances.graph (α := α) MG) s₁ s₂
  -- rewrite both sides to the same core proposition
  simp only [Verify.tensor, Verify.graph]
  exact Iff.trans ht (Iff.symm hg)

theorem tensor_iff_clifford (S : Spec (R := R) n)
    (MT : HeytingLean.Bridges.Tensor.Model α)
    (MC : HeytingLean.Bridges.Clifford.Model α)
    (hMT : MT.R = R := by rfl)
    (hMC : MC.R = R := by rfl)
    (s₁ s₂ : S.State) :
    Verify.tensor (R := R) S MT hMT s₁ s₂ ↔ Verify.clifford (R := R) S MC hMC s₁ s₂ := by
  have ht := Spec.verifyWith_iff_validTransition (R := R) (S := S)
      (L := hMT ▸ Lens.Instances.tensor (α := α) MT) s₁ s₂
  have hc := Spec.verifyWith_iff_validTransition (R := R) (S := S)
      (L := hMC ▸ Lens.Instances.clifford (α := α) MC) s₁ s₂
  simp only [Verify.tensor, Verify.clifford]
  exact Iff.trans ht (Iff.symm hc)

theorem graph_iff_clifford (S : Spec (R := R) n)
    (MG : HeytingLean.Bridges.Graph.Model α)
    (MC : HeytingLean.Bridges.Clifford.Model α)
    (hMG : MG.R = R := by rfl)
    (hMC : MC.R = R := by rfl)
    (s₁ s₂ : S.State) :
    Verify.graph (R := R) S MG hMG s₁ s₂ ↔ Verify.clifford (R := R) S MC hMC s₁ s₂ := by
  have hg := Spec.verifyWith_iff_validTransition (R := R) (S := S)
      (L := hMG ▸ Lens.Instances.graph (α := α) MG) s₁ s₂
  have hc := Spec.verifyWith_iff_validTransition (R := R) (S := S)
      (L := hMC ▸ Lens.Instances.clifford (α := α) MC) s₁ s₂
  simp only [Verify.graph, Verify.clifford]
  exact Iff.trans hg (Iff.symm hc)

end Verify

/-! ## Examples: trivial spec verifies on every lens -/

namespace Examples

open HeytingLean.Crypto

variable {n : ℕ}

@[simp] theorem demoSpec_verifyWith
    (L : Lens (R := R)) (s₁ s₂ : Nat) :
    (Rollup.Examples.demoSpec (R := R)).verifyWith L s₁ s₂ := by
  have h := Spec.verifyWith_iff_validTransition (R := R)
      (S := Rollup.Examples.demoSpec (R := R)) L s₁ s₂
  simpa using h.mpr (Rollup.Examples.demoSpec_valid (R := R) s₁ s₂)

@[simp] theorem demoSpec_tensor
    (M : HeytingLean.Bridges.Tensor.Model α)
    (hR : M.R = R := by rfl) (s₁ s₂ : Nat) :
    Verify.tensor (R := R) (Rollup.Examples.demoSpec (R := R)) M hR s₁ s₂ := by
  simp only [Verify.tensor]
  exact demoSpec_verifyWith (R := R) (hR ▸ Lens.Instances.tensor (α := α) M) s₁ s₂

@[simp] theorem demoSpec_graph
    (M : HeytingLean.Bridges.Graph.Model α)
    (hR : M.R = R := by rfl) (s₁ s₂ : Nat) :
    Verify.graph (R := R) (Rollup.Examples.demoSpec (R := R)) M hR s₁ s₂ := by
  simp only [Verify.graph]
  exact demoSpec_verifyWith (R := R) (hR ▸ Lens.Instances.graph (α := α) M) s₁ s₂

@[simp] theorem demoSpec_clifford
    (M : HeytingLean.Bridges.Clifford.Model α)
    (hR : M.R = R := by rfl) (s₁ s₂ : Nat) :
    Verify.clifford (R := R) (Rollup.Examples.demoSpec (R := R)) M hR s₁ s₂ := by
  simp only [Verify.clifford]
  exact demoSpec_verifyWith (R := R) (hR ▸ Lens.Instances.clifford (α := α) M) s₁ s₂

end Examples

/-! ## Counter example on every lens -/

namespace Examples

@[simp] theorem counter_tensor_accept (R : Reentry α)
    (M : HeytingLean.Bridges.Tensor.Model α)
    (hR : M.R = R := by rfl)
    (s : Rollup.Counter)
    (hguard : s.val + 1 ≤ s.limit) :
    Verify.tensor (R := R) (Rollup.counter (R := R)) M hR s
      { val := s.val + 1, limit := s.limit } := by
  simp only [Verify.tensor]
  have h := Spec.verifyWith_iff_validTransition (R := R)
      (S := Rollup.counter (R := R))
      (L := hR ▸ Lens.Instances.tensor (α := α) M)
      s { val := s.val + 1, limit := s.limit }
  exact h.mpr (Rollup.counter_accept (R := R) s hguard)

@[simp] theorem counter_graph_accept (R : Reentry α)
    (M : HeytingLean.Bridges.Graph.Model α)
    (hR : M.R = R := by rfl)
    (s : Rollup.Counter)
    (hguard : s.val + 1 ≤ s.limit) :
    Verify.graph (R := R) (Rollup.counter (R := R)) M hR s
      { val := s.val + 1, limit := s.limit } := by
  simp only [Verify.graph]
  have h := Spec.verifyWith_iff_validTransition (R := R)
      (S := Rollup.counter (R := R))
      (L := hR ▸ Lens.Instances.graph (α := α) M)
      s { val := s.val + 1, limit := s.limit }
  exact h.mpr (Rollup.counter_accept (R := R) s hguard)

@[simp] theorem counter_clifford_accept (R : Reentry α)
    (M : HeytingLean.Bridges.Clifford.Model α)
    (hR : M.R = R := by rfl)
    (s : Rollup.Counter)
    (hguard : s.val + 1 ≤ s.limit) :
    Verify.clifford (R := R) (Rollup.counter (R := R)) M hR s
      { val := s.val + 1, limit := s.limit } := by
  simp only [Verify.clifford]
  have h := Spec.verifyWith_iff_validTransition (R := R)
      (S := Rollup.counter (R := R))
      (L := hR ▸ Lens.Instances.clifford (α := α) M)
      s { val := s.val + 1, limit := s.limit }
  exact h.mpr (Rollup.counter_accept (R := R) s hguard)

end Examples

end Rollup
end Blockchain
end HeytingLean
