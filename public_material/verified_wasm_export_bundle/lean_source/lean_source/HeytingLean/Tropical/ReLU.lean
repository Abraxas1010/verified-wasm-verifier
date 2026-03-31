import HeytingLean.Tropical.Semiring
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Basic

/-!
# Tropical.ReLU

Basic bridge lemmas between the usual ReLU function and a max-plus tropical encoding.

This is intentionally minimal: it is a local “sanity bridge” for later, more structural work.
-/

namespace HeytingLean.Tropical

open TropicalReal

/-- ReLU function: `max 0 x`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- ReLU as tropical addition with `0` (in the `finite` fragment). -/
theorem relu_is_tropical (x : ℝ) :
    relu x = TropicalReal.toReal (TropicalReal.finite 0 + TropicalReal.finite x) := by
  simp [relu, TropicalReal.toReal]

/-- A single ReLU neuron: `max(0, b + Σᵢ wᵢ·xᵢ)`. -/
structure ReLUNeuron (n : Nat) where
  weights : Fin n → ℝ
  bias : ℝ

/-- The underlying affine form of a neuron. -/
def ReLUNeuron.affine {n : Nat} (neuron : ReLUNeuron n) (input : Fin n → ℝ) : ℝ :=
  neuron.bias + Finset.univ.sum (fun i : Fin n => neuron.weights i * input i)

/-- Evaluation of a ReLU neuron. -/
def ReLUNeuron.eval {n : Nat} (neuron : ReLUNeuron n) (input : Fin n → ℝ) : ℝ :=
  relu (neuron.affine input)

/-- A ReLU layer: a vector of neurons. -/
structure ReLULayer (n m : Nat) where
  neurons : Fin m → ReLUNeuron n

/-- Evaluate a ReLU layer pointwise. -/
def ReLULayer.eval {n m : Nat} (layer : ReLULayer n m) (input : Fin n → ℝ) : Fin m → ℝ :=
  fun j => (layer.neurons j).eval input

/-- A tropical affine form (max-plus “monomial”): an ordinary affine map `b + Σᵢ wᵢ·xᵢ`. -/
structure TropicalAffine (n : Nat) where
  weights : Fin n → ℝ
  bias : ℝ

def TropicalAffine.eval {n : Nat} (t : TropicalAffine n) (input : Fin n → ℝ) : ℝ :=
  t.bias + Finset.univ.sum (fun i : Fin n => t.weights i * input i)

/-- A tiny “tropical polynomial”: a finite max of affine forms, with a default baseline `0`. -/
structure TropicalPolynomial (n : Nat) where
  terms : List (TropicalAffine n)

def TropicalPolynomial.eval {n : Nat} (tp : TropicalPolynomial n) (input : Fin n → ℝ) : ℝ :=
  tp.terms.foldl (fun acc t => max acc (t.eval input)) 0

/-- A ReLU neuron is a max of two affine forms (`0` and its affine pre-activation). -/
theorem relu_neuron_is_tropical {n : Nat} (neuron : ReLUNeuron n) :
    ∃ tp : TropicalPolynomial n, ∀ input, neuron.eval input = tp.eval input := by
  classical
  refine ⟨⟨[{ weights := fun _ => 0, bias := 0 }, { weights := neuron.weights, bias := neuron.bias }]⟩, ?_⟩
  intro input
  simp [ReLUNeuron.eval, ReLUNeuron.affine, TropicalPolynomial.eval, TropicalAffine.eval, relu]

/-- A ReLU layer is pointwise tropical: each neuron admits a tropical-polynomial representation. -/
theorem relu_layer_is_tropical {n m : Nat} (layer : ReLULayer n m) :
    ∃ tp : Fin m → TropicalPolynomial n,
      ∀ input j, layer.eval input j = (tp j).eval input := by
  classical
  refine ⟨fun j => Classical.choose (relu_neuron_is_tropical (layer.neurons j)), ?_⟩
  intro input j
  simpa [ReLULayer.eval] using (Classical.choose_spec (relu_neuron_is_tropical (layer.neurons j)) input)

/-- A lightweight zonotope shell (used for “linear region” narratives). -/
structure Zonotope (n : Nat) where
  generators : List (Fin n → ℝ)
  center : Fin n → ℝ

/-- Associate a (very coarse) zonotope to a layer by taking weight vectors as generators. -/
def ReLULayer.zonotope {n m : Nat} (layer : ReLULayer n m) : Zonotope n :=
  { generators := (List.ofFn fun j : Fin m => (layer.neurons j).weights)
    center := fun _ => 0 }

end HeytingLean.Tropical
