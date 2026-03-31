import Mathlib.Data.Set.Lattice
import HeytingLean.Core.Nucleus
import HeytingLean.Bridges.Nucleus.Extensions.Prenucleus
import HeytingLean.PadicDecoupling.Padic.Valuation

noncomputable section

namespace HeytingLean.PadicDecoupling.Nucleus

open Set
open HeytingLean
open HeytingLean.Bridges.Nucleus.Extensions

variable (p : ℕ) [Fact p.Prime]

abbrev DepthState := (Set ℤ_[p])ᵒᵈ

def asSet (S : DepthState p) : Set ℤ_[p] :=
  OrderDual.ofDual S

noncomputable def padicRound (k : ℕ) (x : ℤ_[p]) : ℤ_[p] :=
  (x.appr k : ℤ_[p])

def roundedSkeleton (k : ℕ) : Set ℤ_[p] :=
  {x | ∃ n : Fin (p ^ k), x = ((n : ℕ) : ℤ_[p])}

theorem padicRound_mem_skeleton (k : ℕ) (x : ℤ_[p]) :
    padicRound p k x ∈ roundedSkeleton p k := by
  refine ⟨⟨x.appr k, PadicInt.appr_lt x k⟩, ?_⟩
  simp [padicRound]

theorem roundedSkeleton_finite (k : ℕ) :
    (roundedSkeleton p k).Finite := by
  classical
  refine (Set.finite_range fun n : Fin (p ^ k) => ((n : ℕ) : ℤ_[p])).subset ?_
  intro x hx
  rcases hx with ⟨n, rfl⟩
  exact ⟨n, rfl⟩

theorem roundedSkeleton_mono {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    roundedSkeleton p k₁ ⊆ roundedSkeleton p k₂ := by
  intro x hx
  rcases hx with ⟨n, rfl⟩
  have hp1 : 1 ≤ p := Nat.succ_le_of_lt (Nat.Prime.pos (Fact.out : Nat.Prime p))
  have hpow : p ^ k₁ ≤ p ^ k₂ := Nat.pow_le_pow_right hp1 h
  exact ⟨⟨n.1, lt_of_lt_of_le n.2 hpow⟩, rfl⟩

def depthRestrict (k : ℕ) (S : DepthState p) : DepthState p :=
  OrderDual.toDual (asSet p S ∩ roundedSkeleton p k)

@[simp] theorem asSet_depthRestrict (k : ℕ) (S : DepthState p) :
    asSet p (depthRestrict p k S) = asSet p S ∩ roundedSkeleton p k :=
  rfl

@[simp] theorem asSet_inf (S T : DepthState p) :
    asSet p (S ⊓ T) = asSet p S ∪ asSet p T :=
  rfl

theorem depthRestrict_idempotent (k : ℕ) (S : DepthState p) :
    depthRestrict p k (depthRestrict p k S) = depthRestrict p k S := by
  apply congrArg OrderDual.toDual
  ext x
  simp

theorem depthRestrict_eq_self_iff (k : ℕ) (S : DepthState p) :
    depthRestrict p k S = S ↔ asSet p S ⊆ roundedSkeleton p k := by
  constructor
  · intro h x hx
    have : x ∈ asSet p (depthRestrict p k S) := by simpa [asSet, h] using hx
    simpa using this.2
  · intro h
    apply congrArg OrderDual.toDual
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, h hx⟩

def depthPrenucleus (k : ℕ) :
    Prenucleus (DepthState p) where
  act := depthRestrict p k
  extensive := by
    intro S
    show asSet p (depthRestrict p k S) ⊆ asSet p S
    intro x hx
    exact hx.1
  map_inf := by
    intro S T
    apply congrArg OrderDual.toDual
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxST, hxU⟩
      rcases hxST with hxS | hxT
      · exact Or.inl ⟨hxS, hxU⟩
      · exact Or.inr ⟨hxT, hxU⟩
    · intro hx
      rcases hx with hxS | hxT
      · exact ⟨Or.inl hxS.1, hxS.2⟩
      · exact ⟨Or.inr hxT.1, hxT.2⟩

def padicDepthNucleus (k : ℕ) :
    Core.Nucleus (DepthState p) :=
  Prenucleus.toCoreNucleus (depthPrenucleus p k) (depthRestrict_idempotent p k)

theorem padicDepthNucleus_R_def (k : ℕ) (S : DepthState p) :
    (padicDepthNucleus p k).R S = depthRestrict p k S :=
  rfl

end HeytingLean.PadicDecoupling.Nucleus
