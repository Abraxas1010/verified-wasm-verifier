import HeytingLean.Algebra.SpectralSequence.Bridge
import HeytingLean.Algebra.SpectralSequence.Paged
import HeytingLean.LoF.Bauer.DomainTheory

namespace HeytingLean
namespace Algebra
namespace SpectralSequence

/-- Ratchet stabilization at index `N`: all later levels are equal to level `N`. -/
def Stabilizes (level : Nat → Nat) (N : Nat) : Prop :=
  ∀ n : Nat, N ≤ n → level n = level N

/-- Spectral convergence at page `N` for a filtration profile. -/
def SpectralConvergesAt (level : Nat → Nat) (N : Nat) : Prop :=
  ∀ n : Nat, N ≤ n → level n = level N

/-- In the current filtration model, convergence and stabilization coincide. -/
theorem spectralConvergesAt_iff_stabilizes (level : Nat → Nat) (N : Nat) :
    SpectralConvergesAt level N ↔ Stabilizes level N := by
  rfl

/-- A monotone ratchet with an upper bound at `N` stabilizes at `N`. -/
theorem stabilizes_of_ratchet_bounded (level : Nat → Nat) (N : Nat)
    (htraj : Topos.JRatchet.RatchetTrajectory level)
    (hub : ∀ n : Nat, level n ≤ level N) :
    Stabilizes level N := by
  intro n hn
  apply Nat.le_antisymm
  · exact hub n
  · exact htraj N n hn

/-- Spectral convergence follows from ratchet monotonicity plus eventual upper bound. -/
theorem spectralConverges_of_ratchet_bounded (level : Nat → Nat) (N : Nat)
    (htraj : Topos.JRatchet.RatchetTrajectory level)
    (hub : ∀ n : Nat, level n ≤ level N) :
    SpectralConvergesAt level N := by
  exact (spectralConvergesAt_iff_stabilizes level N).2
    (stabilizes_of_ratchet_bounded level N htraj hub)

/-- Build a page-indexed differential by truncating with ratchet level threshold. -/
def pagedOfRatchetAndComplex (C : DifferentialComplex) (level : Nat → Nat)
    (_htraj : Topos.JRatchet.RatchetTrajectory level) : PagedComplex where
  E := fun _ n => C.E n
  zero := fun _ n => C.zero n
  d := fun r n x => if level (n + 1) ≤ r then C.zero n else C.d n x
  d_zero := by
    intro r n
    by_cases h : level (n + 1) ≤ r
    · simp [h]
    · simp [h, C.d_zero]
  d_squared := by
    intro r n x
    by_cases h2 : level (n + 2) ≤ r
    · by_cases h1 : level (n + 1) ≤ r
      · simp [h1]
      · simp [h2, h1, C.d_zero]
    · by_cases h1 : level (n + 1) ≤ r
      · simp [h1]
      · simp [h1, h2, C.d_squared]

/-- Stabilization at `N` yields convergence at page `level N`. -/
theorem pagedConverges_of_stabilizes (C : DifferentialComplex) (level : Nat → Nat)
    (htraj : Topos.JRatchet.RatchetTrajectory level) (N : Nat)
    (hstab : Stabilizes level N) :
    PageConverges (pagedOfRatchetAndComplex C level htraj) (level N) := by
  intro r n hr x
  have hbound : level (n + 1) ≤ level N := by
    by_cases hleN : n + 1 ≤ N
    · exact htraj (n + 1) N hleN
    · have hNle : N ≤ n + 1 := Nat.le_of_not_ge hleN
      exact le_of_eq (hstab (n + 1) hNle)
  have hle : level (n + 1) ≤ r := le_trans hbound hr
  simp [pagedOfRatchetAndComplex, hle]

/-- Order-valued ratchet trajectory (for Kleene chains and domain-theoretic lifts). -/
def OrderRatchetTrajectory {D : Type*} [Preorder D] (level : Nat → D) : Prop :=
  Monotone level

/-- Order-valued stabilization at index `N`. -/
def OrderStabilizes {D : Type*} [Preorder D] (level : Nat → D) (N : Nat) : Prop :=
  ∀ n : Nat, N ≤ n → level n = level N

/-- The Kleene chain of a monotone map is an order-valued ratchet trajectory. -/
theorem kleeneChain_order_ratchet
    {D : Type*} [PartialOrder D] [OrderBot D]
    (f : D → D) (hf : Monotone f) :
    OrderRatchetTrajectory (LoF.Bauer.FixedPoint.kleeneChain (D := D) f) :=
  LoF.Bauer.FixedPoint.monotone_kleeneChain (D := D) hf

/-- Once the Kleene chain hits a fixed point at `N`, it is constant on all later steps. -/
theorem kleeneChain_const_from_fixed
    {D : Type*} [PartialOrder D] [OrderBot D]
    (f : D → D) (N : Nat)
    (hfix : f (LoF.Bauer.FixedPoint.kleeneChain (D := D) f N) =
      LoF.Bauer.FixedPoint.kleeneChain (D := D) f N) :
    ∀ k : Nat,
      LoF.Bauer.FixedPoint.kleeneChain (D := D) f (N + k) =
        LoF.Bauer.FixedPoint.kleeneChain (D := D) f N := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        LoF.Bauer.FixedPoint.kleeneChain (D := D) f (N + Nat.succ k)
            = f (LoF.Bauer.FixedPoint.kleeneChain (D := D) f (N + k)) := by
                simp [LoF.Bauer.FixedPoint.kleeneChain]
        _ = f (LoF.Bauer.FixedPoint.kleeneChain (D := D) f N) := by
              simp [ih]
        _ = LoF.Bauer.FixedPoint.kleeneChain (D := D) f N := hfix

/-- A fixed-point hit in the Kleene chain implies order-valued stabilization. -/
theorem kleeneChain_stabilizes_from_fixed
    {D : Type*} [PartialOrder D] [OrderBot D]
    (f : D → D) (N : Nat)
    (hfix : f (LoF.Bauer.FixedPoint.kleeneChain (D := D) f N) =
      LoF.Bauer.FixedPoint.kleeneChain (D := D) f N) :
    OrderStabilizes (LoF.Bauer.FixedPoint.kleeneChain (D := D) f) N := by
  intro n hn
  rcases Nat.exists_eq_add_of_le hn with ⟨k, hk⟩
  subst hk
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    kleeneChain_const_from_fixed (D := D) f N hfix k

/-- Nat-valued Kleene stabilization yields spectral convergence at the same index. -/
theorem spectralConverges_kleene_of_fixed
    (f : Nat → Nat) (N : Nat)
    (hfix : f (LoF.Bauer.FixedPoint.kleeneChain (D := Nat) f N) =
      LoF.Bauer.FixedPoint.kleeneChain (D := Nat) f N) :
    SpectralConvergesAt (LoF.Bauer.FixedPoint.kleeneChain (D := Nat) f) N := by
  apply (spectralConvergesAt_iff_stabilizes (LoF.Bauer.FixedPoint.kleeneChain (D := Nat) f) N).2
  intro n hn
  exact kleeneChain_stabilizes_from_fixed (D := Nat) f N hfix n hn

end SpectralSequence
end Algebra
end HeytingLean
