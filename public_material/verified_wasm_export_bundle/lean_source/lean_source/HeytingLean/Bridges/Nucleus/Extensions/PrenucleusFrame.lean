import HeytingLean.Bridges.Nucleus.Extensions.Prenucleus

namespace HeytingLean
namespace Bridges
namespace Nucleus
namespace Extensions

namespace Prenucleus

variable {L : Type*} [SemilatticeInf L] [OrderBot L]

instance : LE (Prenucleus L) where
  le P Q := ∀ x, P.act x ≤ Q.act x

instance : Preorder (Prenucleus L) where
  le_refl P x := le_rfl
  le_trans P Q R hPQ hQR x := (hPQ x).trans (hQR x)

instance : PartialOrder (Prenucleus L) where
  le := (· ≤ ·)
  le_refl := by intro P x; rfl
  le_trans := by intro P Q R hPQ hQR x; exact (hPQ x).trans (hQR x)
  le_antisymm := by
    intro P Q hPQ hQP
    apply Prenucleus.ext
    funext x
    exact le_antisymm (hPQ x) (hQP x)

/-- Pointwise infimum of prenuclei. -/
def infOp (P Q : Prenucleus L) : Prenucleus L where
  act x := P.act x ⊓ Q.act x
  extensive x := le_inf (P.extensive x) (Q.extensive x)
  map_inf x y := by
    simp [P.map_inf, Q.map_inf, inf_assoc, inf_left_comm]

instance : Min (Prenucleus L) where
  min := infOp

theorem inf_le_left' (P Q : Prenucleus L) : P ⊓ Q ≤ P := by
  intro x
  exact (inf_le_left : P.act x ⊓ Q.act x ≤ P.act x)

theorem inf_le_right' (P Q : Prenucleus L) : P ⊓ Q ≤ Q := by
  intro x
  exact (inf_le_right : P.act x ⊓ Q.act x ≤ Q.act x)

theorem le_inf' {P Q R : Prenucleus L} (hP : R ≤ P) (hQ : R ≤ Q) : R ≤ P ⊓ Q := by
  intro x
  exact (le_inf (hP x) (hQ x) : R.act x ≤ P.act x ⊓ Q.act x)

instance : SemilatticeInf (Prenucleus L) where
  inf := (· ⊓ ·)
  inf_le_left := inf_le_left'
  inf_le_right := inf_le_right'
  le_inf := by
    intro a b c hab hac
    exact le_inf' hab hac

end Prenucleus

end Extensions
end Nucleus
end Bridges
end HeytingLean
