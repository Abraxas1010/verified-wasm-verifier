import HeytingLean.CategoryTheory.Polynomial.Arena
import HeytingLean.Rel.Basic

namespace HeytingLean.HeytingVeil.Wiring

open HeytingLean.Rel
open HeytingLean.Rel.RelOps
open HeytingLean.CategoryTheory.Polynomial

universe u v w z

/-- P1 wiring primitive: compose `Prop`-valued relations as arena wiring edges. -/
def composeWire {α : Type u} {β : Type v} {γ : Type w}
    (P : HRel α β) (Q : HRel β γ) : HRel α γ :=
  tensor P Q

/-- First P1 theorem: wire composition is associative. -/
theorem composeWire_assoc {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}
    (P : HRel α β) (Q : HRel β γ) (R : HRel γ δ) :
    composeWire (composeWire P Q) R = composeWire P (composeWire Q R) := by
  funext a
  funext d
  apply propext
  constructor
  · intro h
    rcases h with ⟨c, hPQ, hR⟩
    rcases hPQ with ⟨b, hP, hQ⟩
    exact ⟨b, hP, ⟨c, hQ, hR⟩⟩
  · intro h
    rcases h with ⟨b, hP, hQR⟩
    rcases hQR with ⟨c, hQ, hR⟩
    exact ⟨c, ⟨b, hP, hQ⟩, hR⟩

/-- Sanity witness: arena parallel positions are product positions. -/
theorem arenaParallel_pos_product (A B : CategoryTheory.Polynomial.Poly) :
    (arenaParallel A B).pos = (A.pos × B.pos) :=
  rfl

end HeytingLean.HeytingVeil.Wiring

