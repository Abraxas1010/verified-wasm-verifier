import HeytingLean.Ontology.CoinductiveBounded.Core
import HeytingLean.Genesis.CoGame
import HeytingLean.Coalgebra.Universal

/-!
# Ontology.CoinductiveBounded.Carriers

Concrete carrier adapters for the coinductive bounded ontology surface.
-/

namespace HeytingLean.Ontology.CoinductiveBounded

open CategoryTheory

universe u

/-- Graph-backed carrier reused from Genesis. -/
abbrev GraphCarrier := HeytingLean.Genesis.CoGame

/-- A packaged universal-coalgebra carrier together with its relator witness. -/
structure CoalgebraPack where
  F : Type u ⥤ Type u
  relator : HeytingLean.Coalgebra.Universal.Relator F
  carrier : HeytingLean.Coalgebra.Universal.Coalg F

namespace CoalgebraPack

/-- The underlying state type of a packaged coalgebra. -/
abbrev State (P : CoalgebraPack) : Type u :=
  P.carrier.V

end CoalgebraPack

/-- A backend-neutral witness is either graph-backed or coalgebra-backed. -/
inductive CarrierWitness
  | graph (carrier : GraphCarrier)
  | coalgebra (pack : CoalgebraPack)

namespace CarrierWitness

/-- Recover the backend tag from a witness. -/
def backend : CarrierWitness → CarrierBackend
  | .graph _ => .graph
  | .coalgebra _ => .coalgebra

@[simp] theorem backend_graph (G : GraphCarrier) :
    backend (.graph G) = .graph :=
  rfl

@[simp] theorem backend_coalgebra (P : CoalgebraPack) :
    backend (.coalgebra P) = .coalgebra :=
  rfl

end CarrierWitness

/-- Genesis adapter. -/
def fromCoGame (G : GraphCarrier) : CarrierWitness :=
  .graph G

/-- Universal-coalgebra adapter. -/
def fromCoalgebra {F : Type u ⥤ Type u} [hF : HeytingLean.Coalgebra.Universal.Relator F]
    (C : HeytingLean.Coalgebra.Universal.Coalg F) : CarrierWitness :=
  .coalgebra
    { F := F
      relator := hF
      carrier := C }

@[simp] theorem backend_fromCoGame (G : GraphCarrier) :
    (fromCoGame G).backend = .graph :=
  rfl

@[simp] theorem backend_fromCoalgebra {F : Type u ⥤ Type u}
    [HeytingLean.Coalgebra.Universal.Relator F]
    (C : HeytingLean.Coalgebra.Universal.Coalg F) :
    (fromCoalgebra C).backend = .coalgebra :=
  rfl

/-- Boolean self-loop observation for graph-backed witnesses. -/
noncomputable def graphSelfLoopContext : ObservationContext GraphCarrier Bool where
  observe := fun G => by
    classical
    exact decide (G.root ∈ G.leftSucc G.root ∧ G.root ∈ G.rightSucc G.root)
  respects_bisim := True

end HeytingLean.Ontology.CoinductiveBounded
