import HeytingLean.GU.Connections
import HeytingLean.GU.Fields
import HeytingLean.GU.Bundles
import HeytingLean.GU.Observerse
import HeytingLean.GU.Representations

/-!
# GU.UnifiedEq (statement layer)

This module is a place to *state* GU-style unified equations over the abstract interfaces.
It intentionally does not attempt to prove physics claims.
-/

namespace HeytingLean
namespace GU

universe u v w

/-! ## Generic “equation on fields” helper -/

def EqOn {X : Type u} {A : Type v} (f g : Field X A) : Prop :=
  ∀ x : X, f x = g x

-- Minimal placeholder: a “system” is a base space plus a bundle+connection and some fields.
structure System (X : Type u) (V : Type v) where
  E : Bundle (X := X)
  nabla : Connection E
  phi : Field X V

/-! ## Additional scaffolding: observer/gauge split -/

structure ObserverSystem (X : Type u) (Y : Type v) (V : Type w)
    [TopologicalSpace X] [TopologicalSpace Y] where
  obs : Observerse X Y
  ambient : Field Y V

namespace ObserverSystem

variable {X : Type u} {Y : Type v} {V : Type w} [TopologicalSpace X] [TopologicalSpace Y]

def observed (S : ObserverSystem X Y V) : Field X V :=
  Field.pullback S.obs S.ambient

theorem observed_invasive (S : ObserverSystem X Y V) :
    Field.IsInvasive (obs := S.obs) (S.observed) :=
  Field.isInvasive_pullback (obs := S.obs) (ψ := S.ambient)

end ObserverSystem

structure GaugeSystem (X : Type u) (G : Type v) (V : Type w) [TopologicalSpace X] [Group G]
    [Representation G V] where
  P : PrincipalBundle (X := X) (G := G)
  A : PointConnection (E := P.toBundle)
  psi : Section (PrincipalBundle.associatedBundle (P := P) (V := V))

structure UnifiedSystem (X : Type u) (Y : Type v) (G : Type v) (V : Type w)
    [TopologicalSpace X] [TopologicalSpace Y] [Group G] [Representation G V] where
  obs : Observerse X Y
  gauge : GaugeSystem (X := Y) (G := G) (V := V)

end GU
end HeytingLean
