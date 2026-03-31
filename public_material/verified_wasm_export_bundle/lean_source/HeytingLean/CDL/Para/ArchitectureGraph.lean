import HeytingLean.CDL.Para.PolynomialSemantics
import HeytingLean.CategoryTheory.Polynomial.ArchitectureGraph

/-!
# CDL Para Architecture Graph Constraints

Bridge between `ParaHom` models and polynomial architecture-graph constraints.
This enables typed candidate filtering before costly training runs.
-/

namespace HeytingLean
namespace CDL
namespace Para

open HeytingLean.CategoryTheory.Polynomial

universe u

/-- A typed Para node carrying explicit in/out port classes. -/
structure TypedNode (X Y : Type u) where
  model : ParaHom X Y
  inPort : ArchPortKind
  outPort : ArchPortKind

namespace TypedNode

/-- Forgetful map from a typed Para node to a polynomial architecture node. -/
def toArchNode {X Y : Type u} (n : TypedNode X Y) : ArchNode :=
  { poly := paraHomToPoly n.model
    inPort := n.inPort
    outPort := n.outPort }

end TypedNode

/-- Compose two typed Para nodes only when port classes are compatible. -/
def composeIfCompatible? {X Y Z : Type u}
    (f : TypedNode X Y) (g : TypedNode Y Z) : Option (TypedNode X Z) :=
  if f.outPort = g.inPort then
    some
      { model := ParaHom.comp g.model f.model
        inPort := f.inPort
        outPort := g.outPort }
  else
    none

theorem composeIfCompatible?_none_of_mismatch {X Y Z : Type u}
    (f : TypedNode X Y) (g : TypedNode Y Z) (h : f.outPort ≠ g.inPort) :
    composeIfCompatible? f g = none := by
  unfold composeIfCompatible?
  simp [h]

theorem composeIfCompatible?_some_of_match {X Y Z : Type u}
    (f : TypedNode X Y) (g : TypedNode Y Z) (h : f.outPort = g.inPort) :
    (composeIfCompatible? f g).isSome = true := by
  unfold composeIfCompatible?
  simp [h]

end Para
end CDL
end HeytingLean
