import HeytingLean.LoF.Lens.Topological
import Mathlib/Topology/Algebra/Ordered

open HeytingLean.LoF.Lens.Topological

variable {X : Type _} [TopologicalSpace X]

example (s t : Set X) : I (s ∩ t) = I s ∩ I t := inf_preserving (s := s) (t := t)

example (s : Set X) : I (I s) = I s := idempotent (s := s)

