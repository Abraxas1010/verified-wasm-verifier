import HeytingLean.PerspectivalPlenum.CechObstruction

/-!
# PerspectivalPlenum.VirtualObstructionBridge

Bridge from generic virtual stabilization behavior to lens obstruction classes.
-/

namespace HeytingLean
namespace PerspectivalPlenum
namespace VirtualObstructionBridge

open ContextualityEngine
open scoped Classical

/-- Profile supplying stabilization semantics and canonical `void/life` probes. -/
structure VirtualProfile (G : Type u) where
  stabilizes : G → Prop
  void : G
  life : G
  void_stable : stabilizes void
  life_unstable : ¬ stabilizes life

/-- Classify a virtual witness source by stabilization behavior. -/
noncomputable def virtualObstructionClass {G : Type u}
    (P : VirtualProfile G) (g : G) : CechObstructionClass :=
  if P.stabilizes g then .none else .h1_overlap_incompatibility

@[simp] theorem virtualObstructionClass_of_stable
    {G : Type u}
    (P : VirtualProfile G)
    {g : G}
    (hG : P.stabilizes g) :
    virtualObstructionClass P g = .none := by
  simp [virtualObstructionClass, hG]

@[simp] theorem virtualObstructionClass_of_unstable
    {G : Type u}
    (P : VirtualProfile G)
    {g : G}
    (hG : ¬ P.stabilizes g) :
    virtualObstructionClass P g = .h1_overlap_incompatibility := by
  simp [virtualObstructionClass, hG]

@[simp] theorem virtualObstructionClass_void
    {G : Type u}
    (P : VirtualProfile G) :
    virtualObstructionClass P P.void = .none := by
  simp [virtualObstructionClass, P.void_stable]

@[simp] theorem virtualObstructionClass_life
    {G : Type u}
    (P : VirtualProfile G) :
    virtualObstructionClass P P.life = .h1_overlap_incompatibility := by
  simp [virtualObstructionClass, P.life_unstable]

theorem virtualObstructionClass_life_ne_none
    {G : Type u}
    (P : VirtualProfile G) :
    virtualObstructionClass P P.life ≠ .none := by
  simp [virtualObstructionClass_life]

theorem virtualObstructionDegree_life
    {G : Type u}
    (P : VirtualProfile G) :
    cohomologyDegree (virtualObstructionClass P P.life) = 1 := by
  simp [virtualObstructionClass_life, cohomologyDegree]

end VirtualObstructionBridge
end PerspectivalPlenum
end HeytingLean
