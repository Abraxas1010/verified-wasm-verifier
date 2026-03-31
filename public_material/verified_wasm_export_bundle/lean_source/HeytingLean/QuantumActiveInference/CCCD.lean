/-!
# QuantumActiveInference.CCCD

Cone–cocone diagram (CCCD) scaffolding.

The unified-system spec references CCCDs as a generic representation of finite quantum reference
frames. In this repository we keep CCCD as a lightweight record that can be refined later with
full categorical structure.
-/

namespace HeytingLean
namespace QuantumActiveInference

/-- A minimal cone–cocone diagram interface (no category theory dependencies). -/
structure CCCD where
  Obj : Type
  apexCone : Obj
  apexCocone : Obj
  coneLeg : Obj → Obj
  coconeLeg : Obj → Obj
  coherence : Prop := True

/-- A quantum reference frame hook: CCCD plus a distinguished “screen” object. -/
structure QuantumReferenceFrame where
  diagram : CCCD
  screen : diagram.Obj

end QuantumActiveInference
end HeytingLean

