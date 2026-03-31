import HeytingLean.Logic.Booleanization

/-!
Proof-Carrying Boolean (PCB) Lens — Single-state flavor.
Generic over a carrier `Ω` (e.g., a fixed-point space `Ω_R`). The Booleanized
view is `Reg Ω` with `toBool : Ω → Reg Ω` (identity shim here). A policy
chooses how to lift Boolean updates back to the rich state.
-/

namespace HeytingLean
namespace Lens
namespace PCB

open HeytingLean.Logic

universe u

variable {Ω : Type u}

structure SingleUpdatePolicy (Ω : Type u) where
  put : Ω → Reg Ω → Ω
  put_get_id : ∀ (h : Ω), put h (toBool h) = h
  view_consistency : ∀ (h : Ω) (b' : Reg Ω), toBool (put h b') = b'

structure SingleState (Ω : Type u) where
  hi    : Ω
  lo    : Reg Ω
  align : lo = toBool hi

namespace SingleState

def fromHi (h : Ω) : SingleState Ω :=
  { hi := h, lo := toBool h, align := rfl }

def get (s : SingleState Ω) : Reg Ω := s.lo

def update (policy : SingleUpdatePolicy Ω)
  (s : SingleState Ω) (b' : Reg Ω) : SingleState Ω :=
  let hi' := policy.put s.hi b'
  { hi := hi', lo := b', align := by simpa using (policy.view_consistency s.hi b').symm }

end SingleState

end PCB
end Lens
end HeytingLean

