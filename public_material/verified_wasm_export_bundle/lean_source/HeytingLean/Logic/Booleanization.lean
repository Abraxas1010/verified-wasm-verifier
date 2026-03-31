/-!
Booleanization shim: provide a Reg-view and `toBool` map for any carrier `Ω`.
This keeps the lens code generic without imposing heavy algebraic structure.
-/

namespace HeytingLean
namespace Logic

universe u

def Reg (Ω : Type u) := Ω

@[simp] def toBool {Ω : Type u} (x : Ω) : Reg Ω := x

@[simp] theorem toBool_id {Ω : Type u} (x : Ω) : toBool x = x := rfl

instance instRegInhabited {Ω : Type u} [Inhabited Ω] : Inhabited (Reg Ω) :=
  ‹Inhabited Ω›
instance instRegDecEq {Ω : Type u} [DecidableEq Ω] : DecidableEq (Reg Ω) :=
  ‹DecidableEq Ω›

end Logic
end HeytingLean
