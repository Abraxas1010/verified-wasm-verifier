import HeytingLean.HeytingVeil.MiniCMachine.Decidable

namespace HeytingLean
namespace HeytingVeil
namespace MiniCMachine
namespace Examples

def arrLenSlot : String := MiniC.arrayLengthSlot "arr"
def arr0Slot : String := MiniC.arrayElemSlot "arr" 0
def arr1Slot : String := MiniC.arrayElemSlot "arr" 1

def arrayDomain : BoundedDomain :=
  { vars := [(arrLenSlot, 2, 2), (arr0Slot, -6, 6), (arr1Slot, -6, 6), ("i", 0, 1)] }

def arraySumFun : MiniC.Fun :=
  {
    name := "array_sum_2"
    params := [arrLenSlot, arr0Slot, arr1Slot, "i"]
    body :=
      .seq
        (.assign "i" (.intLit 0))
        (.seq
          (.arrayUpdate "arr" (.var "i") (.var arr0Slot))
          (.seq
            (.assign "i" (.intLit 1))
            (.seq
              (.arrayUpdate "arr" (.var "i") (.var arr1Slot))
              (.return (.add (.var arr0Slot) (.var arr1Slot))))))
  }

def arrayMaxFun : MiniC.Fun :=
  {
    name := "array_max_2"
    params := [arrLenSlot, arr0Slot, arr1Slot, "i"]
    body :=
      .seq
        (.assign "i" (.intLit 1))
        (.seq
          (.arrayUpdate "arr" (.var "i") (.var arr1Slot))
          (.if_ (.le (.var arr0Slot) (.var arr1Slot))
            (.return (.var arr1Slot))
            (.return (.var arr0Slot))))
  }

def arraySumMachine : ModelCheck.DecidableMachine ProgramConfig :=
  boundedMiniCMachine arraySumFun [] arrayDomain

def arrayMaxMachine : ModelCheck.DecidableMachine ProgramConfig :=
  boundedMiniCMachine arrayMaxFun [] arrayDomain

def arraySumWithinBounds : ProgramConfig → Prop
  | ⟨σ, _, .return e⟩ =>
      let st := σ.toTotalStore
      let len := st arrLenSlot
      let a := st arr0Slot
      let b := st arr1Slot
      2 ≤ len ∧ e.eval st = a + b
  | _ => True

def arrayMaxWithinBounds : ProgramConfig → Prop
  | ⟨σ, _, .return e⟩ =>
      let st := σ.toTotalStore
      let len := st arrLenSlot
      let a := st arr0Slot
      let b := st arr1Slot
      let v := e.eval st
      2 ≤ len ∧ (v = a ∨ v = b) ∧ a ≤ v ∧ b ≤ v
  | _ => True

instance : DecidablePred arraySumWithinBounds := by
  intro cfg
  cases cfg with
  | mk σ _ cont =>
      cases cont <;> simp [arraySumWithinBounds] <;> infer_instance

instance : DecidablePred arrayMaxWithinBounds := by
  intro cfg
  cases cfg with
  | mk σ _ cont =>
      cases cont <;> simp [arrayMaxWithinBounds] <;> infer_instance

#eval checkSafety arraySumMachine arraySumWithinBounds 12
#eval checkSafety arrayMaxMachine arrayMaxWithinBounds 12

end Examples
end MiniCMachine
end HeytingVeil
end HeytingLean
