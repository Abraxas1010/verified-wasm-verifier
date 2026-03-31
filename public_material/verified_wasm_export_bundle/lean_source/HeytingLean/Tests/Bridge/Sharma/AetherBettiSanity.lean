import HeytingLean.Bridge.Sharma.AetherBetti

namespace HeytingLean.Tests.Bridge.Sharma

open HeytingLean.Bridge.Sharma.AetherBetti

#check epsilonGraph
#check epsilonFacts
#check epsilonChainComplex
#check betti1_true
#check betti1_heuristic
#check @heuristic_sound
#check @betti_error_auto
#check @betti_error_bound
#check singleton_not_ChainBettiBridge
#check singleton_ChainBettiBridgeTotal
#check ChainBettiBridgeTotal
#check linearData

example : betti1_heuristic linearData 5 = 0 := by
  native_decide

private def pathData : ByteSeq 5 :=
  fun i => ⟨10 * i.1, by omega⟩

private def cycleRichData : ByteSeq 4 :=
  fun i => ⟨i.1, by omega⟩

private def denseData : ByteSeq 5 :=
  fun i => ⟨2 * i.1, by omega⟩

private def oscillatingVal (i : Fin 8) : Nat :=
  if i.1 = 0 then 10 else
  if i.1 = 1 then 80 else
  if i.1 = 2 then 150 else
  if i.1 = 3 then 15 else
  if i.1 = 4 then 90 else
  if i.1 = 5 then 160 else
  if i.1 = 6 then 20 else 85

private theorem oscillatingVal_lt_256 (i : Fin 8) : oscillatingVal i < 256 := by
  unfold oscillatingVal
  repeat' (split_ifs <;> omega)

private def oscillatingData : ByteSeq 8 :=
  fun i => ⟨oscillatingVal i, oscillatingVal_lt_256 i⟩

private def exceptOkUnit (x : Except String Unit) : Bool :=
  match x with
  | Except.ok () => true
  | Except.error _ => false

private def exceptOkNatEq (x : Except String Nat) (n : Nat) : Bool :=
  match x with
  | Except.ok m => decide (m = n)
  | Except.error _ => false

private def exceptOkNatGe (x : Except String Nat) (n : Nat) : Bool :=
  match x with
  | Except.ok m => decide (n ≤ m)
  | Except.error _ => false

-- Phase-4 computational bridge checks (path/cycle-rich/dense).
example : exceptOkUnit ((epsilonChainComplex pathData 10).bind (fun C => C.validate)) = true := by
  native_decide

example : exceptOkUnit ((epsilonChainComplex cycleRichData 2).bind (fun C => C.validate)) = true := by
  native_decide

example : exceptOkUnit ((epsilonChainComplex denseData 20).bind (fun C => C.validate)) = true := by
  native_decide

-- Concrete β₁ values (matching |E| + 1 - |V| for these connected test graphs).
example : exceptOkNatEq (betti1_true pathData 10) 0 = true := by
  native_decide

example : exceptOkNatEq (betti1_true cycleRichData 2) 2 = true := by
  native_decide

example : exceptOkNatEq (betti1_true denseData 20) 6 = true := by
  native_decide

-- `hdetectCycle`-style computational checks on data where the heuristic fires.
example : ∃ i : Fin 8, isDetectedLoop oscillatingData i 20 := by
  native_decide

example : exceptOkNatGe (betti1_true oscillatingData 21) 1 = true := by
  native_decide

example :
    match betti1_true oscillatingData 21 with
    | .ok b => betti1_heuristic oscillatingData 20 ≤ b + (8 - 3)
    | .error _ => True := by
  simpa using
    betti_error_auto (data := oscillatingData) (tol := 20) (hn := by decide) (eps := 21)

example : ¬ ChainBettiBridge (n := 1) (fun _ => ⟨7, by decide⟩) 0 := by
  simpa using singleton_not_ChainBettiBridge

example : ChainBettiBridgeTotal (n := 1) (fun _ => ⟨7, by decide⟩) 0 := by
  simpa using singleton_ChainBettiBridgeTotal

#eval (epsilonChainComplex linearData 5).bind (fun C => C.validate)
#eval betti1_true linearData 5

end HeytingLean.Tests.Bridge.Sharma
