import HeytingLean.LoF.Combinators.SKYReducerKernel

/-!
# SKYReducerGPUWrapper

GPU-friendly fixed-capacity wrapper around the export-facing `SKYReducerKernel`
state.

This keeps the Lean-owned reducer semantics while switching from dynamic arrays
and lists to a bounded buffer layout that foreign CPU/GPU wrappers can mirror
directly.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace SKYReducerGPUWrapper

open SKYReducerKernel

/-- Fixed-capacity wrapper state mirroring the lowered C/GPU memory layout. -/
structure WrapperState where
  tags : Array Int
  lhs : Array Nat
  rhs : Array Nat
  oracleRefs : Array Nat
  stackData : Array Nat
  focus : Nat
  stackSize : Nat
  nodeCount : Nat
  maxNodes : Nat
  deriving DecidableEq, Repr, Inhabited

def WrapperState.WellFormed (s : WrapperState) : Prop :=
  s.tags.size = s.maxNodes ∧
  s.lhs.size = s.maxNodes ∧
  s.rhs.size = s.maxNodes ∧
  s.oracleRefs.size = s.maxNodes ∧
  s.stackData.size = s.maxNodes ∧
  s.nodeCount ≤ s.maxNodes ∧
  s.stackSize ≤ s.maxNodes

instance (s : WrapperState) : Decidable s.WellFormed := by
  dsimp [WrapperState.WellFormed]
  infer_instance

private def padIntArray (n : Nat) (xs : Array Int) : Array Int :=
  xs ++ Array.replicate (n - xs.size) 0

private def padNatArray (n : Nat) (xs : Array Nat) : Array Nat :=
  xs ++ Array.replicate (n - xs.size) 0

private theorem padIntArray_size (n : Nat) (xs : Array Int) (h : xs.size ≤ n) :
    (padIntArray n xs).size = n := by
  simp [padIntArray, Array.size_append, Nat.add_sub_of_le h]

private theorem padNatArray_size (n : Nat) (xs : Array Nat) (h : xs.size ≤ n) :
    (padNatArray n xs).size = n := by
  simp [padNatArray, Array.size_append, Nat.add_sub_of_le h]

private theorem extract_padIntArray (n : Nat) (xs : Array Int) :
    (padIntArray n xs).extract 0 xs.size = xs := by
  simpa [padIntArray] using
    (Array.extract_append_left (as := xs) (bs := Array.replicate (n - xs.size) 0))

private theorem extract_padNatArray (n : Nat) (xs : Array Nat) :
    (padNatArray n xs).extract 0 xs.size = xs := by
  simpa [padNatArray] using
    (Array.extract_append_left (as := xs) (bs := Array.replicate (n - xs.size) 0))

def ofKernelState? (s : SKYReducerKernel.State) : Option WrapperState :=
  if s.nodeCount ≤ s.maxNodes then
    if s.stack.length ≤ s.maxNodes then
      some
        { tags := padIntArray s.maxNodes s.tags
          lhs := padNatArray s.maxNodes s.lhs
          rhs := padNatArray s.maxNodes s.rhs
          oracleRefs := padNatArray s.maxNodes s.oracleRefs
          stackData := padNatArray s.maxNodes s.stack.reverse.toArray
          focus := s.focus
          stackSize := s.stack.length
          nodeCount := s.nodeCount
          maxNodes := s.maxNodes }
    else
      none
  else
    none

def toKernelState? (s : WrapperState) : Option SKYReducerKernel.State :=
  if _h : s.WellFormed then
    some
      { tags := s.tags.extract 0 s.nodeCount
        lhs := s.lhs.extract 0 s.nodeCount
        rhs := s.rhs.extract 0 s.nodeCount
        oracleRefs := s.oracleRefs.extract 0 s.nodeCount
        focus := s.focus
        stack := (s.stackData.extract 0 s.stackSize).toList.reverse
        maxNodes := s.maxNodes }
  else
    none

def normalize? (s : WrapperState) : Option WrapperState := do
  let core ← toKernelState? s
  ofKernelState? core

theorem toKernelState?_ofKernelState? (s : SKYReducerKernel.State)
    (htags : s.tags.size = s.nodeCount)
    (hlhs : s.lhs.size = s.nodeCount)
    (hrhs : s.rhs.size = s.nodeCount)
    (horacle : s.oracleRefs.size = s.nodeCount)
    (hnode : s.nodeCount ≤ s.maxNodes)
    (hstack : s.stack.length ≤ s.maxNodes) :
    Option.bind (ofKernelState? s) toKernelState? = some s := by
  have hlhsLe : s.lhs.size ≤ s.maxNodes := by simpa [hlhs] using hnode
  have hrhsLe : s.rhs.size ≤ s.maxNodes := by simpa [hrhs] using hnode
  have horacleLe : s.oracleRefs.size ≤ s.maxNodes := by simpa [horacle] using hnode
  have hstackArr : s.stack.reverse.toArray.size ≤ s.maxNodes := by
    simpa using hstack
  simp [ofKernelState?, toKernelState?, WrapperState.WellFormed, hnode, hstack]
  constructor
  · constructor
    · simpa using padIntArray_size s.maxNodes s.tags hnode
    · constructor
      · simpa using padNatArray_size s.maxNodes s.lhs hlhsLe
      · constructor
        · simpa using padNatArray_size s.maxNodes s.rhs hrhsLe
        · constructor
          · simpa using padNatArray_size s.maxNodes s.oracleRefs horacleLe
          · simpa using padNatArray_size s.maxNodes s.stack.reverse.toArray hstackArr
  · cases s with
    | mk tags lhs rhs oracleRefs focus stack maxNodes =>
    simp at htags hlhs hrhs horacle
    rw [SKYReducerKernel.State.mk.injEq]
    constructor
    · simpa [htags] using extract_padIntArray maxNodes tags
    · constructor
      · simpa [hlhs] using extract_padNatArray maxNodes lhs
      · constructor
        · simpa [hrhs] using extract_padNatArray maxNodes rhs
        · constructor
          · simpa [horacle] using extract_padNatArray maxNodes oracleRefs
          · constructor
            · rfl
            · constructor
              · simp [padNatArray]
              · rfl

theorem toKernelState?_ofKernelState?_wellFormed (s : SKYReducerKernel.State)
    (hwf : s.WellFormed) (hstack : s.stack.length ≤ s.maxNodes) :
    Option.bind (ofKernelState? s) toKernelState? = some s := by
  rcases hwf with ⟨hlhs, hrhs, horacle, hnode, _⟩
  exact toKernelState?_ofKernelState? s rfl hlhs hrhs horacle hnode hstack

theorem normalize?_ofKernelState? (s : SKYReducerKernel.State)
    (htags : s.tags.size = s.nodeCount)
    (hlhs : s.lhs.size = s.nodeCount)
    (hrhs : s.rhs.size = s.nodeCount)
    (horacle : s.oracleRefs.size = s.nodeCount)
    (hnode : s.nodeCount ≤ s.maxNodes)
    (hstack : s.stack.length ≤ s.maxNodes) :
    Option.bind (ofKernelState? s) normalize? = ofKernelState? s := by
  have hround :
      toKernelState?
          { tags := padIntArray s.maxNodes s.tags
            lhs := padNatArray s.maxNodes s.lhs
            rhs := padNatArray s.maxNodes s.rhs
            oracleRefs := padNatArray s.maxNodes s.oracleRefs
            stackData := padNatArray s.maxNodes s.stack.reverse.toArray
            focus := s.focus
            stackSize := s.stack.length
            nodeCount := s.nodeCount
            maxNodes := s.maxNodes } = some s := by
    simpa [ofKernelState?, hnode, hstack] using
      (toKernelState?_ofKernelState? s htags hlhs hrhs horacle hnode hstack)
  simp [normalize?, ofKernelState?, hnode, hstack, hround]

theorem normalize?_ofKernelState?_wellFormed (s : SKYReducerKernel.State)
    (hwf : s.WellFormed) (hstack : s.stack.length ≤ s.maxNodes) :
    Option.bind (ofKernelState? s) normalize? = ofKernelState? s := by
  rcases hwf with ⟨hlhs, hrhs, horacle, hnode, _⟩
  exact normalize?_ofKernelState? s rfl hlhs hrhs horacle hnode hstack

theorem step_bind_ofKernelState?_wellFormed (oracleEval : Nat → Bool)
    (s : SKYReducerKernel.State) (hwf : s.WellFormed) (hstack : s.stack.length ≤ s.maxNodes) :
    Option.bind (ofKernelState? s) (fun wrapped => do
      let core ← toKernelState? wrapped
      let result := SKYReducerKernel.step oracleEval core
      let wrapped' ← ofKernelState? result.state
      pure (result.status, wrapped')) = (do
      let r := SKYReducerKernel.step oracleEval s
      let wrapped ← ofKernelState? r.state
      pure (r.status, wrapped)) := by
  rcases hwf with ⟨hlhs, hrhs, horacle, hnode, _⟩
  have hround :
      toKernelState?
          { tags := padIntArray s.maxNodes s.tags
            lhs := padNatArray s.maxNodes s.lhs
            rhs := padNatArray s.maxNodes s.rhs
            oracleRefs := padNatArray s.maxNodes s.oracleRefs
            stackData := padNatArray s.maxNodes s.stack.reverse.toArray
            focus := s.focus
            stackSize := s.stack.length
            nodeCount := s.nodeCount
            maxNodes := s.maxNodes } = some s := by
    simpa [ofKernelState?, hnode, hstack] using
      (toKernelState?_ofKernelState? s rfl hlhs hrhs horacle hnode hstack)
  simp [ofKernelState?, hnode, hstack, hround]

def oracleArrayEval (vals : Array Int) (ref : Nat) : Bool :=
  match vals[ref]? with
  | some n => n ≠ 0
  | none => false

def step? (oracleEval : Nat → Bool) (s : WrapperState) :
    Option (StepStatus × WrapperState) := do
  let core ← toKernelState? s
  let result := SKYReducerKernel.step oracleEval core
  let wrapped ← ofKernelState? result.state
  pure (result.status, wrapped)

def runFuel? (oracleEval : Nat → Bool) (fuel : Nat) (s : WrapperState) :
    Option (StepStatus × WrapperState) :=
  match fuel with
  | 0 => some (.halted, s)
  | fuel + 1 =>
      match step? oracleEval s with
      | some (.progress, s') => runFuel? oracleEval fuel s'
      | some result => some result
      | none => none

end SKYReducerGPUWrapper
end Combinators
end LoF
end HeytingLean
