import HeytingLean.LoF.Combinators.SKYMachineBounded

/-!
# SKYReducerKernel

An export-facing first-order reducer kernel for the bounded SKY machine.

`SKYMachineBounded` remains the richer Lean reference machine. This module
repackages the operational core into a flat, explicit state shape that is
suited to direct lowering into LeanCP-owned C.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace SKYReducerKernel

open SKYGraph
open SKYMachineBounded

/-- Flat node tags used by the export-facing kernel. -/
inductive NodeTag where
  | app
  | combK
  | combS
  | combY
  | oracle
  deriving DecidableEq, Repr, Inhabited

namespace NodeTag

def code : NodeTag → Int
  | .app => 0
  | .combK => 1
  | .combS => 2
  | .combY => 3
  | .oracle => 4

def ofCode? : Int → Option NodeTag
  | 0 => some .app
  | 1 => some .combK
  | 2 => some .combS
  | 3 => some .combY
  | 4 => some .oracle
  | _ => none

@[simp] theorem ofCode?_code (tag : NodeTag) : ofCode? tag.code = some tag := by
  cases tag <;> rfl

end NodeTag

/-- A decoded node view assembled from the parallel kernel arrays. -/
structure NodeView where
  tag : NodeTag
  lhs : Nat := 0
  rhs : Nat := 0
  oracleRef : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Explicit kernel state for LeanCP lowering.

The active stack uses the same convention as `SKYMachineBounded`: the list head
is the top of the stack. The parallel arrays are the source-of-truth node store.
-/
structure State where
  tags : Array Int
  lhs : Array Nat
  rhs : Array Nat
  oracleRefs : Array Nat
  focus : Nat
  stack : List Nat
  maxNodes : Nat
  deriving DecidableEq, Repr, Inhabited

namespace State

def nodeCount (s : State) : Nat :=
  s.tags.size

/--
`WellFormed` tracks heap-segment alignment and heap capacity only.

We intentionally do not require `s.stack.length ≤ s.maxNodes` here. The `.app`
kernel step pushes `rhs` onto the traversal stack, so legitimate deep traversals
can outgrow the heap-node budget even when the heap itself remains bounded and
the step relation stays correct. Any external stack-budget invariant must be
tracked separately from this kernel-local notion of well-formedness.
-/
def WellFormed (s : State) : Prop :=
  s.lhs.size = s.nodeCount ∧
  s.rhs.size = s.nodeCount ∧
  s.oracleRefs.size = s.nodeCount ∧
  s.nodeCount ≤ s.maxNodes ∧
  True

def node? (s : State) (i : Nat) : Option NodeView := do
  let tagCode ← s.tags[i]?
  let tag ← NodeTag.ofCode? tagCode
  let lhs ← s.lhs[i]?
  let rhs ← s.rhs[i]?
  let oracleRef ← s.oracleRefs[i]?
  pure { tag := tag, lhs := lhs, rhs := rhs, oracleRef := oracleRef }

def pushNode (s : State) (tag : NodeTag) (lhs rhs oracleRef : Nat) :
    Option (State × Nat) :=
  if s.nodeCount < s.maxNodes then
    let id := s.nodeCount
    some
      ( { s with
          tags := s.tags.push tag.code
          lhs := s.lhs.push lhs
          rhs := s.rhs.push rhs
          oracleRefs := s.oracleRefs.push oracleRef }
      , id)
  else
    none

theorem pushNode_wellFormed
    {s s' : State} {id : Nat} {tag : NodeTag} {lhs rhs oracleRef : Nat}
    (hwf : s.WellFormed)
    (hpush : s.pushNode tag lhs rhs oracleRef = some (s', id)) :
    s'.WellFormed := by
  rcases hwf with ⟨hlhs, hrhs, hrefs, hnodes, htrue⟩
  by_cases hcap : s.nodeCount < s.maxNodes
  · simp [State.pushNode, hcap] at hpush
    rcases hpush with ⟨rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, trivial⟩
    · simp [State.nodeCount, hlhs]
    · simp [State.nodeCount, hrhs]
    · simp [State.nodeCount, hrefs]
    · simpa [State.nodeCount] using Nat.succ_le_of_lt hcap
  · simp [State.pushNode, hcap] at hpush

theorem setFocusStack_wellFormed
    {s : State} (hwf : s.WellFormed) (focus : Nat) (stack : List Nat) :
    ({ s with focus := focus, stack := stack }).WellFormed := by
  simpa [State.WellFormed, State.nodeCount] using hwf

end State

/-- Kernel step status used both by the pure kernel and the lowered LeanCP
surface. -/
inductive StepStatus where
  | progress
  | halted
  | outOfHeap
  deriving DecidableEq, Repr, Inhabited

namespace StepStatus

def code : StepStatus → Int
  | .progress => 1
  | .halted => 0
  | .outOfHeap => 2

def ofCode? : Int → Option StepStatus
  | 1 => some .progress
  | 0 => some .halted
  | 2 => some .outOfHeap
  | _ => none

end StepStatus

structure StepResult where
  status : StepStatus
  state : State
  deriving DecidableEq, Repr, Inhabited

private def mkResult (status : StepStatus) (state : State) : StepResult :=
  { status := status, state := state }

def step (oracleEval : Nat → Bool) (s : State) : StepResult :=
  match s.node? s.focus with
  | some { tag := .app, lhs := f, rhs := a, .. } =>
      mkResult .progress { s with focus := f, stack := a :: s.stack }
  | some { tag := .combK, .. } =>
      match s.stack with
      | x :: _y :: rest => mkResult .progress { s with focus := x, stack := rest }
      | _ => mkResult .halted s
  | some { tag := .combS, .. } =>
      match s.stack with
      | x :: y :: z :: rest =>
          match s.pushNode .app x z 0 with
          | none => mkResult .outOfHeap s
          | some (s1, xz) =>
              match s1.pushNode .app y z 0 with
              | none => mkResult .outOfHeap s
              | some (s2, yz) =>
                  match s2.pushNode .app xz yz 0 with
                  | none => mkResult .outOfHeap s
                  | some (s3, out) =>
                      mkResult .progress { s3 with focus := out, stack := rest }
      | _ => mkResult .halted s
  | some { tag := .combY, .. } =>
      match s.stack with
      | f :: rest =>
          match s.pushNode .app s.focus f 0 with
          | none => mkResult .outOfHeap s
          | some (s1, self) =>
              match s1.pushNode .app f self 0 with
              | none => mkResult .outOfHeap s
              | some (s2, out) =>
                  mkResult .progress { s2 with focus := out, stack := rest }
      | _ => mkResult .halted s
  | some { tag := .oracle, oracleRef := ref, .. } =>
      match s.stack with
      | t :: f :: rest =>
          let next := if oracleEval ref then t else f
          mkResult .progress { s with focus := next, stack := rest }
      | _ => mkResult .halted s
  | none => mkResult .halted s

def runFuel (oracleEval : Nat → Bool) (fuel : Nat) (s : State) : StepResult :=
  match fuel with
  | 0 => mkResult .halted s
  | fuel + 1 =>
      let r := step oracleEval s
      match r.status with
      | .progress => runFuel oracleEval fuel r.state
      | .halted => r
      | .outOfHeap => r

theorem step_wellFormed
    (oracleEval : Nat → Bool) {s : State}
    (hwf : s.WellFormed) :
    (step oracleEval s).state.WellFormed := by
  unfold step
  cases hnode : s.node? s.focus with
  | none =>
      simpa [hnode]
  | some node =>
      cases node with
      | mk tag lhs rhs oracleRef =>
          cases tag with
          | app =>
              simpa [hnode] using State.setFocusStack_wellFormed hwf lhs (rhs :: s.stack)
          | combK =>
              cases hs : s.stack with
              | nil =>
                  simpa [hs] using hwf
              | cons x xs =>
                cases hs' : xs with
                | nil =>
                    simpa [hs, hs'] using hwf
                | cons y rest =>
                  simpa [hnode, hs, hs'] using State.setFocusStack_wellFormed hwf x rest
          | combS =>
              cases hs : s.stack with
              | nil =>
                  simpa [hs] using hwf
              | cons x xs =>
                cases hs' : xs with
                | nil =>
                    simpa [hs, hs'] using hwf
                | cons y rest =>
                  cases hs'' : rest with
                  | nil =>
                      simpa [hs, hs', hs''] using hwf
                  | cons z rest' =>
                    cases hpush0 : s.pushNode .app x z 0 with
                    | none =>
                        simpa [hs, hs', hs'', hpush0] using hwf
                    | some p0 =>
                        rcases p0 with ⟨s1, xz⟩
                        have hwf1 : s1.WellFormed := State.pushNode_wellFormed hwf hpush0
                        cases hpush1 : s1.pushNode .app y z 0 with
                        | none =>
                            simpa [hs, hs', hs'', hpush0, hpush1] using hwf
                        | some p1 =>
                            rcases p1 with ⟨s2, yz⟩
                            have hwf2 : s2.WellFormed := State.pushNode_wellFormed hwf1 hpush1
                            cases hpush2 : s2.pushNode .app xz yz 0 with
                            | none =>
                                simpa [hs, hs', hs'', hpush0, hpush1, hpush2] using hwf
                            | some p2 =>
                                rcases p2 with ⟨s3, out⟩
                                have hwf3 : s3.WellFormed := State.pushNode_wellFormed hwf2 hpush2
                                simpa [hnode, hs, hs', hs'', hpush0, hpush1, hpush2] using
                                  State.setFocusStack_wellFormed hwf3 out rest'
          | combY =>
              cases hs : s.stack with
              | nil =>
                  simpa [hs] using hwf
              | cons f rest =>
                cases hpush0 : s.pushNode .app s.focus f 0 with
                | none =>
                    simpa [hs, hpush0] using hwf
                | some p0 =>
                    rcases p0 with ⟨s1, self⟩
                    have hwf1 : s1.WellFormed := State.pushNode_wellFormed hwf hpush0
                    cases hpush1 : s1.pushNode .app f self 0 with
                    | none =>
                        simpa [hs, hpush0, hpush1] using hwf
                    | some p1 =>
                        rcases p1 with ⟨s2, out⟩
                        have hwf2 : s2.WellFormed := State.pushNode_wellFormed hwf1 hpush1
                        simpa [hnode, hs, hpush0, hpush1] using
                          State.setFocusStack_wellFormed hwf2 out rest
          | oracle =>
              cases hs : s.stack with
              | nil =>
                  simpa [hs] using hwf
              | cons t xs =>
                cases hs' : xs with
                | nil =>
                    simpa [hs, hs'] using hwf
                | cons f rest =>
                  simpa [hnode, hs, hs'] using
                    State.setFocusStack_wellFormed hwf (if oracleEval oracleRef then t else f) rest

def ofGraphNode : SKYGraph.Node Nat → NodeView
  | .combK => { tag := .combK }
  | .combS => { tag := .combS }
  | .combY => { tag := .combY }
  | .app f a => { tag := .app, lhs := f, rhs := a }
  | .oracle ref => { tag := .oracle, oracleRef := ref }

def ofBoundedState (maxNodes : Nat) (s : SKYMachineBounded.State Nat) : State :=
  { tags := s.nodes.map (fun node => (ofGraphNode node).tag.code)
    lhs := s.nodes.map (fun node => (ofGraphNode node).lhs)
    rhs := s.nodes.map (fun node => (ofGraphNode node).rhs)
    oracleRefs := s.nodes.map (fun node => (ofGraphNode node).oracleRef)
    focus := s.focus
    stack := s.stack
    maxNodes := maxNodes }

def toGraphNode? (view : NodeView) : Option (SKYGraph.Node Nat) :=
  match view.tag with
  | .combK => some .combK
  | .combS => some .combS
  | .combY => some .combY
  | .app => some (.app view.lhs view.rhs)
  | .oracle => some (.oracle view.oracleRef)

private def decodeNodesAux (s : State) (i : Nat) (acc : Array (SKYGraph.Node Nat)) :
    Option (Array (SKYGraph.Node Nat)) :=
  if _h : i < s.nodeCount then
    match s.node? i with
    | some view =>
        match toGraphNode? view with
        | some node => decodeNodesAux s (i + 1) (acc.push node)
        | none => none
    | none => none
  else
    some acc
termination_by s.nodeCount - i

def toBoundedState? (s : State) : Option (SKYMachineBounded.State Nat) := do
  let nodes ← decodeNodesAux s 0 #[]
  pure { nodes := nodes, focus := s.focus, stack := s.stack }

def ofBoundedStepResult (maxNodes : Nat) : SKYMachineBounded.State.StepResult Nat → StepResult
  | .progress s => mkResult .progress (ofBoundedState maxNodes s)
  | .halted s => mkResult .halted (ofBoundedState maxNodes s)
  | .outOfHeap s => mkResult .outOfHeap (ofBoundedState maxNodes s)

@[simp] theorem nodeCount_ofBoundedState (maxNodes : Nat) (s : SKYMachineBounded.State Nat) :
    (ofBoundedState maxNodes s).nodeCount = s.nodes.size := by
  simp [State.nodeCount, ofBoundedState]

@[simp] theorem focus_ofBoundedState (maxNodes : Nat) (s : SKYMachineBounded.State Nat) :
    (ofBoundedState maxNodes s).focus = s.focus := rfl

@[simp] theorem stack_ofBoundedState (maxNodes : Nat) (s : SKYMachineBounded.State Nat) :
    (ofBoundedState maxNodes s).stack = s.stack := rfl

@[simp] theorem maxNodes_ofBoundedState (maxNodes : Nat) (s : SKYMachineBounded.State Nat) :
    (ofBoundedState maxNodes s).maxNodes = maxNodes := rfl

@[simp] theorem wellFormed_ofBoundedState (maxNodes : Nat) (s : SKYMachineBounded.State Nat)
    (hmax : s.nodes.size ≤ maxNodes) :
    (ofBoundedState maxNodes s).WellFormed := by
  simp [State.WellFormed, State.nodeCount, ofBoundedState, hmax]

@[simp] theorem node?_ofBoundedState (maxNodes : Nat) (s : SKYMachineBounded.State Nat) (i : Nat) :
    (ofBoundedState maxNodes s).node? i = Option.map ofGraphNode (s.node? i) := by
  cases hnode : s.nodes[i]? <;> simp [State.node?, ofBoundedState, SKYMachineBounded.State.node?, hnode, Option.map]

theorem pushNode_ofBoundedState (maxNodes : Nat) (s : SKYMachineBounded.State Nat)
    (node : SKYGraph.Node Nat) :
    let view := ofGraphNode node
    State.pushNode (ofBoundedState maxNodes s) view.tag view.lhs view.rhs view.oracleRef =
      Option.map (fun p => (ofBoundedState maxNodes p.1, p.2))
        (s.pushNode maxNodes node) := by
  by_cases hcap : s.nodes.size < maxNodes
  · simp [State.pushNode, SKYMachineBounded.State.pushNode, State.nodeCount, ofBoundedState, hcap]
  · simp [State.pushNode, SKYMachineBounded.State.pushNode, State.nodeCount, ofBoundedState, hcap]

theorem step_ofBoundedState (oracleEval : Nat → Bool) (maxNodes : Nat)
    (s : SKYMachineBounded.State Nat) :
    ofBoundedStepResult maxNodes (SKYMachineBounded.State.step oracleEval maxNodes s) =
      step oracleEval (ofBoundedState maxNodes s) := by
  unfold ofBoundedStepResult mkResult
  unfold SKYMachineBounded.State.step step
  rw [node?_ofBoundedState]
  cases hnode : s.node? s.focus with
  | none =>
      simp [hnode, ofGraphNode, ofBoundedState, mkResult]
  | some node =>
      cases node with
      | app f a =>
          simp [hnode, ofGraphNode, ofBoundedState, mkResult]
      | combK =>
          cases hs : s.stack with
          | nil =>
              simp [hnode, hs, ofGraphNode, ofBoundedState, mkResult]
          | cons x xs =>
              cases hs' : xs with
              | nil =>
                  simp [hnode, hs, hs', ofGraphNode, ofBoundedState, mkResult]
              | cons y rest =>
                  simp [hnode, hs, hs', ofGraphNode, ofBoundedState, mkResult]
      | combS =>
          cases hs : s.stack with
          | nil =>
              simp [ofBoundedState, hnode, hs, ofGraphNode, mkResult]
          | cons x xs =>
              cases hs' : xs with
              | nil =>
                  simp [ofBoundedState, hnode, hs, hs', ofGraphNode, mkResult]
              | cons y rest =>
                  cases hs'' : rest with
                  | nil =>
                      simp [ofBoundedState, hnode, hs, hs', hs'', ofGraphNode, mkResult]
                  | cons z rest' =>
                      cases hpush0 : s.pushNode maxNodes (.app x z) with
                      | none =>
                          have hpush0' :
                              State.pushNode (ofBoundedState maxNodes s) .app x z 0 = none := by
                            simpa [hpush0] using
                              (pushNode_ofBoundedState maxNodes s (.app x z))
                          simp [hnode, hs, hs', hs'', hpush0, hpush0', ofGraphNode, mkResult]
                      | some p0 =>
                          rcases p0 with ⟨s1, xz⟩
                          have hpush0' :
                              State.pushNode (ofBoundedState maxNodes s) .app x z 0 =
                                some (ofBoundedState maxNodes s1, xz) := by
                            simpa [hpush0] using
                              (pushNode_ofBoundedState maxNodes s (.app x z))
                          cases hpush1 : s1.pushNode maxNodes (.app y z) with
                          | none =>
                              have hpush1' :
                                  State.pushNode (ofBoundedState maxNodes s1) .app y z 0 = none := by
                                simpa [hpush1] using
                                  (pushNode_ofBoundedState maxNodes s1 (.app y z))
                              simp [hnode, hs, hs', hs'', hpush0, hpush0', hpush1, hpush1',
                                ofGraphNode, mkResult]
                          | some p1 =>
                              rcases p1 with ⟨s2, yz⟩
                              have hpush1' :
                                  State.pushNode (ofBoundedState maxNodes s1) .app y z 0 =
                                    some (ofBoundedState maxNodes s2, yz) := by
                                simpa [hpush1] using
                                  (pushNode_ofBoundedState maxNodes s1 (.app y z))
                              cases hpush2 : s2.pushNode maxNodes (.app xz yz) with
                              | none =>
                                  have hpush2' :
                                      State.pushNode (ofBoundedState maxNodes s2) .app xz yz 0 = none := by
                                    simpa [hpush2] using
                                      (pushNode_ofBoundedState maxNodes s2 (.app xz yz))
                                  have hresult :
                                      ({ status := StepStatus.outOfHeap
                                         state := ({ (ofBoundedState maxNodes s) with stack := x :: y :: z :: rest' } : State) } :
                                        StepResult) =
                                        { status := StepStatus.outOfHeap, state := ofBoundedState maxNodes s } := by
                                    have hstate :
                                        ({ (ofBoundedState maxNodes s) with stack := x :: y :: z :: rest' } : State) =
                                          ofBoundedState maxNodes s := by
                                      cases s with
                                      | mk nodes focus stack =>
                                          simp [ofBoundedState] at hs hs' hs'' ⊢
                                          cases hs
                                          cases hs'
                                          cases hs''
                                          rfl
                                    simpa [hstate]
                                  simpa [hnode, hs, hs', hs'', hpush0, hpush0', hpush1, hpush1',
                                    hpush2, hpush2', ofGraphNode, mkResult] using hresult
                              | some p2 =>
                                  rcases p2 with ⟨s3, out⟩
                                  have hpush2' :
                                      State.pushNode (ofBoundedState maxNodes s2) .app xz yz 0 =
                                        some (ofBoundedState maxNodes s3, out) := by
                                    simpa [hpush2] using
                                      (pushNode_ofBoundedState maxNodes s2 (.app xz yz))
                                  have hstate :
                                      ofBoundedState maxNodes
                                          ({ nodes := s3.nodes, focus := out, stack := rest' } : SKYMachineBounded.State Nat) =
                                        ({ (ofBoundedState maxNodes s3) with focus := out, stack := rest' } : State) := by
                                    rfl
                                  simpa [hnode, hs, hs', hs'', hpush0, hpush0', hpush1, hpush1',
                                    hpush2, hpush2', ofGraphNode, mkResult] using hstate
      | combY =>
          cases hs : s.stack with
          | nil =>
              simp [hnode, hs, ofGraphNode, ofBoundedState, mkResult]
          | cons f rest =>
              cases hpush0 : s.pushNode maxNodes (.app s.focus f) with
              | none =>
                  have hpush0' :
                      State.pushNode (ofBoundedState maxNodes s) .app s.focus f 0 = none := by
                    simpa [hpush0] using
                      (pushNode_ofBoundedState maxNodes s (.app s.focus f))
                  simp [hnode, hs, hpush0, hpush0', ofGraphNode, mkResult]
              | some p0 =>
                  rcases p0 with ⟨s1, self⟩
                  have hpush0' :
                      State.pushNode (ofBoundedState maxNodes s) .app s.focus f 0 =
                        some (ofBoundedState maxNodes s1, self) := by
                    simpa [hpush0] using
                      (pushNode_ofBoundedState maxNodes s (.app s.focus f))
                  cases hpush1 : s1.pushNode maxNodes (.app f self) with
                  | none =>
                      have hpush1' :
                          State.pushNode (ofBoundedState maxNodes s1) .app f self 0 = none := by
                        simpa [hpush1] using
                          (pushNode_ofBoundedState maxNodes s1 (.app f self))
                      have hresult :
                          ({ status := StepStatus.outOfHeap
                             state := ({ (ofBoundedState maxNodes s) with stack := f :: rest } : State) } : StepResult) =
                            { status := StepStatus.outOfHeap, state := ofBoundedState maxNodes s } := by
                        have hstate :
                            ({ (ofBoundedState maxNodes s) with stack := f :: rest } : State) =
                              ofBoundedState maxNodes s := by
                          cases s with
                          | mk nodes focus stack =>
                              simp [ofBoundedState] at hs ⊢
                              cases hs
                              rfl
                        simpa [hstate]
                      simpa [hnode, hs, hpush0, hpush0', hpush1, hpush1', ofGraphNode, mkResult] using hresult
                  | some p1 =>
                      rcases p1 with ⟨s2, out⟩
                      have hpush1' :
                          State.pushNode (ofBoundedState maxNodes s1) .app f self 0 =
                            some (ofBoundedState maxNodes s2, out) := by
                        simpa [hpush1] using
                          (pushNode_ofBoundedState maxNodes s1 (.app f self))
                      have hstate :
                          ofBoundedState maxNodes { nodes := s2.nodes, focus := out, stack := rest } =
                            { tags := (ofBoundedState maxNodes s2).tags, lhs := (ofBoundedState maxNodes s2).lhs,
                              rhs := (ofBoundedState maxNodes s2).rhs,
                              oracleRefs := (ofBoundedState maxNodes s2).oracleRefs,
                              focus := out, stack := rest, maxNodes := maxNodes } := by
                        rfl
                      simpa [hnode, hs, hpush0, hpush0', hpush1, hpush1', ofGraphNode, mkResult] using hstate
      | oracle ref =>
          cases hs : s.stack with
          | nil =>
              simp [hnode, hs, ofGraphNode, ofBoundedState, mkResult]
          | cons t xs =>
              cases hs' : xs with
              | nil =>
                  simp [hnode, hs, hs', ofGraphNode, ofBoundedState, mkResult]
              | cons f rest =>
                  simp [hnode, hs, hs', ofGraphNode, ofBoundedState, mkResult]

theorem runFuel_ofBoundedState (oracleEval : Nat → Bool) (maxNodes fuel : Nat)
    (s : SKYMachineBounded.State Nat) :
    ofBoundedStepResult maxNodes (SKYMachineBounded.State.runFuel oracleEval maxNodes fuel s) =
      runFuel oracleEval fuel (ofBoundedState maxNodes s) := by
  induction fuel generalizing s with
  | zero =>
      simp [SKYMachineBounded.State.runFuel, runFuel, ofBoundedStepResult, mkResult]
  | succ fuel ih =>
      cases hstep : SKYMachineBounded.State.step oracleEval maxNodes s with
      | progress s' =>
          have hbridge := step_ofBoundedState oracleEval maxNodes s
          rw [hstep] at hbridge
          simp [SKYMachineBounded.State.runFuel, runFuel, hstep]
          rw [← hbridge]
          exact ih s'
      | halted s' =>
          have hbridge := step_ofBoundedState oracleEval maxNodes s
          rw [hstep] at hbridge
          simp [SKYMachineBounded.State.runFuel, runFuel, hstep]
          rw [← hbridge]
          simp [ofBoundedStepResult, mkResult]
      | outOfHeap s' =>
          have hbridge := step_ofBoundedState oracleEval maxNodes s
          rw [hstep] at hbridge
          simp [SKYMachineBounded.State.runFuel, runFuel, hstep]
          rw [← hbridge]
          simp [ofBoundedStepResult, mkResult]

end SKYReducerKernel
end Combinators
end LoF
end HeytingLean
