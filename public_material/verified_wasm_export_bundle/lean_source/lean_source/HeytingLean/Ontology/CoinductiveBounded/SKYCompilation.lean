import Lean
import Mathlib.Tactic
import HeytingLean.Ontology.CoinductiveBounded.Core
import HeytingLean.CLI.SKYStageCore
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY
import HeytingLean.LoF.Combinators.SKYReducerKernel
import HeytingLean.LoF.Combinators.SKYReducerGPUWrapper
import HeytingLean.Bridge.Veselov.HybridZeckendorf.HybridNumber

/-!
# Ontology.CoinductiveBounded.SKYCompilation

Register the existing SKY compiler/runtime surfaces as ontology-facing bounded
observations over staged Lean terms.

This module stays honest about the available substrate:

- Lean terms are first lowered/staged through `CLI.SKYStageCore`,
- bounded machine images come from `Lean4LeanSKY.Machine`,
- export-facing CPU/GPU mirrors reuse `SKYReducerKernel` and
  `SKYReducerGPUWrapper`, and
- sparse support representations route through existing Hybrid Zeckendorf
  infrastructure plus a small signed-NAF encoding used only as an ontology
  support view.
-/

namespace HeytingLean.Ontology.CoinductiveBounded

abbrev StageExpr := HeytingLean.CLI.SKYStageCore.SExpr
abbrev StageInternState := HeytingLean.CLI.SKYStageCore.InternState
abbrev CpuState := HeytingLean.LoF.Combinators.SKYMachineBounded.State Unit
abbrev KernelState := HeytingLean.LoF.Combinators.SKYReducerKernel.State
abbrev WrapperState := HeytingLean.LoF.Combinators.SKYReducerGPUWrapper.WrapperState
abbrev HybridNumber := HeytingLean.Bridge.Veselov.HybridZeckendorf.HybridNumber

/-- Ontology-level registration for the concrete SKY compilation substrates. -/
inductive SkyBackendTag
  | cpuSky
  | gpuSky
  | hybridZeckendorf
  | signedNaf
  deriving DecidableEq, Repr

/-- A Lean term after the repo's existing projection-lowering and staging pass. -/
structure StagedLeanCarrier where
  staged : StageExpr
  internState : StageInternState := {}

/-- Stage a Lean term into the bounded SKY compiler plane. -/
def stageLeanExpr
    (env : Lean.Environment) (expr : Lean.Expr) : IO (Except String StagedLeanCarrier) := do
  let loweredResult ← HeytingLean.CLI.SKYStageCore.lowerProjExpr env expr
  pure <| do
    let lowered ← loweredResult
    let (staged, st) ← HeytingLean.CLI.SKYStageCore.stageExprWithState {} lowered
    pure { staged := staged, internState := st }

/-- Direct bounded SKY machine image for a staged Lean carrier. -/
def compileToCpuState? (maxNodes : Nat) (carrier : StagedLeanCarrier) :
    Option CpuState :=
  HeytingLean.LoF.LeanKernel.Lean4LeanSKY.Machine.compileExprToState? maxNodes carrier.staged

/-- Export routing only needs a dummy `Nat` oracle namespace because staged Lean terms carry no oracle payload. -/
def cpuNodeToNat :
    HeytingLean.LoF.Combinators.SKYGraph.Node Unit →
      HeytingLean.LoF.Combinators.SKYGraph.Node Nat
  | .combK => .combK
  | .combS => .combS
  | .combY => .combY
  | .app f a => .app f a
  | .oracle _ => .oracle 0

/-- Re-index the compiled SKY machine state into the `Nat` oracle namespace expected by the export kernel. -/
def cpuStateToNat (s : CpuState) :
    HeytingLean.LoF.Combinators.SKYMachineBounded.State Nat :=
  { nodes := s.nodes.map cpuNodeToNat
    focus := s.focus
    stack := s.stack }

@[simp] theorem cpuStateToNat_nodes_size (s : CpuState) :
    (cpuStateToNat s).nodes.size = s.nodes.size := by
  simp [cpuStateToNat]

/-- Export-facing CPU kernel image of the same bounded compilation. -/
def compileToKernelState? (maxNodes : Nat) (carrier : StagedLeanCarrier) :
    Option KernelState :=
  Option.map
    (fun s =>
      HeytingLean.LoF.Combinators.SKYReducerKernel.ofBoundedState maxNodes (cpuStateToNat s))
    (compileToCpuState? maxNodes carrier)

/-- GPU/C wrapper mirror of the export-facing CPU kernel image. -/
def compileToGpuWrapper? (maxNodes : Nat) (carrier : StagedLeanCarrier) :
    Option WrapperState := do
  let kernel ← compileToKernelState? maxNodes carrier
  HeytingLean.LoF.Combinators.SKYReducerGPUWrapper.ofKernelState? kernel

/-- Existing JSON export surface used by the CLI tooling. -/
def compileToStateJson
    (maxNodes fuel : Nat) (carrier : StagedLeanCarrier) : Except String Lean.Json :=
  HeytingLean.CLI.SKYStageCore.compileExprToStateJson maxNodes fuel carrier.staged

/-- Small footprint shared by the CPU and GPU-facing bounded machine routes. -/
structure SkyFootprint where
  maxNodes : Nat
  nodesUsed : Nat
  focus : Nat
  stackDepth : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Forget detailed machine nodes and keep the bounded compilation footprint. -/
def cpuFootprint (s : CpuState) (maxNodes : Nat) : SkyFootprint :=
  { maxNodes := maxNodes
    nodesUsed := s.nodes.size
    focus := s.focus
    stackDepth := s.stack.length }

/-- Footprint of the export-facing CPU kernel state. -/
def kernelFootprint (s : KernelState) : SkyFootprint :=
  { maxNodes := s.maxNodes
    nodesUsed := s.nodeCount
    focus := s.focus
    stackDepth := s.stack.length }

/-- Footprint of the GPU/C wrapper state. -/
def wrapperFootprint (s : WrapperState) : SkyFootprint :=
  { maxNodes := s.maxNodes
    nodesUsed := s.nodeCount
    focus := s.focus
    stackDepth := s.stackSize }

/-- Signed digit used by the ontology's formal support-cardinality view. -/
inductive SignedNafDigit
  | negOne
  | zero
  | posOne
  deriving DecidableEq, Repr, Inhabited

namespace SignedNafDigit

def value : SignedNafDigit → Int
  | .negOne => -1
  | .zero => 0
  | .posOne => 1

end SignedNafDigit

/-- Finite signed NAF expansion, least-significant digit first. -/
abbrev SignedNaf := List SignedNafDigit

namespace SignedNaf

def eval : SignedNaf → Int
  | [] => 0
  | d :: ds => SignedNafDigit.value d + 2 * eval ds

def ofNat : Nat → SignedNaf
  | 0 => []
  | n + 1 =>
      let m := n + 1
      if hEven : m % 2 = 0 then
        .zero :: ofNat (m / 2)
      else if hMod4 : m % 4 = 1 then
        .posOne :: ofNat (m / 2)
      else
        .negOne :: ofNat (m / 2 + 1)
termination_by n => n
decreasing_by
  all_goals
    omega

@[simp] theorem eval_nil : eval ([] : SignedNaf) = 0 := by
  rfl

@[simp] theorem eval_single_posOne : eval [.posOne] = 1 := by
  simp [eval, SignedNafDigit.value]

@[simp] theorem ofNat_zero : ofNat 0 = [] := by
  native_decide

@[simp] theorem ofNat_one : ofNat 1 = [.posOne] := by
  native_decide

@[simp] theorem ofNat_two : ofNat 2 = [.zero, .posOne] := by
  native_decide

@[simp] theorem ofNat_three : ofNat 3 = [.negOne, .zero, .posOne] := by
  native_decide

@[simp] theorem eval_ofNat_three : eval (ofNat 3) = 3 := by
  native_decide

@[simp] theorem eval_ofNat_five : eval (ofNat 5) = 5 := by
  native_decide

end SignedNaf

/-- Sparse-support SKY route through the existing Hybrid Zeckendorf surface. -/
noncomputable def compileToHybridZeckendorf? (maxNodes : Nat) (carrier : StagedLeanCarrier) :
    Option HybridNumber :=
  Option.map
    (fun s => HeytingLean.Bridge.Veselov.HybridZeckendorf.fromNat s.nodes.size)
    (compileToCpuState? maxNodes carrier)

/-- Sparse-support SKY route through the ontology's signed-NAF support view. -/
def compileToSignedNaf? (maxNodes : Nat) (carrier : StagedLeanCarrier) :
    Option SignedNaf :=
  Option.map (fun s => SignedNaf.ofNat s.nodes.size) (compileToCpuState? maxNodes carrier)

/-- Backend-tagged bounded observation route. -/
structure SkyBackendObservation (Obs : Type _) where
  backend : SkyBackendTag
  bounded : BoundedObservation StagedLeanCarrier Obs

/-- CPU bounded observation in the export-facing kernel vocabulary. -/
def cpuKernelRoute (maxNodes : Nat) :
    SkyBackendObservation (Option KernelState) where
  backend := SkyBackendTag.cpuSky
  bounded :=
    { depth := maxNodes
      observe := compileToKernelState? maxNodes
      respects_bisim := True }

/-- GPU bounded observation in the fixed-capacity wrapper vocabulary. -/
def gpuWrapperRoute (maxNodes : Nat) :
    SkyBackendObservation (Option WrapperState) where
  backend := SkyBackendTag.gpuSky
  bounded :=
    { depth := maxNodes
      observe := compileToGpuWrapper? maxNodes
      respects_bisim := True }

/-- Sparse-support bounded observation via Hybrid Zeckendorf. -/
noncomputable def hybridZeckendorfRoute (maxNodes : Nat) :
    SkyBackendObservation (Option HybridNumber) where
  backend := SkyBackendTag.hybridZeckendorf
  bounded :=
    { depth := maxNodes
      observe := compileToHybridZeckendorf? maxNodes
      respects_bisim := True }

/-- Sparse-support bounded observation via signed NAF. -/
def signedNafRoute (maxNodes : Nat) :
    SkyBackendObservation (Option SignedNaf) where
  backend := SkyBackendTag.signedNaf
  bounded :=
    { depth := maxNodes
      observe := compileToSignedNaf? maxNodes
      respects_bisim := True }

/-- The export-facing CPU kernel route preserves the direct bounded machine footprint. -/
theorem kernel_route_preserves_cpu_footprint (maxNodes : Nat) (carrier : StagedLeanCarrier) :
    Option.map kernelFootprint (compileToKernelState? maxNodes carrier) =
      Option.map (fun s => cpuFootprint s maxNodes) (compileToCpuState? maxNodes carrier) := by
  cases h : compileToCpuState? maxNodes carrier with
  | none =>
      simp [compileToKernelState?, h]
  | some s =>
      simp [compileToKernelState?, h, kernelFootprint, cpuFootprint, cpuStateToNat,
        HeytingLean.LoF.Combinators.SKYReducerKernel.nodeCount_ofBoundedState]
      constructor
      · rfl
      constructor
      · rfl
      · rfl

/-- The Zeckendorf route preserves the bounded node count semantically. -/
theorem hybridZeckendorf_route_preserves_nodesUsed (maxNodes : Nat) (carrier : StagedLeanCarrier) :
    Option.map HeytingLean.Bridge.Veselov.HybridZeckendorf.eval
        (compileToHybridZeckendorf? maxNodes carrier) =
      Option.map (fun s => s.nodes.size) (compileToCpuState? maxNodes carrier) := by
  cases h : compileToCpuState? maxNodes carrier with
  | none =>
      simp [compileToHybridZeckendorf?, h]
  | some s =>
      simp [compileToHybridZeckendorf?, h]

/-- A small staged literal used for compile-time sanity checks. -/
def stagedNatThree : StagedLeanCarrier where
  staged := (.lit (.natVal 3) : StageExpr)

/-- A small staged application used for nontrivial machine routing checks. -/
def stagedAppNat : StagedLeanCarrier where
  staged :=
    (.app
      (.lam 0 .default (.sort .zero) (.bvar 0))
      (.lit (.natVal 7)) : StageExpr)

@[simp] theorem cpuKernelRoute_backend (maxNodes : Nat) :
    (cpuKernelRoute maxNodes).backend = SkyBackendTag.cpuSky :=
  rfl

@[simp] theorem gpuWrapperRoute_backend (maxNodes : Nat) :
    (gpuWrapperRoute maxNodes).backend = SkyBackendTag.gpuSky :=
  rfl

@[simp] theorem hybridZeckendorfRoute_backend (maxNodes : Nat) :
    (hybridZeckendorfRoute maxNodes).backend = SkyBackendTag.hybridZeckendorf :=
  rfl

@[simp] theorem signedNafRoute_backend (maxNodes : Nat) :
    (signedNafRoute maxNodes).backend = SkyBackendTag.signedNaf :=
  rfl

end HeytingLean.Ontology.CoinductiveBounded
