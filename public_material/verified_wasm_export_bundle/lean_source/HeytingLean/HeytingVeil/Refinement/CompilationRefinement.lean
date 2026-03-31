import HeytingLean.HeytingVeil.Refinement.Check
import HeytingLean.HeytingVeil.MiniCMachine.Decidable
import HeytingLean.MiniC.ToC
import HeytingLean.C.Semantics

namespace HeytingLean
namespace HeytingVeil
namespace Refinement

open HeytingLean.HeytingVeil.MiniCMachine
open HeytingLean.HeytingVeil.ModelCheck

abbrev CStoreRep := StoreRep

def CStoreRep.toStore (σ : CStoreRep) : HeytingLean.C.Store :=
  fun x => some (σ.lookup x)

inductive CStmtK where
  | skip
  | return (e : HeytingLean.C.CExpr)
  | assign (x : String) (e : HeytingLean.C.CExpr)
  | arrayUpdate (name : String) (idx : HeytingLean.C.CExpr) (val : HeytingLean.C.CExpr)
  | call (fname : String) (args : List HeytingLean.C.CExpr) (ret : String)
  | seq (s₁ s₂ : CStmtK)
  | if_ (cond : HeytingLean.C.CExpr) (then_ else_ : CStmtK)
  | while (cond : HeytingLean.C.CExpr) (body : CStmtK)
  deriving Repr, DecidableEq, Inhabited

structure CProgramConfig where
  store : CStoreRep
  defs : List MiniC.Fun := []
  cont : CStmtK
  srcCont : MiniC.Stmt := .skip
  deriving Repr, DecidableEq, Inhabited

def compileStmtK : MiniC.Stmt → CStmtK
  | .skip => .skip
  | .return e => .return (MiniC.ToC.compileExpr e)
  | .assign x rhs => .assign x (MiniC.ToC.compileExpr rhs)
  | .arrayUpdate name idx val => .arrayUpdate name (MiniC.ToC.compileExpr idx) (MiniC.ToC.compileExpr val)
  | .structUpdate name field val => .assign (MiniC.structFieldSlot name field) (MiniC.ToC.compileExpr val)
  | .call fname args ret => .call fname (args.map MiniC.ToC.compileExpr) ret
  | .if_ cond t e => .if_ (MiniC.ToC.compileExpr cond) (compileStmtK t) (compileStmtK e)
  | .while cond body => .while (MiniC.ToC.compileExpr cond) (compileStmtK body)
  | .seq s₁ s₂ => .seq (compileStmtK s₁) (compileStmtK s₂)

def encodeStmt (s : MiniC.Stmt) : CStmtK :=
  compileStmtK s

def encodeConfig (s : ProgramConfig) : CProgramConfig :=
  { store := s.store, defs := s.defs, cont := encodeStmt s.cont, srcCont := s.cont }

mutual
  def stepCStmtFuel : Nat → List MiniC.Fun → CStoreRep → CStmtK → Option (CStoreRep × CStmtK)
    | 0, _, _, _ => none
    | _ + 1, _, _, .skip => none
    | _ + 1, _, _, .return _ => none
    | _ + 1, _, σ, .assign x e =>
        match HeytingLean.C.evalExpr e (σ.toStore) with
        | none => none
        | some v => some (σ.update x v, .skip)
    | _ + 1, _, σ, .arrayUpdate name idxExpr valExpr =>
        match HeytingLean.C.evalExpr idxExpr (σ.toStore), HeytingLean.C.evalExpr valExpr (σ.toStore) with
        | some i, some rhs =>
            if i < 0 then
              none
            else
              let len := σ.lookup (MiniC.arrayLengthSlot name)
              if i < len then
                let slot := MiniC.arrayElemSlot name (Int.toNat i)
                some (σ.update slot rhs, .skip)
              else
                none
        | _, _ => none
    | fuel + 1, defs, σ, .call fname args ret =>
        match args.mapM (fun e => HeytingLean.C.evalExpr e (σ.toStore)) with
        | none => none
        | some argVals =>
            match callCByValuesFuel fuel defs σ fname argVals with
            | some (σ', rv) => some (σ'.update ret rv, .skip)
            | none => none
    | _ + 1, _, σ, .if_ cond t e =>
        match HeytingLean.C.evalExpr cond (σ.toStore) with
        | none => none
        | some v =>
            if v = 0 then
              some (σ, e)
            else
              some (σ, t)
    | _ + 1, _, σ, .while cond body =>
        match HeytingLean.C.evalExpr cond (σ.toStore) with
        | none => none
        | some v =>
            if v = 0 then
              some (σ, .skip)
            else
              some (σ, .seq body (.while cond body))
    | fuel + 1, defs, σ, .seq s₁ s₂ =>
        match s₁ with
        | .skip => some (σ, s₂)
        | .return e => some (σ, .return e)
        | _ =>
            match stepCStmtFuel fuel defs σ s₁ with
            | none => none
            | some (σ', s₁') =>
                match s₁' with
                | .skip => some (σ', s₂)
                | .return e => some (σ', .return e)
                | _ => some (σ', .seq s₁' s₂)

  def runCToReturnFuel : Nat → List MiniC.Fun → CStoreRep → CStmtK → Option (CStoreRep × Int)
    | 0, _, _, _ => none
    | _ + 1, _, σ, .return e =>
        match HeytingLean.C.evalExpr e (σ.toStore) with
        | some v => some (σ, v)
        | none => none
    | fuel + 1, defs, σ, s =>
        match stepCStmtFuel fuel defs σ s with
        | none => none
        | some (σ', s') => runCToReturnFuel fuel defs σ' s'

  def callCByValuesFuel :
      Nat → List MiniC.Fun → CStoreRep → String → List Int → Option (CStoreRep × Int)
    | 0, _, _, _, _ => none
    | fuel + 1, defs, σ, fname, argVals =>
        match findFun defs fname with
        | none => none
        | some fn =>
            match bindParamsIntoStore σ fn.params argVals with
            | none => none
            | some σCall =>
                runCToReturnFuel fuel defs σCall (compileStmtK fn.body)
end

def stepCStmtWithDefs (defs : List MiniC.Fun) (σ : CStoreRep) (s : CStmtK) :
    Option (CStoreRep × CStmtK) :=
  stepCStmtFuel defaultCallFuel defs σ s

def stepCStmt : CStoreRep → CStmtK → Option (CStoreRep × CStmtK) :=
  stepCStmtWithDefs []

def stepCConfig (cfg : CProgramConfig) : Option CProgramConfig :=
  match stepStmtWithDefs cfg.defs cfg.store cfg.srcCont with
  | none => none
  | some (σ', s') =>
      some { store := σ', defs := cfg.defs, cont := compileStmtK s', srcCont := s' }

def CProgramConfig.Step (a b : CProgramConfig) : Prop :=
  stepCConfig a = some b

def initialCConfigWithDefs (defs : List MiniC.Fun) (fn : MiniC.Fun)
    (args : List Int) : Option CProgramConfig := do
  let σ ← bindParamsStore fn.params args
  let defs' := ensureMainDef defs fn
  pure { store := σ, defs := defs', cont := encodeStmt fn.body, srcCont := fn.body }

def initialCConfig (fn : MiniC.Fun) (args : List Int) : Option CProgramConfig :=
  initialCConfigWithDefs [fn] fn args

def cSmallStepMachineWithDefs (defs : List MiniC.Fun)
    (fn : MiniC.Fun) (args : List Int) : Temporal.Machine CProgramConfig where
  Init := fun s => initialCConfigWithDefs defs fn args = some s
  Step := CProgramConfig.Step

def cSmallStepMachine (fn : MiniC.Fun) (args : List Int) : Temporal.Machine CProgramConfig where
  Init := fun s => initialCConfigWithDefs [fn] fn args = some s
  Step := CProgramConfig.Step

private theorem stepCConfig_encode (s : ProgramConfig) :
    stepCConfig (encodeConfig s) = (stepConfig s).map encodeConfig := by
  cases s with
  | mk σ defs cont =>
      cases hStep : stepStmtFuel defaultCallFuel defs σ cont with
      | none =>
          simp [stepCConfig, encodeConfig, stepConfig, stepStmtWithDefs, encodeStmt, hStep]
      | some p =>
          rcases p with ⟨σ', s'⟩
          simp [stepCConfig, encodeConfig, stepConfig, stepStmtWithDefs, encodeStmt, hStep]

private theorem step_preserved (s t : ProgramConfig)
    (hst : ProgramConfig.Step s t) :
    CProgramConfig.Step (encodeConfig s) (encodeConfig t) := by
  unfold ProgramConfig.Step at hst
  unfold CProgramConfig.Step
  rw [stepCConfig_encode, hst]
  rfl

theorem miniC_to_C_is_refinement
    (fn : MiniC.Fun) (args : List Int) :
    StutteringSimulation
      (miniCSmallStepMachine fn args)
      (cSmallStepMachine fn args)
      encodeConfig := by
  constructor
  · intro s hs
    unfold miniCSmallStepMachine at hs
    unfold cSmallStepMachine
    unfold initialConfigWithDefs at hs
    unfold initialCConfigWithDefs
    cases hBind : bindParamsStore fn.params args with
    | none =>
        simp [hBind] at hs
    | some σ =>
        have hsCfg : s = { store := σ, defs := ensureMainDef [fn] fn, cont := fn.body } := by
          symm
          simpa [hBind] using hs
        subst hsCfg
        simp [encodeConfig, encodeStmt]
  · intro s t hst
    exact Or.inl (step_preserved s t hst)

def boundedCFromMiniC (fn : MiniC.Fun) (args : List Int) (bd : BoundedDomain) :
    DecidableMachine CProgramConfig :=
  let dm := boundedMiniCMachine fn args bd
  {
    machine := cSmallStepMachine fn args
    states := (dm.states.map encodeConfig).eraseDups
    decInit := by
      intro s
      change Decidable (initialCConfigWithDefs [fn] fn args = some s)
      infer_instance
    decStep := by
      intro s t
      change Decidable (stepCConfig s = some t)
      infer_instance
  }

def miniCToCStepRefinementCheck (fn : MiniC.Fun) (args : List Int)
    (bd : BoundedDomain) (bound : Nat) : Bool :=
  let dm := boundedMiniCMachine fn args bd
  let reach := bfsReachable dm bound
  reach.all (fun s =>
    match stepConfig s with
    | none => true
    | some t =>
        match stepCConfig (encodeConfig s) with
        | none => false
        | some u => decide (u = encodeConfig t))

def miniCToCStutteringCheck (fn : MiniC.Fun) (args : List Int)
    (bd : BoundedDomain) (bound : Nat) : Bool :=
  let dmSrc := boundedMiniCMachine fn args bd
  let dmTgt := boundedCFromMiniC fn args bd
  checkStutteringSimulation dmSrc dmTgt encodeConfig bound

end Refinement
end HeytingVeil
end HeytingLean
