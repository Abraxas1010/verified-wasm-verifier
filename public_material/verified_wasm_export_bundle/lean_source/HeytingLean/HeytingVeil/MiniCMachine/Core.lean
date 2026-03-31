import HeytingLean.MiniC.Semantics
import HeytingLean.HeytingVeil.Temporal.Core

namespace HeytingLean
namespace HeytingVeil
namespace MiniCMachine

open HeytingLean.MiniC
open HeytingLean.HeytingVeil.Temporal

abbrev StoreRep := List (String × Int)

def StoreRep.lookup (σ : StoreRep) (x : String) : Int :=
  match σ.find? (fun kv => kv.1 = x) with
  | some kv => kv.2
  | none => 0

def StoreRep.update : StoreRep → String → Int → StoreRep
  | [], x, v => [(x, v)]
  | (k, w) :: rest, x, v =>
      if k = x then
        (x, v) :: rest
      else
        (k, w) :: StoreRep.update rest x v

def StoreRep.toTotalStore (σ : StoreRep) : MiniC.TotalStore :=
  fun x => σ.lookup x

def bindParamsStore : List String → List Int → Option StoreRep
  | [], [] => some []
  | p :: ps, v :: vs => do
      let tail ← bindParamsStore ps vs
      pure ((p, v) :: tail)
  | _, _ => none

def bindParamsIntoStore : StoreRep → List String → List Int → Option StoreRep
  | σ, [], [] => some σ
  | σ, p :: ps, v :: vs => bindParamsIntoStore (σ.update p v) ps vs
  | _, _, _ => none

def findFun (defs : List MiniC.Fun) (fname : String) : Option MiniC.Fun :=
  defs.find? (fun fn => fn.name = fname)

def defaultCallFuel : Nat := 64

structure ProgramConfig where
  store : StoreRep
  defs : List MiniC.Fun := []
  cont : MiniC.Stmt
  deriving Repr, DecidableEq

def ProgramConfig.toTotalStore (cfg : ProgramConfig) : MiniC.TotalStore :=
  cfg.store.toTotalStore

mutual
  def stepStmtFuel : Nat → List MiniC.Fun → StoreRep → MiniC.Stmt → Option (StoreRep × MiniC.Stmt)
    | 0, _, _, _ => none
    | _ + 1, _, _, .skip => none
    | _ + 1, _, _, .return _ => none
    | _ + 1, _, σ, .assign x rhs =>
        let v := rhs.eval (σ.toTotalStore)
        some (σ.update x v, .skip)
    | _ + 1, _, σ, .arrayUpdate name idxExpr valExpr =>
        let i := idxExpr.eval (σ.toTotalStore)
        let rhs := valExpr.eval (σ.toTotalStore)
        if i < 0 then
          none
        else
          let len := σ.lookup (MiniC.arrayLengthSlot name)
          if i < len then
            let slot := MiniC.arrayElemSlot name (Int.toNat i)
            some (σ.update slot rhs, .skip)
          else
            none
    | _ + 1, _, σ, .structUpdate name field rhs =>
        let v := rhs.eval (σ.toTotalStore)
        some (σ.update (MiniC.structFieldSlot name field) v, .skip)
    | fuel + 1, defs, σ, .call fname args ret =>
        let argVals := args.map (fun e => e.eval (σ.toTotalStore))
        match callByValuesFuel fuel defs σ fname argVals with
        | some (σ', rv) => some (σ'.update ret rv, .skip)
        | none => none
    | _ + 1, _, σ, .if_ cond t e =>
        if cond.eval (σ.toTotalStore) ≠ 0 then
          some (σ, t)
        else
          some (σ, e)
    | _ + 1, _, σ, .while cond body =>
        if cond.eval (σ.toTotalStore) = 0 then
          some (σ, .skip)
        else
          some (σ, .seq body (.while cond body))
    | fuel + 1, defs, σ, .seq s₁ s₂ =>
        match s₁ with
        | .skip => some (σ, s₂)
        | .return e => some (σ, .return e)
        | _ =>
            match stepStmtFuel fuel defs σ s₁ with
            | none => none
            | some (σ', s₁') =>
                match s₁' with
                | .skip => some (σ', s₂)
                | .return e => some (σ', .return e)
                | _ => some (σ', .seq s₁' s₂)

  def runToReturnFuel : Nat → List MiniC.Fun → StoreRep → MiniC.Stmt → Option (StoreRep × Int)
    | 0, _, _, _ => none
    | _ + 1, _, σ, .return e => some (σ, e.eval (σ.toTotalStore))
    | fuel + 1, defs, σ, s =>
        match stepStmtFuel fuel defs σ s with
        | none => none
        | some (σ', s') => runToReturnFuel fuel defs σ' s'

  def callByValuesFuel : Nat → List MiniC.Fun → StoreRep → String → List Int → Option (StoreRep × Int)
    | 0, _, _, _, _ => none
    | fuel + 1, defs, σ, fname, argVals =>
        match findFun defs fname with
        | none => none
        | some fn =>
            match bindParamsIntoStore σ fn.params argVals with
            | none => none
            | some σCall => runToReturnFuel fuel defs σCall fn.body
end

def stepStmtWithDefs (defs : List MiniC.Fun) (σ : StoreRep) (s : MiniC.Stmt) :
    Option (StoreRep × MiniC.Stmt) :=
  stepStmtFuel defaultCallFuel defs σ s

def stepStmt : StoreRep → MiniC.Stmt → Option (StoreRep × MiniC.Stmt) :=
  stepStmtWithDefs []

def stepConfig (cfg : ProgramConfig) : Option ProgramConfig :=
  match stepStmtWithDefs cfg.defs cfg.store cfg.cont with
  | none => none
  | some (σ', s') => some { store := σ', defs := cfg.defs, cont := s' }

def ProgramConfig.Step (a b : ProgramConfig) : Prop :=
  stepConfig a = some b

def ensureMainDef (defs : List MiniC.Fun) (fn : MiniC.Fun) : List MiniC.Fun :=
  if defs.any (fun g => g.name = fn.name) then defs else fn :: defs

def initialConfigWithDefs (defs : List MiniC.Fun) (fn : MiniC.Fun)
    (args : List Int) : Option ProgramConfig := do
  let σ ← bindParamsStore fn.params args
  let defs' := ensureMainDef defs fn
  pure { store := σ, defs := defs', cont := fn.body }

def initialConfig (fn : MiniC.Fun) (args : List Int) : Option ProgramConfig :=
  initialConfigWithDefs [fn] fn args

def initialConfigProgram (prog : MiniC.Program) (args : List Int) : Option ProgramConfig :=
  initialConfigWithDefs (prog.main :: prog.defs) prog.main args

def miniCSmallStepMachineWithDefs (defs : List MiniC.Fun)
    (fn : MiniC.Fun) (args : List Int) : Machine ProgramConfig where
  Init := fun s => initialConfigWithDefs defs fn args = some s
  Step := ProgramConfig.Step

def miniCSmallStepMachine (fn : MiniC.Fun) (args : List Int) : Machine ProgramConfig where
  Init := fun s => initialConfigWithDefs [fn] fn args = some s
  Step := ProgramConfig.Step

def miniCFunToMachineWithDefs (defs : List MiniC.Fun)
    (fn : MiniC.Fun) (args : List Int) : Machine StoreRep where
  Init := fun σ => ∃ cfg, initialConfigWithDefs defs fn args = some cfg ∧ cfg.store = σ
  Step := fun σ τ =>
    ∃ c c', c.store = σ ∧ c'.store = τ ∧ ProgramConfig.Step c c'

def miniCFunToMachine (fn : MiniC.Fun) (args : List Int) : Machine StoreRep where
  Init := fun σ => ∃ cfg, initialConfigWithDefs [fn] fn args = some cfg ∧ cfg.store = σ
  Step := fun σ τ =>
    ∃ c c', c.store = σ ∧ c'.store = τ ∧ ProgramConfig.Step c c'

def runConfigFuel : Nat → ProgramConfig → ProgramConfig
  | 0, cfg => cfg
  | n + 1, cfg =>
      match stepConfig cfg with
      | none => cfg
      | some cfg' => runConfigFuel n cfg'

end MiniCMachine
end HeytingVeil
end HeytingLean
