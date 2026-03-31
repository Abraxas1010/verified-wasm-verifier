import HeytingLean.HeytingVeil.MiniCMachine.Properties
import HeytingLean.HeytingVeil.ModelCheck.BFS

namespace HeytingLean
namespace HeytingVeil
namespace MiniCMachine

open HeytingLean.HeytingVeil.ModelCheck

structure BoundedDomain where
  vars : List (String × Int × Int)
  deriving Repr, DecidableEq

def BoundedDomain.rangeFor (bd : BoundedDomain) (name : String) : Int × Int :=
  match bd.vars.find? (fun t => t.1 = name) with
  | some (_, lo, hi) => (lo, hi)
  | none => (0, 0)

def valuesInRange (lo hi : Int) : List Int :=
  if hi < lo then
    []
  else
    let n : Nat := Int.toNat (hi - lo + 1)
    (List.range n).map (fun k => lo + Int.ofNat k)

private def enumerateAssignments : List (String × Int × Int) → List (List (String × Int))
  | [] => [[]]
  | (name, lo, hi) :: rest =>
      let tail := enumerateAssignments rest
      (valuesInRange lo hi).foldl (fun acc v => acc ++ tail.map (fun t => (name, v) :: t)) []

def enumerateStores (bd : BoundedDomain) : List StoreRep :=
  enumerateAssignments bd.vars

private def enumerateParamStores (params : List String) (bd : BoundedDomain) : List StoreRep :=
  let rec go : List String → List StoreRep
    | [] => [[]]
    | p :: ps =>
        let (lo, hi) := bd.rangeFor p
        let tail := go ps
        (valuesInRange lo hi).foldl (fun acc v => acc ++ tail.map (fun t => (p, v) :: t)) []
  go params

def collectContinuations : MiniC.Stmt → List MiniC.Stmt
  | .skip => [.skip]
  | .return e => [.return e]
  | .assign x rhs => [.assign x rhs, .skip]
  | .arrayUpdate name idx rhs => [.arrayUpdate name idx rhs, .skip]
  | .structUpdate name field rhs => [.structUpdate name field rhs, .skip]
  | .call fname args ret => [.call fname args ret, .skip]
  | .seq s₁ s₂ => (.seq s₁ s₂) :: (collectContinuations s₁ ++ collectContinuations s₂)
  | .if_ c t e => (.if_ c t e) :: (collectContinuations t ++ collectContinuations e)
  | .while c b => (.while c b) :: (.seq b (.while c b)) :: (collectContinuations b ++ [.skip])

def boundedMiniCMachine (fn : MiniC.Fun) (args : List Int) (bd : BoundedDomain) :
    DecidableMachine ProgramConfig :=
  let defs := ensureMainDef [] fn
  let initStores :=
    match bindParamsStore fn.params args with
    | some σ => [σ]
    | none => enumerateParamStores fn.params bd
  let conts := (collectContinuations fn.body).eraseDups
  let states :=
    (enumerateStores bd).foldl
      (fun acc σ => acc ++ conts.map (fun c => { store := σ, defs := defs, cont := c })) []
  {
    machine := {
      Init := fun s => s.cont = fn.body ∧ s.store ∈ initStores ∧ s.defs = defs
      Step := ProgramConfig.Step
    }
    states := states.eraseDups
    decInit := by
      intro s
      infer_instance
    decStep := by
      intro s t
      unfold ProgramConfig.Step
      infer_instance
  }

def checkSafety (dm : DecidableMachine ProgramConfig) (P : ProgramConfig → Prop)
    [DecidablePred P] (bound : Nat) : Bool :=
  (bfsReachable dm bound).all (fun s => decide (P s))

def firstSafetyViolation (dm : DecidableMachine ProgramConfig) (P : ProgramConfig → Prop)
    [DecidablePred P] (bound : Nat) : Option ProgramConfig :=
  (bfsReachable dm bound).find? (fun s => !decide (P s))

end MiniCMachine
end HeytingVeil
end HeytingLean
