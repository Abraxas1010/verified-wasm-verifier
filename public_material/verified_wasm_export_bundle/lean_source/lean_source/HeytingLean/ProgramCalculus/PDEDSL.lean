import HeytingLean.ProgramCalculus.Core
import HeytingLean.PDE.Core

namespace HeytingLean
namespace ProgramCalculus

structure HeatParams where
  alphaNumerator : Nat
  alphaDenominator : Nat
  deriving Repr, DecidableEq, Inhabited

structure HeatState where
  values : List Int
  deriving Repr, DecidableEq, Inhabited

inductive PDEProgram where
  | identity
  | heat1DStep (params : HeatParams)
  deriving Repr, DecidableEq, Inhabited

namespace PDEProgram

private def localAvgStep (values : List Int) : List Int :=
  match values with
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
      let rec loop (prev curr : Int) (tail : List Int) : List Int :=
        match tail with
        | [] => [prev, curr]
        | z :: zs =>
            let mid := (prev + curr + z) / 3
            prev :: loop mid z zs
      loop x y rest

def eval : PDEProgram → HeatState → HeatState
  | .identity, state => state
  | .heat1DStep _, state => { state with values := localAvgStep state.values }

end PDEProgram

def PDELanguage : Language where
  Program := PDEProgram
  Input := HeatState
  Output := HeatState
  eval := PDEProgram.eval

def compileToy (spec : HeytingLean.PDE.PDESpec) : Option PDEProgram :=
  if spec.pdeClass = .parabolic ∧ spec.dimension = 1 then
    some (.heat1DStep { alphaNumerator := 1, alphaDenominator := 2 })
  else
    none

end ProgramCalculus
end HeytingLean
