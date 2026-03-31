import HeytingLean.PTS.BaseExtension.Main
import HeytingLean.PTS.BaseExtension.Search

namespace HeytingLean.PTS.BaseExtension.ZKAttestation

open HeytingLean.PTS.BaseExtension

structure AttestedRun where
  fuel : Nat
  program : Program
  goal : Goal
  result : Bool

def AttestedRun.valid (run : AttestedRun) : Prop :=
  run.result = search run.fuel run.program run.goal

def AttestedRun.recomputed (run : AttestedRun) : Bool :=
  search run.fuel run.program run.goal

def commitPayload (run : AttestedRun) : String :=
  s!"hh-search|fuel={run.fuel}|result={run.result}"

end HeytingLean.PTS.BaseExtension.ZKAttestation
