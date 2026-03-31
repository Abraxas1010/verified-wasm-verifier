import HeytingLean.PTS.BaseExtension.Demo.GuardrailPolicy
import HeytingLean.PTS.BaseExtension.ZKAttestation

namespace HeytingLean.PTS.BaseExtension.Demo

open HeytingLean.PTS.BaseExtension
open HeytingLean.PTS.BaseExtension.ZKAttestation

def complianceRun : AttestedRun :=
  { fuel := 96
    program := guardrailProgram
    goal := encode guardrailPolicy
    result := guardrailResult }

def complianceValid : Prop :=
  complianceRun.valid

end HeytingLean.PTS.BaseExtension.Demo
