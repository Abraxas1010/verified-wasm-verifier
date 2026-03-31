import HeytingLean.LeanCP.VCG.SymExec

/-!
# LeanCP SMT Metrics and Policy

Phase 5 does not redefine verification conditions. It records which previewed
VCs are intended for automatic discharge and exposes small computable metrics
for benchmark suites.
-/

namespace HeytingLean.LeanCP

inductive SMTBackend where
  | z3
  | cvc5
  deriving DecidableEq, Repr, Inhabited

def SMTBackend.optionValue : SMTBackend → String
  | .z3 => "z3"
  | .cvc5 => "cvc5"

def VCAutoClass.isAutomatic : VCAutoClass → Bool
  | .structural => true
  | .pure => true
  | .manual => false

def VCAutoClass.isSMTEligible : VCAutoClass → Bool
  | .pure => true
  | .structural => false
  | .manual => false

def VCPreview.isAutomatic (vc : VCPreview) : Bool :=
  vc.autoClass.isAutomatic

def VCPreview.isSMTEligible (vc : VCPreview) : Bool :=
  vc.autoClass.isSMTEligible

def countAutomatic (vcs : List VCPreview) : Nat :=
  vcs.countP VCPreview.isAutomatic

def countSMTEligible (vcs : List VCPreview) : Nat :=
  vcs.countP VCPreview.isSMTEligible

def previewAutomationRatePct (vcs : List VCPreview) : Nat :=
  match vcs.length with
  | 0 => 0
  | n => (100 * countAutomatic vcs) / n

def previewSMTEligibleRatePct (vcs : List VCPreview) : Nat :=
  match vcs.length with
  | 0 => 0
  | n => (100 * countSMTEligible vcs) / n

structure SMTBenchmark where
  name : String
  previews : List VCPreview
  deriving Inhabited

def SMTBenchmark.totalVCs (bench : SMTBenchmark) : Nat :=
  bench.previews.length

def SMTBenchmark.automaticVCs (bench : SMTBenchmark) : Nat :=
  countAutomatic bench.previews

def SMTBenchmark.smtEligibleVCs (bench : SMTBenchmark) : Nat :=
  countSMTEligible bench.previews

def SMTBenchmark.automationRatePct (bench : SMTBenchmark) : Nat :=
  previewAutomationRatePct bench.previews

def SMTBenchmark.smtEligibleRatePct (bench : SMTBenchmark) : Nat :=
  previewSMTEligibleRatePct bench.previews

def benchmarkTotals (benches : List SMTBenchmark) : Nat :=
  (benches.map SMTBenchmark.totalVCs).sum

def benchmarkAutomatic (benches : List SMTBenchmark) : Nat :=
  (benches.map SMTBenchmark.automaticVCs).sum

def benchmarkSMTEligible (benches : List SMTBenchmark) : Nat :=
  (benches.map SMTBenchmark.smtEligibleVCs).sum

def benchmarkAutomationRatePct (benches : List SMTBenchmark) : Nat :=
  match benchmarkTotals benches with
  | 0 => 0
  | n => (100 * benchmarkAutomatic benches) / n

def benchmarkSMTEligibleRatePct (benches : List SMTBenchmark) : Nat :=
  match benchmarkTotals benches with
  | 0 => 0
  | n => (100 * benchmarkSMTEligible benches) / n

end HeytingLean.LeanCP
