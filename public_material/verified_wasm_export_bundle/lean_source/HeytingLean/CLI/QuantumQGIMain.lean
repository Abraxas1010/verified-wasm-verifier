import HeytingLean.Quantum.QGIContext
import HeytingLean.Quantum.QGIPhaseLaw
import HeytingLean.Quantum.VacuumOmegaRBridge

/-
QGI + Ωᴿ phase CLI

This executable specialises the abstract QGI + Ωᴿ scaffold to the
concrete `QGIContext.qgiBaseContext` and prints a single-line, machine
friendly summary of:

* the input parameters (m, g, T),
* the symbolic t³ phase `t3Phase`,
* and the corresponding `gaugePhase` between the laboratory and
  free-fall frames recorded in a `QGIPhaseModel`.

Example (using default PhysParams hbar=1, G=1; integer inputs only):

  lake exe quantum_qgi_phase --m 1 --g 10 --T 1

Outputs (schematically):

  m=1 g=10 T=1 t3Phase=... gaugePhase=...

This is intended for scripting / plotting rather than for core proofs.
-/

namespace HeytingLean.CLI

open HeytingLean.Quantum
open HeytingLean.Quantum.QGIContext
open HeytingLean.Quantum.QGIPhaseLaw

/-- Simple flag parser on a flat argument list. -/
private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x :: y :: rest =>
      if x = flag then some y else parseArg (y :: rest) flag
  | _ => none

/-- Parse an integer parameter from a string and return it as a `Float`,
    defaulting to `d` on failure. -/
private def parseIntAsFloat (s : Option String) (d : Float) : Float :=
  match s with
  | some t =>
      match t.toInt? with
      | some n => Float.ofInt n
      | none   => d
  | none => d

/-- Default symbolic gravitational/phase parameters for the Float demo. -/
def demoParams : PhysParamsF :=
  { hbar := 1.0, G := 1.0 }

/-- Main entry point for the `quantum_qgi_phase` CLI. -/
def QuantumQGIMain.run (argv : List String) : IO Unit := do
  let mF := parseIntAsFloat (parseArg argv "--m") 1.0
  let gF := parseIntAsFloat (parseArg argv "--g") 10.0
  let tF := parseIntAsFloat (parseArg argv "--T") 1.0
  let pairFlag := parseArg argv "--pair"
  -- Choose between the trivial laboratory/laboratory pair and the
  -- laboratory/free-fall pair. By default we use `(lab, free)`.
  let isLabLab : Bool :=
    match pairFlag with
    | some s => decide (s = "lab-lab")
    | none   => false
  let pairLabel : String := if isLabLab then "lab-lab" else "lab-free"
  -- All numeric work stays in `Float` via the Float-valued phase law.
  let φ_t3 := t3Phase demoParams mF gF tF
  -- For the laboratory/laboratory pair the gauge phase is taken to be
  -- trivial; for the laboratory/free-fall pair we use the T³ profile.
  let φ_gauge :=
    if isLabLab then 0.0 else gaugePhase demoParams mF gF tF
  IO.println
    s!"m={mF} g={gF} T={tF} framePair={pairLabel} t3Phase={φ_t3} gaugePhase={φ_gauge}"

end HeytingLean.CLI

/-- Top-level `main` for the `quantum_qgi_phase` executable. -/
def main (argv : List String) : IO Unit :=
  HeytingLean.CLI.QuantumQGIMain.run argv
