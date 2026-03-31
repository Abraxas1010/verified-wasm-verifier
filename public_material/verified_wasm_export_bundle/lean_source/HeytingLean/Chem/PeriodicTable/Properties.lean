import HeytingLean.Chem.PeriodicTable.CIAAW2024
import HeytingLean.Chem.PeriodicTable.ElectronConfiguration

/-!
# Periodic-table properties (model layer)

This module provides a minimal, fully-defined "properties" API for all 118 elements:
- period (1..7)
- block (s/p/d/f)
- an IUPAC-style group number when meaningful (`Option Nat`)
- a simple valence-electron model useful for materials-science scaffolding

The implementation is derived from `ElectronConfiguration.modelConfiguration` (Aufbau model).
-/

namespace HeytingLean
namespace Chem
namespace PeriodicTable

open HeytingLean.Chem.PeriodicTable

structure ElementProperties where
  atomicNumber      : Nat
  period            : Nat
  block             : Orbital
  iupacGroup?       : Option Nat
  valenceElectrons  : Nat
deriving Repr

namespace ElementProperties

def withZ (Z : Nat) : ElementProperties :=
  { atomicNumber := Z
    period := 0
    block := .s
    iupacGroup? := none
    valenceElectrons := 0 }

end ElementProperties

private def lastSubshell? (cfg : Configuration) : Option Subshell :=
  match cfg.getLast? with
  | none => none
  | some p => some p.1

private def occ (cfg : Configuration) (n : Nat) (l : Orbital) : Nat :=
  match cfg.find? (fun p => p.1.n = n ∧ p.1.l = l) with
  | none => 0
  | some p => p.2

private def periodFromConfig (cfg : Configuration) : Nat :=
  match lastSubshell? cfg with
  | none => 0
  | some s => s.n

private def blockFromConfig (cfg : Configuration) : Orbital :=
  match lastSubshell? cfg with
  | none => .s
  | some s => s.l

/-!
IUPAC-style group model derived from valence shell occupancies.

For f-block elements, group numbering is convention-dependent in the literature; we return `none`
and set `valenceElectrons` to a conservative default (3) for materials scaffolding.
-/
private def groupAndValenceFromConfig (cfg : Configuration) : Option Nat × Nat :=
  let p := periodFromConfig cfg
  match blockFromConfig cfg with
  | .s =>
      let v := occ cfg p .s
      -- Helium is chemically in group 18 despite being an `s`-subshell closure.
      if p = 1 ∧ v = 2 then
        (some 18, v)
      else
        (some v, v)
  | .p =>
      let v := occ cfg p .s + occ cfg p .p
      (some (10 + v), v)
  | .d =>
      -- Transition metals: group = ns + (n-1)d, with `n = period`.
      let v := occ cfg p .s + occ cfg (p - 1) .d
      (some v, v)
  | .f =>
      (none, 3)

def modelProperties (e : Element) : ElementProperties :=
  let Z := atomicNumber e
  let cfg := modelConfiguration Z
  let p := periodFromConfig cfg
  let b := blockFromConfig cfg
  let (g?, v) := groupAndValenceFromConfig cfg
  { atomicNumber := Z
    period := p
    block := b
    iupacGroup? := g?
    valenceElectrons := v }

theorem modelProperties_atomicNumber (e : Element) :
    (modelProperties e).atomicNumber = atomicNumber e := by
  simp [modelProperties]

end PeriodicTable
end Chem
end HeytingLean
