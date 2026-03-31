import Lean.Data.Json
import HeytingLean.Numbers.Goldbach.Data
import HeytingLean.Bridges.Emergence
import HeytingLean.Occam.Emergence

/-
# Goldbach — Emergence / Occam / PSR bridge

This module provides a small, semantics-level bridge between bounded
Goldbach verification logs and the existing Emergence Selector,
Occam/`ModelComplexity`, and PSR robustness interfaces.

Rather than constructing a particular TPM inside Lean, we treat the
finite Goldbach dynamics as already packaged into a TPM `tpm : TPM n`
on a finite state space of size `n` (for example, derived externally
from Goldbach comet or circle-method data).  The definitions here
then:

* run the Emergence Selector on `tpm`,
* expose the emergence-driven `ModelComplexity` profile, and
* specialise the PSR robustness predicate to this Goldbach TPM.

All constructions are purely structural and contain no proof holes.
-/

namespace HeytingLean
namespace Numbers
namespace Goldbach

open Lean
open Lean.Json
open HeytingLean.Bridges
open HeytingLean.Bridges.Emergence
open scoped ENNReal

/-- A finite Goldbach dynamics profile couples:

* a bounded verification log (as parsed by `Goldbach.Data.Verify`), and
* a finite-state TPM on `Fin n`.

The TPM may be obtained by any external construction (for example,
from Goldbach comet/circle data); this module does not assume a
particular recipe, it merely provides spec-level bridges to the
Emergence/Occam/PSR stack. -/
structure Dynamics (n : Nat) where
  log : Verify.Log
  tpm : TPM n

/-- Run the Emergence Selector on a Goldbach dynamics profile,
returning the chosen macroscale and associated complexity profile. -/
noncomputable def Dynamics.emergentChoice {n : Nat}
    (G : Dynamics n) : EmergentChoice n :=
  chooseScale G.tpm

/-- Emergence-driven `ModelComplexity` profile for partitions of the
TPM carried by a Goldbach dynamics profile, relative to a chosen
candidate set.  This is a direct application of the generic
`emergenceModelComplexity` construction. -/
noncomputable def Dynamics.emergenceModelComplexity {n : Nat}
    (G : Dynamics n) (candidates : List (Partition n)) :=
  HeytingLean.Occam.Emergence.emergenceModelComplexity G.tpm candidates

/-- PSR robustness predicate specialised to a Goldbach dynamics
profile: determinism and specificity at partition `π` are invariant
under the supplied perturbation relation `Perturb` on the TPM. -/
def Dynamics.PSR {n : Nat}
    (G : Dynamics n)
    (Perturb : TPM n → TPM n → Prop)
    (π : Partition n) : Prop :=
  HeytingLean.Occam.Emergence.PSR_RobustAtScale Perturb G.tpm π

/-- Under the identity perturbation relation, PSR robustness for a
Goldbach dynamics profile is immediate, by instantiating the generic
`PSR_RobustAtScale_id` lemma. -/
lemma Dynamics.PSR_id {n : Nat}
    (G : Dynamics n) (π : Partition n) :
    G.PSR HeytingLean.Occam.Emergence.PerturbId π :=
  HeytingLean.Occam.Emergence.PSR_RobustAtScale_id G.tpm π

/- A minimal view of a Goldbach TPM report derived from comet data.

This mirrors the JSON shape emitted by `tools/goldbach/tpm_comet.py`
(`GoldbachTPMComet.v1`), but focuses only on the finite matrix and
its dimension.  The `states` and `g` fields are intentionally omitted
at this level; they can be threaded separately if needed. -/
structure CometTPM where
  N     : Nat
  n     : Nat
  tpm   : List (List ℝ≥0∞)

/-! ### JSON parsing for comet‑derived TPMs -/

/-- Parse a `GoldbachTPMComet.v1` JSON object into a `CometTPM`.  The
parser is deliberately small and strict: it checks the version tag and
that the TPM is an `n × n` matrix, where `n = states.length`.  Numeric
entries are interpreted via the `JsonNumber` mantissa/exponent pair and
embedded into `ℝ≥0∞` using `ENNReal.ofReal`. -/
noncomputable def cometTPMFromJson (j : Json) : Except String CometTPM := do
  let obj ←
    match j.getObj? with
    | Except.ok _ => pure j
    | Except.error _ => .error "expected object"
  let ver ←
    match obj.getObjVal? "version" with
    | Except.ok v =>
        match v.getStr? with
        | Except.ok s => pure s
        | Except.error _ => .error "field 'version' not a String"
    | Except.error _ => .error "missing field 'version'"
  if ver ≠ "GoldbachTPMComet.v1" then
    .error s!"unexpected version '{ver}'"
  let N ←
    match obj.getObjVal? "N" with
    | Except.ok v =>
        match v.getNat? with
        | Except.ok k => pure k
        | Except.error _ => .error "field 'N' not a Nat"
    | Except.error _ => .error "missing field 'N'"
  let statesArr ←
    match obj.getObjVal? "states" with
    | Except.ok v =>
        match v.getArr? with
        | Except.ok a => pure a
        | Except.error _ => .error "field 'states' not an array"
    | Except.error _ => .error "missing field 'states'"
  let n := statesArr.size
  let tpmJ ←
    match obj.getObjVal? "tpm" with
    | Except.ok v => pure v
    | Except.error _ => .error "missing field 'tpm'"
  let rowsArr ←
    match tpmJ.getArr? with
    | Except.ok a => pure a
    | Except.error _ => .error "field 'tpm' not an array"
  let rec parseRow (v : Json) : Except String (List ℝ≥0∞) :=
    match v.getArr? with
    | Except.error _ => .error "TPM row is not an array"
    | Except.ok a =>
        let rec go (xs : List Json) (acc : List ℝ≥0∞) :
            Except String (List ℝ≥0∞) :=
          match xs with
          | [] => .ok acc.reverse
          | h :: t =>
              match h.getNum? with
              | Except.ok s =>
                  -- Interpret the JSON number as a real `mantissa * 10^{-exponent}`.
                  let r : ℝ :=
                    (s.mantissa : ℝ) / (10 : ℝ) ^ s.exponent
                  let w : ℝ≥0∞ := ENNReal.ofReal r
                  go t (w :: acc)
              | Except.error _ =>
                  .error "non-numeric entry in TPM row"
        go a.toList []
  let rec parseRows (rs : List Json) (acc : List (List ℝ≥0∞)) :
      Except String (List (List ℝ≥0∞)) := do
    match rs with
    | [] => pure acc.reverse
    | r :: rt =>
        let row ← parseRow r
        parseRows rt (row :: acc)
  let tpm ← parseRows rowsArr.toList []
  if tpm.length ≠ n then
    .error "row count does not match states length"
  else if tpm.any (fun row => row.length ≠ n) then
    .error "TPM is not square"
  else
    pure { N, n, tpm }

/-- Generic finite TPM encoded in the `EmergenceTPM.v1` schema used by
the selector CLI.  This is independent of Goldbach and can be reused
for other finite-state experiments that supply a TPM externally. -/
structure EmergenceTPM where
  n   : Nat
  tpm : List (List ℝ≥0∞)

/-- Parse an `EmergenceTPM.v1` JSON object into an `EmergenceTPM`.
The parser is intentionally strict: it checks the version tag, the
dimension `n`, and that `tpm` is an `n × n` matrix. -/
noncomputable def emergenceTPMFromJson (j : Json) : Except String EmergenceTPM := do
  let obj ←
    match j.getObj? with
    | .ok _ => pure j
    | .error _ => .error "expected object"
  let ver ←
    match obj.getObjVal? "version" with
    | .ok v =>
        match v.getStr? with
        | .ok s => pure s
        | .error _ => .error "field 'version' not a String"
    | .error _ => .error "missing field 'version'"
  if ver ≠ "EmergenceTPM.v1" then
    .error s!"unexpected version '{ver}'"
  let n ←
    match obj.getObjVal? "n" with
    | .ok v =>
        match v.getNat? with
        | .ok k => pure k
        | .error _ => .error "field 'n' not a Nat"
    | .error _ => .error "missing field 'n'"
  let tpmJ ←
    match obj.getObjVal? "tpm" with
    | .ok v => pure v
    | .error _ => .error "missing field 'tpm'"
  let rowsArr ←
    match tpmJ.getArr? with
    | .ok a => pure a
    | .error _ => .error "field 'tpm' not an array"
  let rec parseRow (v : Json) : Except String (List ℝ≥0∞) :=
    match v.getArr? with
    | .error _ => .error "TPM row is not an array"
    | .ok a =>
        let rec go (xs : List Json) (acc : List ℝ≥0∞) :
            Except String (List ℝ≥0∞) :=
          match xs with
          | [] => .ok acc.reverse
          | h :: t =>
              match h.getNum? with
              | .ok s =>
                  let r : ℝ :=
                    (s.mantissa : ℝ) / (10 : ℝ) ^ s.exponent
                  let w : ℝ≥0∞ := ENNReal.ofReal r
                  go t (w :: acc)
              | .error _ =>
                  .error "non-numeric entry in TPM row"
        go a.toList []
  let rec parseRows (rs : List Json) (acc : List (List ℝ≥0∞)) :
      Except String (List (List ℝ≥0∞)) := do
    match rs with
    | [] => pure acc.reverse
    | r :: rt =>
        let row ← parseRow r
        parseRows rt (row :: acc)
  let tpm ← parseRows rowsArr.toList []
  if tpm.length ≠ n then
    .error "row count does not match 'n'"
  else if tpm.any (fun row => row.length ≠ n) then
    .error "TPM is not square"
  else
    pure { n, tpm }

/-- Embed a finite `CometTPM` into the `TPM n` type used by the
Emergence stack.  The entries are already `ℝ≥0∞` weights, so we simply
read them with default `0` for out-of-range indices. Row normalisation
is enforced on the Python side (`tpm_comet.py`). -/
noncomputable def CometTPM.toTPM (c : CometTPM) : TPM c.n :=
  ⟨ (fun i j =>
      let row := c.tpm.getD i.1 []
      row.getD j.1 0),
    True ⟩

/-- Embed a generic `EmergenceTPM` into the `TPM n` type used by the
Emergence stack.  As with `CometTPM.toTPM`, the entries are treated as
nonnegative weights with row normalisation enforced at the data layer. -/
noncomputable def EmergenceTPM.toTPM (e : EmergenceTPM) : TPM e.n :=
  ⟨ (fun i j =>
      let row := e.tpm.getD i.1 []
      row.getD j.1 0),
    True ⟩

end Goldbach
end Numbers
end HeytingLean
