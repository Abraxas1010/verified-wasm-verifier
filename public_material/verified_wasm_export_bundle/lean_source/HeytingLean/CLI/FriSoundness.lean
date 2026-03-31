import HeytingLean.Crypto.ZK.Spec.FRI
import Mathlib

open HeytingLean
open Crypto ZK Spec

/-- Safe max for `Float` values (Lean core lacks a `Float.max`). -/
def fmax (a b : Float) : Float :=
  if a < b then b else a

/-- Parse a `Float` option from a simple decimal string (supports a single `.`). -/
def parseFloatOpt (s : String) : Option Float :=
  match s.splitOn "." with
  | [intPart] =>
      intPart.toInt?.map Float.ofInt
  | [intPart, fracPart] =>
      match intPart.toInt?, fracPart.toNat? with
      | some n, some f =>
          let denom := Float.ofNat ((10 : Nat) ^ fracPart.length)
          let fracVal := (Float.ofNat f) / denom
          if n < 0 then some ((Float.ofInt n) - fracVal) else some ((Float.ofInt n) + fracVal)
      | _, _ => none
  | _ => none

/-- Parse a `Float` with a default fallback. -/
def parseFloatD (s : String) (fallback : Float) : Float :=
  (parseFloatOpt s).getD fallback

/-- Empirical acceptance rate for the one-sample constancy check on a finite array. -/
def sampleConstCheck (xs : Array ℚ) (trials : Nat) : IO Float := do
  if xs.isEmpty then
    return 0
  else
    let n := xs.size
    if trials = 0 then
      return 0
    else
      let x0 := xs[0]!
      let mut acc : Nat := 0
      for _ in [0:trials] do
        let idx ← IO.rand 0 (n - 1)
        if xs[idx]! == x0 then
          acc := acc + 1
      return (Float.ofNat acc) / (Float.ofNat trials)

/-- Fold an array according to a schedule: provide per-round sizes and fold by averaging. -/
structure FoldSchedule where
  sizes : List Nat -- expected domain sizes per round (including level 0)

/-- Fold an array once (even-length check against schedule size). -/
def foldStepArray (expected : Nat) (xs : Array ℚ) : Array ℚ :=
  if xs.size ≠ expected ∨ xs.size < 2 ∨ xs.size % 2 = 1 then
    xs
  else
    let half := expected / 2
    let rec build (i : Nat) (acc : Array ℚ) :=
      if h : i < half then
        let a := xs[i]!
        let b := xs[i + half]!
        build (i+1) (acc.push ((a + b) / 2))
      else
        acc
    build 0 (Array.mkEmpty half)

/-- Empirical acceptance for a multi-round FRI-style constancy check with a given schedule. -/
def sampleFriSchedule (sched : FoldSchedule) (xs : Array ℚ) (trials : Nat) : IO Float := do
  if trials = 0 ∨ xs.isEmpty then
    return 0
  else
    let mut success : Nat := 0
    for _ in [0:trials] do
      let mut cur := xs
      let mut ok := true
      let mut sizes := sched.sizes
      while ok ∧ (!sizes.isEmpty) do
        match sizes with
        | [] => pure ()
        | expected :: rest =>
            if cur.size ≠ expected then
              ok := false
            else
              let idx ← IO.rand 0 (cur.size - 1)
              if cur[idx]! ≠ cur[0]! then
                ok := false
              if !rest.isEmpty then
                cur := foldStepArray expected cur
              sizes := rest
      if ok then
        success := success + 1
    return (Float.ofNat success) / (Float.ofNat trials)

/-- Derive the sequence of domain sizes seen during folding (level 0 included) using halving. -/
def foldSizes (xs : Array ℚ) (rounds : Nat) : List Nat :=
  let rec go (cur : Array ℚ) (r : Nat) (acc : List Nat) :=
    if r = 0 then
      (cur.size :: acc).reverse
    else
      let acc' := cur.size :: acc
      go (foldStepArray cur.size cur) (r - 1) acc'
  go xs rounds []

/-- Parse a comma-separated list of natural numbers into a schedule; fallback to halving sizes. -/
def parseSchedule (fallback : List Nat) (s? : Option String) : List Nat :=
  match s? with
  | none => fallback
  | some s =>
      let parts := s.splitOn ","
      let parsed := parts.map (·.toNat?)
      if parsed.all Option.isSome then
        parsed.map Option.get!
      else
        fallback

/-- Parse three floats (q, η, s) from args (starting at index 3). -/
def parseProximity (args : List String) (start : Nat := 0) : Float × Float × Float :=
  let q := args.getD start "0.1"
  let η := args.getD (start + 1) "2.0"
  let s := args.getD (start + 2) "1.0"
  let qf := parseFloatD q 0.1
  let ηf := parseFloatD η 2.0
  let sf := parseFloatD s 1.0
  (qf, ηf, sf)

def parseNatD (s : String) (fallback : Nat) : Nat :=
  s.toNat?.getD fallback

def clamp01 (x : Float) : Float :=
  if x < 0 then 0 else if 1 < x then 1 else x

def sumList (xs : List Float) : Float :=
  xs.foldl (· + ·) 0

def minListOr (fallback : Float) : List Float → Float
  | [] => fallback
  | x :: xs => xs.foldl (fun acc t => if t < acc then t else acc) x

def absDistanceFromDim (m dim : Nat) : Nat :=
  if dim = 0 ∨ m = 0 then 0
  else if dim ≤ m then m - dim + 1 else 0

def relDistanceFromAbs (m dAbs : Nat) : Float :=
  if m = 0 then 0 else (Float.ofNat dAbs) / (Float.ofNat m)

def boundFromAbs (m dAbs : Nat) : Float :=
  if m = 0 then 0 else (Float.ofNat (m - dAbs)) / (Float.ofNat m)

/-- Zip with default: truncate to the shorter of the two lists. -/
def zipWithTrunc {α β γ} (f : α → β → γ) : List α → List β → List γ
  | a :: as, b :: bs => f a b :: zipWithTrunc f as bs
  | _, _ => []

/-- Derive a default `δ_i` list from schedule sizes: (m_i-1)/m_i as a crude RS gap. -/
def deltaRSFromSchedule (sched : List Nat) : List Float :=
  sched.map (fun n => if _h : n = 0 then 0 else (Float.ofNat (n - 1)) / (Float.ofNat n))

/-- Derive a Reed–Solomon relative distance list from a schedule and optional dimensions.
    Uses `(m - dim + 1) / m` when `dim ≤ m`, otherwise falls back to `0`. -/
def deltaRSFromDims (sched dims : List Nat) : List Float :=
  zipWithTrunc (fun m d =>
    if _h : d ≤ m then
      (Float.ofNat (m - d + 1)) / (Float.ofNat m)
    else 0) sched dims

/-- Parse a comma-separated list of deltas for proximity scaling. -/
def parseDeltas (fallback : List Float) (s? : Option String) : List Float :=
  match s? with
  | none => fallback
  | some s =>
      let parts := s.splitOn ","
      let parsed := parts.map parseFloatOpt
      if parsed.all Option.isSome then
        parsed.map (·.get!)
      else
        fallback

/-- Parse a comma-separated list of dimensions to accompany the schedule. -/
def parseDims (fallback : List Nat) (s? : Option String) : List Nat :=
  match s? with
  | none => fallback
  | some s =>
      let parts := s.splitOn ","
      let parsed := parts.map (·.toNat?)
      if parsed.all Option.isSome then
        parsed.map Option.get!
      else
        fallback

/-- Build a capped-dimension list from a single dimension `d` and schedule sizes. -/
def capDimList (d : Nat) (sched : List Nat) : List Nat :=
  sched.map (fun m => Nat.min d m)

/-- Derive folded dimensions assuming degree halves each round (capped and at least 1). -/
def deriveDimsFold (dim0 : Nat) (sched : List Nat) : List Nat :=
  let rec go (i : Nat) (ss : List Nat) : List Nat :=
    match ss with
    | [] => []
    | m :: ms =>
        let d := Nat.max 1 (dim0 / Nat.pow 2 i)
        let dCap := Nat.min d m
        dCap :: go (i+1) ms
  go 0 sched

def deriveDimsFromArg (sched : List Nat) (s? : Option String) : List Nat :=
  match s? with
  | none => sched
  | some s =>
      if s.contains ',' then
        let dims := parseDims sched (some s)
        if dims.length = sched.length then
          zipWithTrunc Nat.min dims sched
        else
          sched
      else
        let dim0 := parseNatD s (sched.headD 1)
        deriveDimsFold dim0 sched

/-- Minimal CLI harness for FRI soundness artifacts.
    Reports that the library lemmas are available; extend later with sampling. -/
def main (args : List String) : IO Unit := do
  IO.println "FRI soundness harness (CLI): empirical vs RS-derived bounds"
  IO.println "  Lemmas (Spec.FRI.Example): friSchedule_soundness_bound_sum_rs, friSchedule_proximity_bound_sum_scaled_rs_tight"
  IO.println "Args: [m0] [kRounds] [trials] [dims|dim0] [q] [η] [s] [schedSizes?] [deltaRel?]"
  IO.println "Note: RS-tight bounds assume each folded oracle is an RS codeword of dimension dim_i (not enforced by this CLI sampler)."

  let m0 : Nat := parseNatD (args.getD 0 "8") 8
  let k : Nat := parseNatD (args.getD 1 "3") 3
  let trials : Nat := parseNatD (args.getD 2 "2000") 2000
  let dimsArg? := args[3]?
  let (q, η, s) := parseProximity args 4
  let schedArg? := args[7]?
  let deltaRelArg? := args[8]?

  let mkConstArray (n : Nat) : Array ℚ :=
    Array.ofFn (fun (_ : Fin n) => (1 : ℚ))
  let mkNonConstArray (n : Nat) : Array ℚ :=
    Array.ofFn (fun i : Fin n => (i.1 : ℚ))

  let baseOracle := mkNonConstArray m0
  let defaultSched : List Nat :=
    if k = 0 then [] else foldSizes baseOracle (k - 1)
  let schedSizes := parseSchedule defaultSched schedArg?
  let kEff := schedSizes.length
  let sched : FoldSchedule := ⟨schedSizes⟩

  let nonConstArr := mkNonConstArray (schedSizes.headD m0)
  let constArr := mkConstArray (schedSizes.headD m0)

  let dim0Default : Nat := Nat.max 1 (m0 / 2)
  let dims : List Nat :=
    match dimsArg? with
    | none => deriveDimsFold dim0Default schedSizes
    | some _ => deriveDimsFromArg schedSizes dimsArg?

  let distAbs : List Nat := zipWithTrunc absDistanceFromDim schedSizes dims
  let deltaRelDefault : List Float := zipWithTrunc relDistanceFromAbs schedSizes distAbs
  let deltaRel : List Float :=
    let parsed := parseDeltas deltaRelDefault deltaRelArg?
    if parsed.length = schedSizes.length then parsed else deltaRelDefault

  let roundBoundsRS : List Float := zipWithTrunc (fun m dAbs => boundFromAbs m dAbs) schedSizes distAbs
  let roundBoundsFromDelta : List Float := deltaRel.map (fun δ => fmax 0 (1 - δ))

  let slackSeq : List Float := deltaRel.map (fun δ => fmax 0 (q * η * s * δ))

  let sumBoundRS := sumList roundBoundsRS
  let minBoundRS := minListOr 0 roundBoundsRS
  let sumBoundDelta := sumList roundBoundsFromDelta
  let minBoundDelta := minListOr 0 roundBoundsFromDelta
  let sumSlack := sumList slackSeq
  let sumBoundSlack := sumBoundDelta + sumSlack

  let empConst ← sampleFriSchedule sched constArr trials
  let empNonConst ← sampleFriSchedule sched nonConstArr trials

  IO.println s!"Schedule sizes (k={kEff}): {schedSizes}"
  IO.println s!"Dims (k={dims.length}): {dims}"
  IO.println s!"RS distance (absolute) dAbs_i := m_i - dim_i + 1: {distAbs}"
  IO.println s!"RS distance (relative) δRel_i := dAbs_i / m_i (default or overridden): {deltaRel}"
  IO.println s!"Round RS bounds (exact): (m_i - dAbs_i)/m_i = (dim_i - 1)/m_i: {roundBoundsRS}"
  IO.println s!"Round bounds from δRel (exact): 1 - δRel_i: {roundBoundsFromDelta}"
  IO.println s!"Slack_i := max(0, q*η*s*δRel_i), q={q}, η={η}, s={s}: {slackSeq}"
  IO.println s!"Empirical accept (const oracle, {trials} trials): {empConst}"
  IO.println s!"Empirical accept (non-const oracle, {trials} trials): {empNonConst}"
  IO.println s!"Bound total (min; tight, independence-free): {minBoundDelta} (clamped {clamp01 minBoundDelta})"
  IO.println s!"Bound total (sum; loose additive upper bound, may exceed 1): {sumBoundDelta} (clamped {clamp01 sumBoundDelta})"
  IO.println s!"Bound total (sum + slack; loose additive): {sumBoundSlack} (clamped {clamp01 sumBoundSlack})"
  if sumBoundRS != sumBoundDelta ∨ minBoundRS != minBoundDelta then
    IO.println s!"(internal check) from dAbs: min={minBoundRS}, sum={sumBoundRS}"
