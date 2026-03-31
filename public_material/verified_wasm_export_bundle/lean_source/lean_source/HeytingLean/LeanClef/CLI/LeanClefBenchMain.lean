import HeytingLean.LoF.ICC.Reduction
import HeytingLean.LeanClef.Export.HVM3

/-!
# LeanClef Benchmark: Standard Full Normalization vs HVM3 Inet

Compares two reduction strategies on the same ICC.Term values:
1. **Standard**: Full normalization via repeated `step?` (Lean native compiled code)
2. **HVM3**: Interaction net reduction via compiled HVM3 (`-c` mode, warm cache)

Methodology (Kimina-inspired warm-cache protocol):
- HVM3 `.so` is pre-compiled once (cold start excluded from measurement)
- Each term reuses the cached `.so` — measures actual inet reduction, not gcc
- Standard reducer uses `fullNormalize` (recurse into all subterms)
- All Church terms applied to (succ, zero) to force full evaluation

Usage:
  lake exe leanclef_bench
-/

open HeytingLean.LoF.ICC
open HeytingLean.LeanClef.Export.HVM3

def monoNs : IO Nat := IO.monoNanosNow

-- ═══════════════════════════════════════
-- Term constructors
-- ═══════════════════════════════════════

def churchNum : Nat → Term
  | 0 => .lam (.lam (.var 0))
  | n + 1 => .lam (.lam (applyN (n + 1) (.var 1) (.var 0)))
where
  applyN : Nat → Term → Term → Term
  | 0, _, x => x
  | n + 1, f, x => .app f (applyN n f x)

def churchSucc : Term :=
  .lam (.lam (.lam (.app (.var 1) (.app (.app (.var 2) (.var 1)) (.var 0)))))

def churchMul : Term :=
  .lam (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0)))))

def churchExp : Term :=
  .lam (.lam (.app (.var 0) (.var 1)))

/-- Force full evaluation: apply expr to (succ, zero). -/
def forceEval (expr : Term) : Term :=
  .app (.app expr churchSucc) (churchNum 0)

def churchMulForced (m n : Nat) : Term :=
  forceEval (.app (.app churchMul (churchNum m)) (churchNum n))

def churchExpForced (m n : Nat) : Term :=
  forceEval (.app (.app churchExp (churchNum m)) (churchNum n))

def sComb : Term :=
  .lam (.lam (.lam (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))
def kComb : Term :=
  .lam (.lam (.var 1))

-- ═══════════════════════════════════════
-- Full normalizer
-- ═══════════════════════════════════════

partial def fullNormalize (fuel : Nat) (t : Term) : Term :=
  let whnf := reduceFuel fuel t
  match whnf with
  | .lam body => .lam (fullNormalize fuel body)
  | .app fn arg => .app (fullNormalize fuel fn) (fullNormalize fuel arg)
  | .bridge body => .bridge (fullNormalize fuel body)
  | .ann val typ => .ann (fullNormalize fuel val) (fullNormalize fuel typ)
  | t => t

partial def fullNormalizeSteps (fuel : Nat) (t : Term) : Nat :=
  let steps := countWhnf fuel t
  let whnf := reduceFuel fuel t
  match whnf with
  | .lam body => steps + fullNormalizeSteps fuel body
  | .app fn arg => steps + fullNormalizeSteps fuel fn + fullNormalizeSteps fuel arg
  | .bridge body => steps + fullNormalizeSteps fuel body
  | .ann val typ => steps + fullNormalizeSteps fuel val + fullNormalizeSteps fuel typ
  | _ => steps
where
  countWhnf : Nat → Term → Nat
  | 0, _ => 0
  | fuel + 1, t =>
    match step? t with
    | some u => 1 + countWhnf fuel u
    | none => 0

-- ═══════════════════════════════════════
-- HVM3 warm-cache runner
-- ═══════════════════════════════════════

initialize hvm3Counter : IO.Ref Nat ← IO.mkRef 0

/-- Pre-warm HVM3's .so cache for a term (gcc compilation happens here). -/
def warmHVM3Cache (t : Term) : IO String := do
  let tmpPath := "/tmp/leanclef_bench_warm.hvm"
  IO.FS.writeFile tmpPath (emitHVM3 t)
  let _ ← IO.Process.output {
    cmd := "/home/abraxas/.cabal/bin/hvm"
    args := #["run", tmpPath, "-c", "-s"]
  }
  return tmpPath

/-- Run HVM3 with warm cache. Returns (wall_ns, interactions, self_reported_ns). -/
def runHVM3Warm (t : Term) : IO (Nat × Nat × Nat) := do
  let idx ← hvm3Counter.modifyGet (fun n => (n, n + 1))
  let tmpPath := s!"/tmp/leanclef_bench_{idx}.hvm"
  IO.FS.writeFile tmpPath (emitHVM3 t)

  -- First run compiles .so (warm cache)
  let _ ← IO.Process.output {
    cmd := "/home/abraxas/.cabal/bin/hvm"
    args := #["run", tmpPath, "-c", "-s"]
  }

  -- Second run measures with warm .so cache (Kimina-style)
  let startNs ← monoNs
  let result ← IO.Process.output {
    cmd := "timeout"
    args := #["30", "/home/abraxas/.cabal/bin/hvm", "run", tmpPath, "-c", "-s"]
  }
  let endNs ← monoNs
  let wallNs := endNs - startNs

  -- Parse WORK: N interactions
  let parts := result.stdout.splitOn "WORK: "
  let interactions := (parts[1]?)
    |>.bind (fun s => s.splitOn " " |>.head? |>.bind String.toNat?)
    |>.getD 0

  -- Parse TIME: X.XXXXXXX seconds → microseconds
  let timeParts := result.stdout.splitOn "TIME: "
  let selfTimeUs : Nat := (timeParts[1]?)
    |>.bind (fun s =>
      let numStr := (s.splitOn " " |>.head? |>.getD "0")
      -- Parse "0.0001207" as microseconds
      let pieces := numStr.splitOn "."
      let wholeSec := (pieces[0]? |>.bind String.toNat?).getD 0
      let fracStr := (pieces[1]?).getD "0"
      -- Take first 6 decimal digits for microseconds
      let padded := fracStr ++ "000000"
      let usDigits := padded.take 6
      let us := (String.toNat? usDigits).getD 0
      some (wholeSec * 1000000 + us))
    |>.getD 0

  return (wallNs, interactions, selfTimeUs)

-- ═══════════════════════════════════════
-- Benchmark harness
-- ═══════════════════════════════════════

def formatNs (ns : Nat) : String :=
  if ns < 1000 then s!"{ns}ns"
  else if ns < 1_000_000 then s!"{ns / 1000}.{(ns % 1000) / 100}μs"
  else if ns < 1_000_000_000 then s!"{ns / 1_000_000}.{(ns % 1_000_000) / 100_000}ms"
  else s!"{ns / 1_000_000_000}.{(ns % 1_000_000_000) / 100_000_000}s"

def formatUs (us : Nat) : String :=
  if us < 1000 then s!"{us}μs"
  else s!"{us / 1000}.{(us % 1000) / 100}ms"

structure BenchResult where
  name : String
  termSize : Nat
  stdTimeNs : Nat
  stdSteps : Nat
  hvm3WallNs : Nat
  hvm3SelfUs : Nat  -- HVM3 self-reported reduction time in μs
  hvm3Interactions : Nat

def runBench (name : String) (t : Term) (fuel : Nat := 500000) : IO BenchResult := do
  let size := t.size

  -- Standard: full normalization (Lean native)
  let stdStart ← monoNs
  let _ := fullNormalize fuel t
  let stdEnd ← monoNs
  let stdNs := stdEnd - stdStart
  let stdSteps := fullNormalizeSteps fuel t

  -- HVM3: warm cache (Kimina-style)
  let (hvm3WallNs, hvm3Itrs, hvm3SelfUs) ← runHVM3Warm t

  let r : BenchResult := {
    name, termSize := size,
    stdTimeNs := stdNs, stdSteps,
    hvm3WallNs, hvm3SelfUs,
    hvm3Interactions := hvm3Itrs,
  }

  -- Verdict: compare standard time vs HVM3 self-reported time
  let hvm3SelfNs := hvm3SelfUs * 1000
  let verdict := if hvm3SelfNs > 0 && stdNs > 0 then
    let ratio := Float.ofNat stdNs / Float.ofNat hvm3SelfNs
    if ratio >= 1.0 then s!"HVM3 inet {ratio.toString}x faster"
    else s!"Std {(1.0/ratio).toString}x faster"
  else "N/A"

  IO.println s!"  {name} (size={size}, steps={stdSteps}, interactions={hvm3Itrs})"
  IO.println s!"    Std full-norm: {formatNs stdNs}"
  IO.println s!"    HVM3 wall:     {formatNs hvm3WallNs} (warm cache)"
  IO.println s!"    HVM3 self-time:{formatUs hvm3SelfUs} (inet reduction only)"
  IO.println s!"    Verdict:       {verdict}"
  IO.println ""
  return r

def main : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════════════════════╗"
  IO.println "║  LeanClef Benchmark: Standard vs HVM3 (Kimina warm-cache)       ║"
  IO.println "║  DGX Spark GB10 | Unified Memory | Compiled (-c), warm .so      ║"
  IO.println "╚═══════════════════════════════════════════════════════════════════╝"
  IO.println ""
  IO.println "Protocol: each HVM3 term pre-compiled (gcc cold excluded)."
  IO.println "Measurement: warm .so wall time + HVM3 self-reported inet time."
  IO.println "All Church terms applied to (succ, zero) for full evaluation."
  IO.println ""

  let mut results : Array BenchResult := #[]

  IO.println "Category 1: Baseline"
  IO.println "─────────────────────"
  results := results.push (← runBench "identity" (.lam (.var 0)))
  results := results.push (← runBench "beta" (.app (.lam (.var 0)) (.lam (.var 0))))
  results := results.push (← runBench "SKK(id)"
    (.app (.app (.app sComb kComb) kComb) (.lam (.var 0))))

  IO.println "Category 2: Church Multiplication (forced)"
  IO.println "───────────────────────────────────────────"
  results := results.push (← runBench "3×3=9" (churchMulForced 3 3))
  results := results.push (← runBench "5×5=25" (churchMulForced 5 5))
  results := results.push (← runBench "8×8=64" (churchMulForced 8 8))
  results := results.push (← runBench "10×10=100" (churchMulForced 10 10))
  results := results.push (← runBench "15×15=225" (churchMulForced 15 15))
  results := results.push (← runBench "20×20=400" (churchMulForced 20 20))

  IO.println "Category 3: Church Exponentiation (forced)"
  IO.println "───────────────────────────────────────────"
  results := results.push (← runBench "2^3=8" (churchExpForced 2 3))
  results := results.push (← runBench "2^4=16" (churchExpForced 2 4))
  results := results.push (← runBench "2^5=32" (churchExpForced 2 5))
  results := results.push (← runBench "2^6=64" (churchExpForced 2 6))
  results := results.push (← runBench "2^8=256" (churchExpForced 2 8))
  results := results.push (← runBench "3^3=27" (churchExpForced 3 3))
  results := results.push (← runBench "3^4=81" (churchExpForced 3 4))

  -- ═══════════════════════════════════════
  IO.println "═══════════════════════════════════════════"
  IO.println "Summary"
  IO.println "═══════════════════════════════════════════"

  let mut totalStdNs : Nat := 0
  let mut totalHvmSelfUs : Nat := 0
  let mut totalHvmWallNs : Nat := 0
  let mut hvm3Wins : Nat := 0
  let mut stdWins : Nat := 0
  for r in results do
    totalStdNs := totalStdNs + r.stdTimeNs
    totalHvmSelfUs := totalHvmSelfUs + r.hvm3SelfUs
    totalHvmWallNs := totalHvmWallNs + r.hvm3WallNs
    let hvm3SelfNs := r.hvm3SelfUs * 1000
    if hvm3SelfNs > 0 then
      if r.stdTimeNs > hvm3SelfNs then hvm3Wins := hvm3Wins + 1
      else stdWins := stdWins + 1

  IO.println s!"  Tests: {results.size}"
  IO.println s!"  Total std time:       {formatNs totalStdNs}"
  IO.println s!"  Total HVM3 self-time: {formatUs totalHvmSelfUs}"
  IO.println s!"  Total HVM3 wall time: {formatNs totalHvmWallNs} (warm cache)"
  IO.println s!"  HVM3 wins (self-time vs std): {hvm3Wins}/{results.size}"
  IO.println s!"  Std wins:                     {stdWins}/{results.size}"
  IO.println ""
  IO.println "Note: 'Std' = Lean-native compiled fullNormalize (in-process)."
  IO.println "'HVM3 self-time' = interaction net reduction only (no process/gcc)."
  IO.println "'HVM3 wall' = warm-cache wall time (process spawn, .so load, reduce)."
