import HeytingLean.LoF.ICC.Reduction
import HeytingLean.LeanClef.FFI.InetReduce
import HeytingLean.LeanClef.Export.HVM3

/-!
# LeanClef Inet Benchmark: 3-Way Comparison

Compares three reduction backends on identical ICC.Term values:
1. **Lean native**: `fullNormalize` (compiled aarch64, in-process)
2. **HVM3**: Interaction nets via subprocess (`hvm run -c`, warm cache)
3. **Inet FFI**: Precompiled C kernel via `@[extern]` (in-process, zero subprocess)

The Inet FFI backend eliminates the 284ms gcc cold-start and 11ms warm-cache
overhead of HVM3, bringing wall time close to the raw reduction time.

Usage:
  lake exe leanclef_inet_bench
-/

open HeytingLean.LoF.ICC
open LeanClef.FFI
open HeytingLean.LeanClef.Export.HVM3

def monoNs : IO Nat := IO.monoNanosNow

-- ═══════════════════════════════════════
-- Term constructors (same as LeanClefBenchMain)
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

def forceEval (expr : Term) : Term :=
  .app (.app expr churchSucc) (churchNum 0)

def churchMulForced (m n : Nat) : Term :=
  forceEval (.app (.app churchMul (churchNum m)) (churchNum n))

def churchExpForced (m n : Nat) : Term :=
  forceEval (.app (.app churchExp (churchNum m)) (churchNum n))

-- ═══════════════════════════════════════
-- Full normalizer (Lean native baseline)
-- ═══════════════════════════════════════

partial def fullNormalize (fuel : Nat) (t : Term) : Term :=
  let whnf := reduceFuel fuel t
  match whnf with
  | .lam body => .lam (fullNormalize fuel body)
  | .app fn arg => .app (fullNormalize fuel fn) (fullNormalize fuel arg)
  | .bridge body => .bridge (fullNormalize fuel body)
  | .ann val typ => .ann (fullNormalize fuel val) (fullNormalize fuel typ)
  | t => t

-- ═══════════════════════════════════════
-- Benchmark harness
-- ═══════════════════════════════════════

def formatNs (ns : Nat) : String :=
  if ns < 1000 then s!"{ns}ns"
  else if ns < 1_000_000 then s!"{ns / 1000}.{(ns % 1000) / 100}μs"
  else if ns < 1_000_000_000 then s!"{ns / 1_000_000}.{(ns % 1_000_000) / 100_000}ms"
  else s!"{ns / 1_000_000_000}.{(ns % 1_000_000_000) / 100_000_000}s"

initialize hvm3Ctr : IO.Ref Nat ← IO.mkRef 0

/-- Run HVM3 with warm cache (2 calls: first compiles, second measures). -/
def runHVM3Warm (t : Term) : IO Nat := do
  let idx ← hvm3Ctr.modifyGet (fun n => (n, n + 1))
  let tmpPath := s!"/tmp/leanclef_inet_bench_{idx}.hvm"
  IO.FS.writeFile tmpPath (emitHVM3 t)
  -- Warm: compile .so
  let _ ← IO.Process.output {
    cmd := "/home/abraxas/.cabal/bin/hvm"
    args := #["run", tmpPath, "-c", "-s"]
  }
  -- Measure: warm run
  let startNs ← monoNs
  let _ ← IO.Process.output {
    cmd := "timeout"
    args := #["30", "/home/abraxas/.cabal/bin/hvm", "run", tmpPath, "-c", "-s"]
  }
  let endNs ← monoNs
  return endNs - startNs

def runBench (name : String) (t : Term) (fuel : Nat := 500000) : IO Unit := do
  let size := t.size

  -- 1. Lean native
  let stdStart ← monoNs
  let _ := fullNormalize fuel t
  let stdEnd ← monoNs
  let stdNs := stdEnd - stdStart

  -- 2. Inet FFI
  let ffiStart ← monoNs
  let (resultOpt, interactions) ← reduceViaInet t fuel
  let ffiEnd ← monoNs
  let ffiNs := ffiEnd - ffiStart
  let ffiOk := resultOpt.isSome

  -- 3. HVM3 warm
  let hvm3Ns ← runHVM3Warm t

  -- Speedup: FFI vs HVM3
  let speedup := if ffiNs > 0 then Float.ofNat hvm3Ns / Float.ofNat ffiNs else 0.0

  IO.println s!"  {name} (size={size})"
  IO.println s!"    Lean native:  {formatNs stdNs}"
  IO.println s!"    Inet FFI:     {formatNs ffiNs} ({interactions} nodes, ok={ffiOk})"
  IO.println s!"    HVM3 warm:    {formatNs hvm3Ns}"
  IO.println s!"    FFI vs HVM3:  {speedup.toString}x faster"
  IO.println ""

def main : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════════════════════╗"
  IO.println "║  LeanClef 3-Way Benchmark: Lean Native vs Inet FFI vs HVM3     ║"
  IO.println "║  DGX Spark GB10 | Precompiled C Kernel | Zero Subprocess        ║"
  IO.println "╚═══════════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Initialize the precompiled reducer
  IO.println "Calling inetInit..."
  inetInit
  IO.println "Inet FFI kernel initialized."

  -- Smoke test: serialize and reduce identity
  IO.println "Smoke test: serialize identity..."
  let idTerm : Term := .lam (.var 0)
  let bytes := serializeTerm idTerm
  IO.println s!"  Serialized: {bytes.size} bytes"

  IO.println "Smoke test: reduce identity..."
  let (resultOpt, itrs) ← reduceViaInet idTerm 1000
  IO.println s!"  Result: {resultOpt.isSome}, interactions: {itrs}"
  IO.println ""

  IO.println "Category 1: Baseline"
  IO.println "─────────────────────"
  runBench "identity" (.lam (.var 0))
  runBench "beta" (.app (.lam (.var 0)) (.lam (.var 0)))
  runBench "K combinator" (.lam (.lam (.var 1)))

  IO.println "Category 2: Church Multiplication (forced)"
  IO.println "───────────────────────────────────────────"
  runBench "3×3=9" (churchMulForced 3 3)
  runBench "5×5=25" (churchMulForced 5 5)
  runBench "10×10=100" (churchMulForced 10 10)

  IO.println "Category 3: Church Exponentiation (forced)"
  IO.println "───────────────────────────────────────────"
  runBench "2^4=16" (churchExpForced 2 4)
  runBench "2^6=64" (churchExpForced 2 6)
  runBench "3^3=27" (churchExpForced 3 3)
  runBench "3^4=81" (churchExpForced 3 4)

  -- Cleanup
  inetShutdown
  IO.println "Inet FFI kernel shut down."
