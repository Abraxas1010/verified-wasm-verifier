/-!
# Simple discrete projectors (nuclei) for demo CLIs

Projectors on arrays of `Float` suitable for time and frequency coarse-graining.
These are intentionally simple and live on the CLI path where we avoid heavy deps.
-/

namespace HeytingLean
namespace Analysis

def timeWindow (m : Nat) (xs : Array Float) : Array Float := Id.run do
  let n := xs.size
  let mut out := xs
  for i in [0:n] do
    if i > m then out := out.set! i 0.0 else ()
  return out

def lowpass (k : Nat) (xs : Array (Float × Float)) : Array (Float × Float) := Id.run do
  -- Keep first k bins; zero the rest
  let n := xs.size
  let mut out := xs
  for i in [0:n] do
    if i ≥ k then out := out.set! i (0.0, 0.0) else ()
  return out

end Analysis
end HeytingLean

