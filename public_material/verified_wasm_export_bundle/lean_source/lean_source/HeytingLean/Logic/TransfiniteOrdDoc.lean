/-!
# Transfinite Ordinal Iteration (Design Sketch)

This module documents the intended proof-oriented extension for transfinite
iteration of nuclei over complete lattices. It is not imported by the main
library or CLIs (kept separate to maintain fast executable builds under strict
flags). The key ingredients:

* iterateOrd R o x:
  - Base: iterateOrd R 0 x = x
  - Successor: iterateOrd R (succ a) x = R (iterateOrd R a x)
  - Limit: iterateOrd R a x = sSup { iterateOrd R b x | b < a }

* Lemma suite (targets):
  - ofNat alignment: iterateOrd R (Ordinal.ofNat n) x = iterateNat R n x
  - Successor monotonicity: iterateOrd R a x ≤ iterateOrd R (succ a) x
  - ω alignment: sSup { iterateNat R n x | n ∈ ℕ } ≤ iterateOrd R ω x
  - Stabilization: if iterateOrd R (succ a) x = iterateOrd R a x then
    ∀ b ≥ a, iterateOrd R b x = iterateOrd R a x.

These are routine in complete-lattice settings with closure operators; their
implementation is straightforward but proof-heavy. We keep them separate and
documented here to avoid slowing down the build of the executable subset.
-/

-- Intentionally no code here; see `HeytingLean.Logic.TransfiniteNucleus` for
-- the ω-fragment and limit constructors used by executables.

