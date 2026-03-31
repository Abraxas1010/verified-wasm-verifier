import OSforGFF.OS.Master

/-!
# OSforGFF (Stable Import Set)

This wrapper makes the Lean 4.24 backport of `OSforGFF` available inside the
HeytingLean package under a stable import path.

Why this exists:
- The hostile audit required `OSforGFF` to stop being search-sidecar-only.
- HeytingLean wants a buildable, indexable import surface for the full
  Osterwalder-Schrader development of the 4D Gaussian free field.
- The actual package is backported in `recovery/external_backports/OSforGFF`
  for this remediation branch; this wrapper is the repo-local import anchor.

Build policy:
- Strict core: this wrapper is not imported by `HeytingLean.lean`.
- External integration: `(cd lean && lake build HeytingLean.External.OSforGFFStable)`

The upstream master theorem already transitively pulls the full OSforGFF proof
graph, so this wrapper imports only `OSforGFF.OS.Master`.
-/
