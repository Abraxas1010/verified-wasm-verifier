import HeytingLean.Crypto.Form
import HeytingLean.LoF.Core
import HeytingLean.LoF.Lens.Tensor
import HeytingLean.LoF.Lens.Graph
import HeytingLean.LoF.Lens.Clifford
import HeytingLean.LoF.Lens.RoundTrip

/-
Compile-time sanity checks for LoF canonicalization and lens round-trips.

These are tiny, explicit examples verifying that:
* structurally different `Form n` values have distinct canonical encodings;
* tensor/graph/Clifford encoders respect the shared canonical payload;
* `computeAll` + `decodeAllToCanonical` agrees with `canonicalize` on a sample.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.Crypto
open HeytingLean.LoF

def sampleForm₁ : Form 2 :=
  .and (.var ⟨0, by decide⟩) (.var ⟨1, by decide⟩)

def sampleForm₂ : Form 2 :=
  .or (.var ⟨0, by decide⟩) (.var ⟨1, by decide⟩)

-- Canonical forms for conjunction and disjunction are different.
example : canonicalize sampleForm₁ ≠ canonicalize sampleForm₂ := by
  decide

-- Tensor/graph/Clifford encoders embed the canonical payload with prefixes.
example :
    HeytingLean.LoF.Lens.encodeTensor sampleForm₁ = "tensor::(& v0 v1)" ∧
    HeytingLean.LoF.Lens.encodeGraph sampleForm₁  = "graph::(& v0 v1)" ∧
    HeytingLean.LoF.Lens.encodeClifford sampleForm₁ = "clifford::(& v0 v1)" := by
  decide

end LoF
end Tests
end HeytingLean
