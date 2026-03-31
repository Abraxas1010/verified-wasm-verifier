import HeytingLean.Crypto.Form
import HeytingLean.LoF.Core

/-
Tensor lens encoders/decoders for `Form n`.

The current representation is a stable textual wrapper around the
canonical `Form n` encoding from `HeytingLean.LoF.Core`. This keeps
the API honest and round-trippable without committing to a specific
numeric tensor format yet.
-/

namespace HeytingLean
namespace LoF
namespace Lens

open HeytingLean.Crypto

/-- Encode a `Form n` for the tensor lens by prefixing its canonical
string representation. -/
def encodeTensor {n} (f : Form n) : String :=
  let canon := HeytingLean.LoF.canonicalize f
  "tensor::" ++ canon.asString

/-- Decode a tensor-encoded string back to a canonical wrapper.

If the string has the expected `tensor::` prefix, the payload after
the prefix is treated as the canonical form. Otherwise we fall back
to the supplied canonical representative. -/
def decodeTensorToCanonical {n} (s : String) (canon : Canonical n) : Canonical n :=
  if s.startsWith "tensor::" then
    { asString := s.drop ("tensor::".length) }
  else
    canon

end Lens
end LoF
end HeytingLean
