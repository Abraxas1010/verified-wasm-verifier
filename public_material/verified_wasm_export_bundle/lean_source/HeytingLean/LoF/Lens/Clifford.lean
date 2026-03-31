import HeytingLean.Crypto.Form
import HeytingLean.LoF.Core

/-
Clifford lens encoders/decoders for `Form n`.

As with the tensor and graph lenses, we wrap the canonical `Form n`
encoding from `HeytingLean.LoF.Core` with a lens-specific prefix.
-/

namespace HeytingLean
namespace LoF
namespace Lens

open HeytingLean.Crypto

/-- Encode a `Form n` for the Clifford lens by prefixing its canonical
string representation. -/
def encodeClifford {n} (f : Form n) : String :=
  let canon := HeytingLean.LoF.canonicalize f
  "clifford::" ++ canon.asString

/-- Decode a Clifford-encoded string back to a canonical wrapper.

If the string has the expected `clifford::` prefix, the payload after
the prefix is treated as the canonical form. Otherwise we fall back
to the supplied canonical representative. -/
def decodeCliffordToCanonical {n} (s : String) (canon : Canonical n) : Canonical n :=
  if s.startsWith "clifford::" then
    { asString := s.drop ("clifford::".length) }
  else
    canon

end Lens
end LoF
end HeytingLean

