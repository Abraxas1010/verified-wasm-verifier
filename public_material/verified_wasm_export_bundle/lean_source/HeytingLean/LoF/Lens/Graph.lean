import HeytingLean.Crypto.Form
import HeytingLean.LoF.Core

/-
Graph lens encoders/decoders for `Form n`.

These mirror the tensor lens convention: a simple textual wrapper
around the canonical `Form n` encoding from `HeytingLean.LoF.Core`,
with a lens-specific prefix.
-/

namespace HeytingLean
namespace LoF
namespace Lens

open HeytingLean.Crypto

/-- Encode a `Form n` for the graph lens by prefixing its canonical
string representation. -/
def encodeGraph {n} (f : Form n) : String :=
  let canon := HeytingLean.LoF.canonicalize f
  "graph::" ++ canon.asString

/-- Decode a graph-encoded string back to a canonical wrapper.

If the string has the expected `graph::` prefix, the payload after
the prefix is treated as the canonical form. Otherwise we fall back
to the supplied canonical representative. -/
def decodeGraphToCanonical {n} (s : String) (canon : Canonical n) : Canonical n :=
  if s.startsWith "graph::" then
    { asString := s.drop ("graph::".length) }
  else
    canon

end Lens
end LoF
end HeytingLean

