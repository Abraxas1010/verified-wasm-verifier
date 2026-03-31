import HeytingLean.Embeddings.LensRegistry
import HeytingLean.Embeddings.CoreLenses
import HeytingLean.Embeddings.Presets
import HeytingLean.Embeddings.Adelic
import HeytingLean.Embeddings.CrossLensTransport
import HeytingLean.Embeddings.LensUnification
import HeytingLean.Embeddings.PerspectivalDescentCarrier
import HeytingLean.Embeddings.PerspectivalDescentHierarchy
import HeytingLean.Embeddings.PDCExtensions
import HeytingLean.Embeddings.PDCOverview

/-!
# Lens Registry - Complete Import

Import this module to get the full extensible lens registry system:
- `LensRegistry`: Core typeclass infrastructure
- `CoreLenses`: 71 core lens tags
- `Presets`: Domain-specific preset configurations
- `Adelic`: Original adelic structure (for backwards compatibility)
- `CrossLensTransport`: Multi-lens coordination

## Quick Start

```lean
import HeytingLean.Embeddings.LensAll

open HeytingLean.Embeddings

-- Use a preset
def myLenses := LensPreset.quantum

-- Or select by domain
def autoLenses := selectLensesFor "crypto"

-- Or custom selection
def customLenses := LensSet.ofList [.tensor, .graph, .surreal, .zkProof]
```
-/
