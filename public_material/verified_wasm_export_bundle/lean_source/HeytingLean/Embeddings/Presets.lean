import HeytingLean.Embeddings.CoreLenses

/-!
# Lens Presets

Pre-configured lens sets for common use cases. These provide sensible defaults
for different problem domains while allowing full customization.

## Available Presets

- **minimal**: Just omega + tensor + graph (3 lenses)
- **standard**: Foundational lenses (6 lenses)
- **extended**: Foundational + generative (12 lenses)
- **full**: All 100 core lenses
- **quantum**: Quantum computing focused (7 lenses)
- **crypto**: Cryptographic applications (7 lenses)
- **ml**: Machine learning / neural networks (10 lenses)
- **physics**: Physical systems (13 lenses)
- **proofs**: Theorem proving / ATP (10 lenses)
- **finance**: Financial modeling (8 lenses)
- **categorical**: Category theory / topos (13 lenses)
- **concurrency**: Process algebra / concurrent (8 lenses)
- **biology**: Biological / emergence (8 lenses)
- **hardware**: PCB / hardware lenses (6 lenses)
- **diffGeometry**: Differential geometry and gauge theory (8 lenses)
- **tda**: Topological data analysis (7 lenses)
- **transport**: Optimal transport / Wasserstein analysis (6 lenses)
- **signalProcessing**: Signal and harmonic analysis (7 lenses)
- **automataTheory**: Coalgebra and automata analysis (7 lenses)
- **games**: Game theory and mechanism design (7 lenses)

## Usage

```lean
-- Use a preset
def myLenses := LensPreset.quantum

-- Combine presets
def combinedLenses := LensPreset.quantum.union LensPreset.crypto

-- Custom selection
def customLenses := LensSet.ofList [.tensor, .tropical, .zkProof]
```
-/

namespace HeytingLean
namespace Embeddings

open CoreLensTag

/-! ## Preset Lens Configurations -/

namespace LensPreset

/-- Minimal lens set: just the essential three.
    Good for quick computations where full multi-lens isn't needed. -/
def minimal : LensSet CoreLensTag :=
  LensSet.ofList [.omega, .tensor, .graph]

/-- Standard lens set: the 6 foundational lenses.
    Balanced coverage for general-purpose use. -/
def standard : LensSet CoreLensTag :=
  LensSet.ofList foundationalLenses

/-- Extended standard: foundational + generative stack.
    Good for exploring computational structures. -/
def extended : LensSet CoreLensTag :=
  LensSet.ofList (foundationalLenses ++ generativeLenses)

/-- Full lens set: all 100 core lenses.
    Maximum coverage, higher computational cost. -/
def full : LensSet CoreLensTag :=
  LensSet.ofList CoreLensTag.all

/-! ### Domain-Specific Presets -/

/-- Quantum computing preset.
    Optimized for quantum algorithms, circuits, and measurements. -/
def quantum : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,        -- Base eigenform
    .tensor,       -- Tensor products
    .density,      -- Mixed states
    .bloch,        -- Qubit geometry
    .circuit,      -- Quantum circuits
    .contextuality, -- Non-classical correlations
    .oml           -- Quantum logic
  ]

/-- Cryptographic applications preset.
    For ZK proofs, FHE, and post-quantum cryptography. -/
def crypto : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,    -- Base
    .tensor,   -- Linear algebra
    .zkProof,  -- Zero-knowledge
    .fhe,      -- Homomorphic encryption
    .lattice,  -- Post-quantum
    .boolLens, -- Boolean circuits
    .plonk     -- SNARK protocol
  ]

/-- Machine learning / neural networks preset.
    For training, inference, and neural architecture analysis. -/
def ml : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,     -- Base eigenform
    .tensor,    -- Tensor operations (core)
    .tropical,  -- ReLU / max-plus
    .flow,      -- Computational flow
    .graph,     -- Network structure
    .activeInf, -- Active inference / FEP
    .fourier,   -- Spectral methods
    .wavelet,   -- Signal processing
    .matrix,    -- Matrix operations
    .absInt     -- Abstract interpretation
  ]

/-- Physical systems preset.
    For physics simulations and theoretical physics. -/
def physics : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,      -- Base
    .tensor,     -- Tensor fields
    .spinGlass,  -- Statistical mechanics
    .string,     -- String theory
    .assembly,   -- Complexity measures
    .topology,   -- Topological invariants
    .riemannian, -- Geometry
    .renormGroup, -- RG flow
    .conformal,  -- CFT
    .wolfram,    -- Hypergraph physics
    .quantumInfo, -- Quantum information
    .holographic, -- Holographic principle
    .spectral    -- Spectral analysis
  ]

/-- Theorem proving / ATP preset.
    For automated theorem proving and proof search. -/
def proofs : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,       -- Base eigenform
    .tensor,      -- Spectral analysis
    .graph,       -- Proof graphs
    .typeTheory,  -- Type-theoretic proofs
    .modal,       -- Modal reasoning
    .fca,         -- Concept lattices
    .homotopy,    -- HoTT
    .lambda,      -- Lambda calculus
    .leanCore,    -- Lean type theory
    .rewriting    -- Term rewriting
  ]

/-- Financial modeling preset.
    For quantitative finance and risk analysis. -/
def finance : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,      -- Base
    .tensor,     -- Portfolio matrices
    .flow,       -- Cash flows
    .causal,     -- Causal models
    .tropical,   -- Optimization
    .graph,      -- Network effects
    .kelly,      -- Optimal betting
    .defi        -- DeFi protocols
  ]

/-- Category theory / abstract math preset.
    For categorical constructions and abstract algebra. -/
def categorical : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,       -- Eigenforms as universal
    .typeTheory,  -- Types as objects
    .fca,         -- Galois connections
    .modal,       -- Modalities
    .topology,    -- Topoi structure
    .ordinal,     -- Transfinite
    .sheafLT,     -- Lawvere-Tierney
    .groupoid,    -- Groupoids
    .chainComplex, -- Homological
    .homotopy,    -- HoTT
    .simplicial,  -- Simplicial homotopy
    .topos,       -- Topos theory
    .derivedCat   -- Derived categories
  ]

/-- Process algebra / concurrency preset.
    For concurrent systems and process calculi. -/
def concurrency : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,     -- Base
    .process,   -- Process algebra
    .causal,    -- Happens-before
    .flow,      -- Control flow
    .graph,     -- State graphs
    .modal,     -- Temporal logic
    .cybernetic, -- Feedback control
    .petriNet   -- Petri nets
  ]

/-- Biological / emergence preset.
    For biological systems and emergence phenomena. -/
def biology : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,      -- Self-reference
    .assembly,   -- Complexity / life detection
    .flow,       -- Metabolic flows
    .graph,      -- Networks
    .activeInf,  -- Free energy principle
    .causal,     -- Causal mechanisms
    .emergence,  -- Emergence metrics
    .probability -- Probabilistic models
  ]

/-- Hardware / PCB preset.
    For physical computation board representations. -/
def hardware : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,      -- Base
    .tensor,     -- Tensor operations
    .pcbSingle,  -- Single board
    .pcbMulti,   -- Multi-board
    .pcbDistance, -- Distance metrics
    .lensIR      -- Compiled IR
  ]

/-- Information theory preset.
    For information-theoretic analysis. -/
def information : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,       -- Base
    .tensor,      -- Matrix info
    .probability, -- Probability
    .infoTrace,   -- Info flow
    .holographic, -- Holographic
    .infoTheory,  -- Entropy
    .trace        -- Execution traces
  ]

/-- Topological preset.
    For topological and homological analysis. -/
def topological : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,        -- Base
    .topology,     -- Topological invariants
    .locSys,       -- Local systems
    .chainComplex, -- Chain complexes
    .jRatchet,     -- J-ratchet
    .knot,         -- Knot invariants
    .spectral,     -- Spectral
    .dimLens       -- Dimensional
  ]

/-- Bridge operations preset.
    For cross-representational transport. -/
def bridges : LensSet CoreLensTag :=
  LensSet.ofList [
    .tensorIntensity,
    .graphAlexandroff,
    .cliffordProjector,
    .cliffordCommutant,
    .geometric,
    .ctGraph,
    .ctTensor,
    .ctQuantum,
    .emergence
  ]

/-- Differential geometry preset.
    For fiber bundles, gauge theory, and geometric analysis. -/
def diffGeometry : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,       -- Base eigenform
    .tensor,      -- Tensor fields
    .fiberBundle, -- Fiber bundles
    .gauge,       -- Gauge fields
    .riemannian,  -- Riemannian metrics
    .symplectic,  -- Symplectic structure
    .topology,    -- Topological invariants
    .clifford     -- Clifford algebra
  ]

/-- Topological data analysis preset.
    For persistent homology and shape analysis. -/
def tda : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,       -- Base
    .topology,    -- Topological invariants
    .persistence, -- Persistent homology
    .mapper,      -- Mapper graphs
    .morse,       -- Morse theory
    .graph,       -- Network structure
    .chainComplex -- Homological chains
  ]

/-- Optimal transport / distribution preset.
    For measure-theoretic and distributional analysis. -/
def transport : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,       -- Base
    .wasserstein, -- Wasserstein distance
    .ot,          -- Optimal transport
    .probability, -- Probability distributions
    .flow,        -- Flow networks
    .fisher       -- Fisher information
  ]

/-- Signal processing / harmonic analysis preset.
    For Fourier, wavelet, and spectral methods. -/
def signalProcessing : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,     -- Base
    .fourier,   -- Fourier transform
    .wavelet,   -- Wavelets
    .laplacian, -- Laplacian
    .spectral,  -- Spectral analysis
    .tensor,    -- Tensor products
    .graph      -- Graph structure
  ]

/-- Automata / formal language preset.
    For automata theory and formal verification. -/
def automataTheory : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,     -- Base
    .automaton, -- Finite automata
    .coalgebra, -- Coalgebraic structure
    .stream,    -- Coinductive streams
    .rewriting, -- Term rewriting
    .modal,     -- Temporal/modal logic
    .graph      -- State graphs
  ]

/-- Game theory / mechanism design preset.
    For strategic interaction and incentive design. -/
def games : LensSet CoreLensTag :=
  LensSet.ofList [
    .omega,       -- Base
    .gameTheory,  -- Nash equilibria
    .auction,     -- Mechanism design
    .probability, -- Probabilistic strategies
    .flow,        -- Network flows
    .kelly,       -- Optimal betting
    .causal       -- Causal inference
  ]

end LensPreset

/-! ## Preset Metadata -/

/-- Metadata about a preset for documentation. -/
structure PresetInfo where
  /-- Name of the preset -/
  name : String
  /-- Brief description -/
  description : String
  /-- Number of lenses -/
  count : ℕ
  /-- Use cases -/
  useCases : List String

namespace PresetInfo

def minimal : PresetInfo :=
  { name := "minimal"
    description := "Essential three lenses for quick computations"
    count := 3
    useCases := ["Simple problems", "Testing", "Low-overhead"] }

def standard : PresetInfo :=
  { name := "standard"
    description := "Foundational six lenses for general use"
    count := 6
    useCases := ["General purpose", "Balanced coverage", "Default"] }

def extended : PresetInfo :=
  { name := "extended"
    description := "Foundational plus generative stack"
    count := 12
    useCases := ["Computational exploration", "Number systems", "Combinators"] }

def full : PresetInfo :=
  { name := "full"
    description := "All 100 core lenses for maximum coverage"
    count := 100
    useCases := ["Comprehensive analysis", "Research", "Exploration"] }

def quantum : PresetInfo :=
  { name := "quantum"
    description := "Quantum computing focused lenses"
    count := 7
    useCases := ["Quantum algorithms", "Circuits", "Measurements"] }

def crypto : PresetInfo :=
  { name := "crypto"
    description := "Cryptographic application lenses"
    count := 7
    useCases := ["ZK proofs", "FHE", "Post-quantum", "SNARKs"] }

def ml : PresetInfo :=
  { name := "ml"
    description := "Machine learning / neural network lenses"
    count := 10
    useCases := ["Training", "Inference", "Architecture analysis"] }

def physics : PresetInfo :=
  { name := "physics"
    description := "Physical systems lenses"
    count := 13
    useCases := ["Simulations", "String theory", "Statistical mechanics"] }

def proofs : PresetInfo :=
  { name := "proofs"
    description := "Theorem proving and ATP lenses"
    count := 10
    useCases := ["Proof search", "Lane-changing ATP", "Verification"] }

def finance : PresetInfo :=
  { name := "finance"
    description := "Financial modeling lenses"
    count := 8
    useCases := ["Portfolio", "Risk analysis", "DeFi", "Kelly criterion"] }

def categorical : PresetInfo :=
  { name := "categorical"
    description := "Category theory / abstract math lenses"
    count := 13
    useCases := ["Topos theory", "HoTT", "Galois connections"] }

def concurrency : PresetInfo :=
  { name := "concurrency"
    description := "Process algebra / concurrency lenses"
    count := 8
    useCases := ["CSP/CCS", "Temporal logic", "Feedback systems"] }

def biology : PresetInfo :=
  { name := "biology"
    description := "Biological / emergence lenses"
    count := 8
    useCases := ["Life detection", "Metabolic flows", "FEP"] }

def hardware : PresetInfo :=
  { name := "hardware"
    description := "PCB / hardware computation lenses"
    count := 6
    useCases := ["Physical boards", "Distance metrics", "Compiled IR"] }

def information : PresetInfo :=
  { name := "information"
    description := "Information theory lenses"
    count := 7
    useCases := ["Entropy", "Info flow", "Holographic"] }

def topological : PresetInfo :=
  { name := "topological"
    description := "Topological / homological lenses"
    count := 8
    useCases := ["Homology", "Knot theory", "Local systems"] }

def bridges : PresetInfo :=
  { name := "bridges"
    description := "Cross-representational transport lenses"
    count := 9
    useCases := ["Lane changing", "Multi-lens coordination"] }

def diffGeometry : PresetInfo :=
  { name := "diffGeometry"
    description := "Differential geometry and gauge theory lenses"
    count := 8
    useCases := ["Fiber bundles", "Gauge theory", "Riemannian geometry"] }

def tda : PresetInfo :=
  { name := "tda"
    description := "Topological data analysis lenses"
    count := 7
    useCases := ["Persistent homology", "Shape analysis", "Barcodes"] }

def transport : PresetInfo :=
  { name := "transport"
    description := "Optimal transport / distribution lenses"
    count := 6
    useCases := ["Wasserstein distance", "Optimal transport", "Distribution comparison"] }

def signalProcessing : PresetInfo :=
  { name := "signalProcessing"
    description := "Signal processing and harmonic analysis lenses"
    count := 7
    useCases := ["Fourier analysis", "Wavelets", "Spectral methods"] }

def automataTheory : PresetInfo :=
  { name := "automataTheory"
    description := "Automata theory and formal language lenses"
    count := 7
    useCases := ["Finite automata", "Coinduction", "Formal verification"] }

def games : PresetInfo :=
  { name := "games"
    description := "Game theory and mechanism design lenses"
    count := 7
    useCases := ["Nash equilibria", "Auctions", "Strategic interaction"] }

end PresetInfo

/-! ## Dynamic Lens Selection -/

/-- Select lenses based on problem domain string. -/
def selectLensesFor (domain : String) : LensSet CoreLensTag :=
  match domain.toLower with
  | "quantum" | "qc" | "qubit" => LensPreset.quantum
  | "crypto" | "zk" | "fhe" | "snark" => LensPreset.crypto
  | "ml" | "neural" | "nn" | "deep" | "ai" => LensPreset.ml
  | "physics" | "phys" | "string" => LensPreset.physics
  | "proofs" | "atp" | "proving" | "theorem" => LensPreset.proofs
  | "finance" | "quant" | "defi" | "kelly" => LensPreset.finance
  | "category" | "cat" | "abstract" | "topos" => LensPreset.categorical
  | "concurrent" | "process" | "csp" | "ccs" => LensPreset.concurrency
  | "biology" | "bio" | "life" | "emergence" => LensPreset.biology
  | "hardware" | "pcb" | "board" => LensPreset.hardware
  | "information" | "info" | "entropy" => LensPreset.information
  | "topological" | "topo" | "homology" | "knot" => LensPreset.topological
  | "diffgeometry" | "geometry" | "gauge" | "bundle" => LensPreset.diffGeometry
  | "tda" | "persistence" | "barcode" | "mapper" => LensPreset.tda
  | "transport" | "wasserstein" | "ot" => LensPreset.transport
  | "signal" | "fourier" | "wavelet" | "harmonic" => LensPreset.signalProcessing
  | "automata" | "automaton" | "coalgebra" | "stream" => LensPreset.automataTheory
  | "games" | "game" | "nash" | "mechanism" | "auction" => LensPreset.games
  | "bridges" | "cross" => LensPreset.bridges
  | "minimal" | "min" => LensPreset.minimal
  | "standard" | "default" => LensPreset.standard
  | "extended" | "ext" => LensPreset.extended
  | "full" | "all" => LensPreset.full
  | _ => LensPreset.standard  -- Default to standard

/-- Combine multiple domain presets. -/
def combinePresets (domains : List String) : LensSet CoreLensTag :=
  domains.foldl (fun acc d => acc ∪ selectLensesFor d) (LensSet.ofList [])

/-- Get all presets as a list of (name, lens set) pairs. -/
def allPresets : List (String × LensSet CoreLensTag) :=
  [ ("minimal", LensPreset.minimal)
  , ("standard", LensPreset.standard)
  , ("extended", LensPreset.extended)
  , ("full", LensPreset.full)
  , ("quantum", LensPreset.quantum)
  , ("crypto", LensPreset.crypto)
  , ("ml", LensPreset.ml)
  , ("physics", LensPreset.physics)
  , ("proofs", LensPreset.proofs)
  , ("finance", LensPreset.finance)
  , ("categorical", LensPreset.categorical)
  , ("concurrency", LensPreset.concurrency)
  , ("biology", LensPreset.biology)
  , ("hardware", LensPreset.hardware)
  , ("information", LensPreset.information)
  , ("topological", LensPreset.topological)
  , ("diffGeometry", LensPreset.diffGeometry)
  , ("tda", LensPreset.tda)
  , ("transport", LensPreset.transport)
  , ("signalProcessing", LensPreset.signalProcessing)
  , ("automataTheory", LensPreset.automataTheory)
  , ("games", LensPreset.games)
  , ("bridges", LensPreset.bridges)
  ]

end Embeddings
end HeytingLean
