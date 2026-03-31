import HeytingLean.Embeddings.LensRegistry

/-!
# Core Lens Tags

This module defines all discovered lens tags in HeytingLean.
Based on comprehensive audit: 54+ lens files, 47+ encode/decode implementations.

## Categories

1. **Foundational** (6): omega, tensor, graph, clifford, topology, matula
2. **Generative Stack** (6): surreal, combinator, typeTheory, ordinal, lambda, leanCore
3. **Quantum** (7): density, bloch, circuit, contextuality, activeInf, vacuum, oml
4. **Algebraic** (8): tropical, tropicalDiff, modal, fca, sheafLT, operad, profunctor, kTheory
5. **Process/Flow** (7): process, causal, flow, cybernetic, rewriting, petriNet, symbDyn
6. **Cryptographic** (5): zkProof, fhe, lattice, boolLens, plonk
7. **Physical** (7): assembly, spinGlass, string, wolfram, quantumInfo, renormGroup, conformal
8. **Topological/Categorical** (11): locSys, chainComplex, groupoid, jRatchet, knot, spectral, dimLens, homotopy, simplicial, topos, derivedCat
9. **Information** (6): probability, infoTrace, holographic, infoTheory, kolmogorov, fisher
10. **Bridge Variants** (9): tensorIntensity, graphAlexandroff, cliffordProjector, cliffordCommutant, geometric, ctGraph, ctTensor, ctQuantum, emergence
11. **PCB/Hardware** (4): pcbSingle, pcbMulti, pcbDistance, lensIR
12. **Economic** (4): kelly, defi, gameTheory, auction
13. **Representation** (2): matrix, radial
14. **Utility** (3): trace, truncation, absInt
15. **Differential Geometry** (4): fiberBundle, gauge, riemannian, symplectic
16. **Topological Data Analysis** (3): persistence, mapper, morse
17. **Coalgebraic/Coinductive** (3): coalgebra, stream, automaton
18. **Optimal Transport** (2): wasserstein, ot
19. **Signal/Harmonic** (3): fourier, wavelet, laplacian

Total: 100 core lenses

## Extensibility

Domain-specific lens sets can extend beyond these core lenses by defining
their own `LensTag` instances. See `QuantumLenses`, `CryptoLenses`, etc.
-/

namespace HeytingLean
namespace Embeddings

/-! ## Core Lens Tag Enum -/

/-- Core lens tags covering all discovered representational domains.

These are the "built-in" lenses that are always available. Domain-specific
extensions can add more via separate `LensTag` instances. -/
inductive CoreLensTag where
  -- ### Foundational Lenses (6)

  /-- LoF eigenform / re-entry: the primordial self-referential structure.
      Fixed points of the R-nucleus. -/
  | omega

  /-- Tensor / eigenvalue representation: spectral decomposition view.
      Maps Ω_R elements to eigenvalue spectra. -/
  | tensor

  /-- Spectral graph representation: adjacency / Laplacian view.
      Maps Ω_R elements to graph structures. -/
  | graph

  /-- Clifford algebra representation: grade-based decomposition.
      Uses geometric algebra structure. -/
  | clifford

  /-- Topological invariants: homology, Betti numbers, connectivity.
      Captures topological essence. -/
  | topology

  /-- Matula arborification representation: rooted-tree encoding via primes.
      Bridges executable Matula encode/decode with lens transport. -/
  | matula

  -- ### Generative Stack Lenses (6)

  /-- Surreal number representation: games as ordered pairs.
      Conway's surreal construction. -/
  | surreal

  /-- SKY combinator basis: S, K, Y combinatorial logic.
      Functional / applicative structure. -/
  | combinator

  /-- Type theory representation: MLTT, dependent types.
      Propositions-as-types view. -/
  | typeTheory

  /-- Ordinal number representation: well-ordered sets.
      Transfinite structure. -/
  | ordinal

  /-- Lambda calculus representation: pure lambda terms.
      Church-style functional encoding. -/
  | lambda

  /-- Lean core type theory: Lean's kernel type system.
      CIC-based representation. -/
  | leanCore

  -- ### Quantum Lenses (7)

  /-- Density matrix representation: mixed quantum states.
      Positive trace-class operators. -/
  | density

  /-- Bloch sphere representation: pure qubit states.
      S² geometric view. -/
  | bloch

  /-- Quantum circuit representation: gates and measurements.
      Computational view. -/
  | circuit

  /-- Contextual valuations: Kochen-Specker / sheaf view.
      Non-classical truth assignments. -/
  | contextuality

  /-- Active inference: free energy minimization view.
      Bayesian brain / FEP. -/
  | activeInf

  /-- Vacuum state representation: ground states.
      Surreal vacuum encoding. -/
  | vacuum

  /-- Orthomodular lattice representation.
      Quantum logic structure. -/
  | oml

  -- ### Algebraic Lenses (8)

  /-- Tropical (max-plus) semiring: optimization view.
      Shortest paths, dynamic programming. -/
  | tropical

  /-- Tropical differential: differentiation in tropical setting.
      Tropical calculus. -/
  | tropicalDiff

  /-- Modal logic operators: necessity / possibility.
      Kripke semantics view. -/
  | modal

  /-- Formal Concept Analysis: concept lattices.
      Galois connection view. -/
  | fca

  /-- Sheaf Lawvere-Tierney representation.
      Topos-theoretic modalities. -/
  | sheafLT

  /-- Operad / multicategory composition structure.
      Higher algebraic operations. -/
  | operad

  /-- Profunctor / bimodule / distributor.
      Generalized relations between categories. -/
  | profunctor

  /-- Algebraic/topological K-theory.
      Vector bundle classification. -/
  | kTheory

  -- ### Process / Flow Lenses (7)

  /-- Process algebra: CCS / CSP style.
      Concurrent computation view. -/
  | process

  /-- Causal DAG representation: directed acyclic graphs.
      Causal inference view. -/
  | causal

  /-- Flow network representation: max-flow / min-cut.
      Network optimization view. -/
  | flow

  /-- Cybernetic feedback systems.
      Control theory view. -/
  | cybernetic

  /-- Rewriting systems representation.
      Term rewriting / reduction. -/
  | rewriting

  /-- Petri net / marking / firing sequence.
      Concurrent system modeling. -/
  | petriNet

  /-- Shift space / symbolic coding / subshifts.
      Dynamical system encoding. -/
  | symbDyn

  -- ### Cryptographic Lenses (5)

  /-- Zero-knowledge proof representation: R1CS / Plonk.
      Verifiable computation view. -/
  | zkProof

  /-- Fully homomorphic encryption: encrypted computation.
      Privacy-preserving view. -/
  | fhe

  /-- Lattice-based cryptography: LWE / Ring-LWE.
      Post-quantum view. -/
  | lattice

  /-- Boolean lens for crypto VM.
      Boolean circuit representation. -/
  | boolLens

  /-- Plonk verifier representation.
      SNARK protocol view. -/
  | plonk

  -- ### Physical Lenses (7)

  /-- Assembly theory: J-depth / construction steps.
      Complexity measure view. -/
  | assembly

  /-- Spin glass representation: disordered magnetic systems.
      Statistical physics view. -/
  | spinGlass

  /-- String theory representation: worldsheet / target space.
      High-energy physics view. -/
  | string

  /-- Wolfram physics model representation.
      Hypergraph rewriting view. -/
  | wolfram

  /-- Quantum information bridge.
      Quantum info theory view. -/
  | quantumInfo

  /-- RG flow / fixed points / universality.
      Renormalization group structure. -/
  | renormGroup

  /-- Conformal field theory / Virasoro algebra.
      Scale-invariant quantum fields. -/
  | conformal

  -- ### Topological / Categorical Lenses (11)

  /-- Local systems representation.
      Locally constant sheaves. -/
  | locSys

  /-- Chain complex representation.
      Homological algebra view. -/
  | chainComplex

  /-- Groupoid representation.
      Category with invertible morphisms. -/
  | groupoid

  /-- J-ratchet topology representation.
      Nucleus-induced topology. -/
  | jRatchet

  /-- Knot invariant representation.
      Topological knot theory. -/
  | knot

  /-- Spectral analysis representation.
      Eigenvalue/eigenvector analysis. -/
  | spectral

  /-- Dimensional lens representation.
      HoTT dimension tracking. -/
  | dimLens

  /-- Homotopy type representation.
      HoTT path types. -/
  | homotopy

  /-- Simplicial set / nerve / Kan complex.
      Combinatorial homotopy theory. -/
  | simplicial

  /-- Topos / subobject classifier / internal language.
      Generalized space / logic duality. -/
  | topos

  /-- Derived category / triangulated structure.
      Homological algebra localization. -/
  | derivedCat

  -- ### Information-Theoretic Lenses (6)

  /-- Probabilistic nucleus representation.
      Probability distributions. -/
  | probability

  /-- Information trace representation.
      Information flow tracking. -/
  | infoTrace

  /-- Holographic screen representation.
      Holographic principle encoding. -/
  | holographic

  /-- Information theory representation.
      Entropy / mutual information. -/
  | infoTheory

  /-- Kolmogorov complexity / algorithmic information.
      Incompressible information content. -/
  | kolmogorov

  /-- Fisher information metric / natural gradient.
      Information geometry. -/
  | fisher

  -- ### Bridge Variant Lenses (9)

  /-- Tensor intensity variant.
      Intensity-based tensor encoding. -/
  | tensorIntensity

  /-- Graph Alexandroff variant.
      Alexandroff topology on graphs. -/
  | graphAlexandroff

  /-- Clifford projector variant.
      Projector-based Clifford encoding. -/
  | cliffordProjector

  /-- Clifford commutant variant.
      Commutant subalgebra view. -/
  | cliffordCommutant

  /-- Geometric algebra representation.
      General geometric algebra view. -/
  | geometric

  /-- Category-to-Graph bridge.
      Categorical structure as graph. -/
  | ctGraph

  /-- Category-to-Tensor bridge.
      Categorical structure as tensor. -/
  | ctTensor

  /-- Category-to-Quantum bridge.
      Categorical structure as quantum. -/
  | ctQuantum

  /-- Emergence metrics representation.
      Emergence / complexity measures. -/
  | emergence

  -- ### PCB / Hardware Lenses (4)

  /-- PCB single-board representation.
      Single physical computation board. -/
  | pcbSingle

  /-- PCB multi-board representation.
      Multiple physical computation boards. -/
  | pcbMulti

  /-- PCB distance metrics.
      Distance on physical boards. -/
  | pcbDistance

  /-- Compiled lens IR representation.
      Intermediate representation for compiled lenses. -/
  | lensIR

  -- ### Economic Lenses (4)

  /-- Kelly criterion representation.
      Optimal betting / portfolio. -/
  | kelly

  /-- DeFi protocol representation.
      Decentralized finance structures. -/
  | defi

  /-- Nash equilibrium / strategy profile.
      Game-theoretic solution concept. -/
  | gameTheory

  /-- Mechanism design / auction theory.
      Incentive-compatible structures. -/
  | auction

  -- ### Representation Lenses (2)

  /-- Matrix representation.
      Linear algebra / matrices. -/
  | matrix

  /-- Radial representation.
      Radial / ring-based encoding. -/
  | radial

  -- ### Utility Lenses (3)

  /-- Execution trace representation.
      Computation traces. -/
  | trace

  /-- Truncation / approximation representation.
      Bounded approximations. -/
  | truncation

  /-- Abstract interpretation representation.
      Static analysis domains. -/
  | absInt

  -- ### Differential Geometry Lenses (4) — NEW

  /-- Fiber bundle with connection and curvature.
      Gauge-theoretic and topological structure. -/
  | fiberBundle

  /-- Gauge field / principal bundle connection.
      Yang-Mills structure. -/
  | gauge

  /-- Riemannian metric tensor / geodesic structure.
      Intrinsic geometry. -/
  | riemannian

  /-- Symplectic manifold / Hamiltonian mechanics.
      Phase space structure. -/
  | symplectic

  -- ### TDA Lenses (3) — NEW

  /-- Persistent homology barcodes / diagrams.
      Topological data analysis filtrations. -/
  | persistence

  /-- Mapper / Reeb graph approximation.
      TDA shape summarization. -/
  | mapper

  /-- Morse function critical points / handle decomposition.
      Smooth topology via critical values. -/
  | morse

  -- ### Coalgebraic / Coinductive Lenses (3) — NEW

  /-- F-coalgebra / final coalgebra / bisimulation.
      Coinductive behavioral structure. -/
  | coalgebra

  /-- Coinductive streams / infinite sequences.
      Productive corecursion. -/
  | stream

  /-- Deterministic/nondeterministic finite automata.
      Regular language recognition. -/
  | automaton

  -- ### Optimal Transport Lenses (2) — NEW

  /-- Wasserstein / earth mover's distance.
      Measure-theoretic optimal coupling. -/
  | wasserstein

  /-- Optimal transport plan / Monge map.
      Mass transportation structure. -/
  | ot

  -- ### Signal / Harmonic Lenses (3) — NEW

  /-- Fourier transform / spectral decomposition.
      Frequency-domain representation. -/
  | fourier

  /-- Wavelet transform / multiresolution analysis.
      Time-frequency localization. -/
  | wavelet

  /-- Graph/manifold Laplacian / diffusion kernel.
      Spectral geometry. -/
  | laplacian

  deriving DecidableEq, Repr, Inhabited

namespace CoreLensTag

/-! ## LensTag Instance -/

/-- Human-readable names for core lenses. -/
def nameOf : CoreLensTag → String
  -- Foundational
  | .omega           => "Omega (Eigenform)"
  | .tensor          => "Tensor"
  | .graph           => "Graph"
  | .clifford        => "Clifford"
  | .topology        => "Topology"
  | .matula          => "Matula Arborification"
  -- Generative
  | .surreal         => "Surreal"
  | .combinator      => "Combinator (SKY)"
  | .typeTheory      => "Type Theory"
  | .ordinal         => "Ordinal"
  | .lambda          => "Lambda Calculus"
  | .leanCore        => "Lean Core"
  -- Quantum
  | .density         => "Density Matrix"
  | .bloch           => "Bloch Sphere"
  | .circuit         => "Quantum Circuit"
  | .contextuality   => "Contextuality"
  | .activeInf       => "Active Inference"
  | .vacuum          => "Vacuum State"
  | .oml             => "Orthomodular Lattice"
  -- Algebraic
  | .tropical        => "Tropical"
  | .tropicalDiff    => "Tropical Differential"
  | .modal           => "Modal"
  | .fca             => "Formal Concept Analysis"
  | .sheafLT         => "Sheaf Lawvere-Tierney"
  | .operad          => "Operad"
  | .profunctor      => "Profunctor"
  | .kTheory         => "K-Theory"
  -- Process
  | .process         => "Process Algebra"
  | .causal          => "Causal DAG"
  | .flow            => "Flow Network"
  | .cybernetic      => "Cybernetic"
  | .rewriting       => "Rewriting"
  | .petriNet        => "Petri Net"
  | .symbDyn         => "Symbolic Dynamics"
  -- Crypto
  | .zkProof         => "ZK Proof"
  | .fhe             => "FHE"
  | .lattice         => "Lattice Crypto"
  | .boolLens        => "Boolean Lens"
  | .plonk           => "Plonk"
  -- Physical
  | .assembly        => "Assembly Theory"
  | .spinGlass       => "Spin Glass"
  | .string          => "String Theory"
  | .wolfram         => "Wolfram Physics"
  | .quantumInfo     => "Quantum Info"
  | .renormGroup     => "Renormalization Group"
  | .conformal       => "Conformal Field"
  -- Topological
  | .locSys          => "Local Systems"
  | .chainComplex    => "Chain Complex"
  | .groupoid        => "Groupoid"
  | .jRatchet        => "J-Ratchet"
  | .knot            => "Knot Invariants"
  | .spectral        => "Spectral"
  | .dimLens         => "Dimensional"
  | .homotopy        => "Homotopy"
  | .simplicial      => "Simplicial Set"
  | .topos           => "Topos"
  | .derivedCat      => "Derived Category"
  -- Information
  | .probability     => "Probability"
  | .infoTrace       => "Info Trace"
  | .holographic     => "Holographic"
  | .infoTheory      => "Info Theory"
  | .kolmogorov      => "Kolmogorov Complexity"
  | .fisher          => "Fisher Information"
  -- Bridges
  | .tensorIntensity   => "Tensor Intensity"
  | .graphAlexandroff  => "Graph Alexandroff"
  | .cliffordProjector => "Clifford Projector"
  | .cliffordCommutant => "Clifford Commutant"
  | .geometric         => "Geometric"
  | .ctGraph           => "CT Graph"
  | .ctTensor          => "CT Tensor"
  | .ctQuantum         => "CT Quantum"
  | .emergence         => "Emergence"
  -- PCB
  | .pcbSingle       => "PCB Single"
  | .pcbMulti        => "PCB Multi"
  | .pcbDistance     => "PCB Distance"
  | .lensIR          => "Lens IR"
  -- Economic
  | .kelly           => "Kelly Criterion"
  | .defi            => "DeFi"
  | .gameTheory      => "Game Theory"
  | .auction         => "Auction / Mechanism"
  -- Representation
  | .matrix          => "Matrix"
  | .radial          => "Radial"
  -- Utility
  | .trace           => "Trace"
  | .truncation      => "Truncation"
  | .absInt          => "Abstract Interpretation"
  -- Differential Geometry
  | .fiberBundle     => "Fiber Bundle"
  | .gauge           => "Gauge Field"
  | .riemannian      => "Riemannian Metric"
  | .symplectic      => "Symplectic"
  -- TDA
  | .persistence     => "Persistent Homology"
  | .mapper          => "Mapper Graph"
  | .morse           => "Morse Theory"
  -- Coalgebraic
  | .coalgebra       => "Coalgebra"
  | .stream          => "Stream"
  | .automaton       => "Automaton"
  -- Optimal Transport
  | .wasserstein     => "Wasserstein Distance"
  | .ot              => "Optimal Transport"
  -- Signal/Harmonic
  | .fourier         => "Fourier Transform"
  | .wavelet         => "Wavelet"
  | .laplacian       => "Laplacian"

/-- Unique identifiers for serialization. -/
def idOf : CoreLensTag → String
  -- Foundational
  | .omega           => "core.omega"
  | .tensor          => "core.tensor"
  | .graph           => "core.graph"
  | .clifford        => "core.clifford"
  | .topology        => "core.topology"
  | .matula          => "core.matula"
  -- Generative
  | .surreal         => "core.surreal"
  | .combinator      => "core.combinator"
  | .typeTheory      => "core.typeTheory"
  | .ordinal         => "core.ordinal"
  | .lambda          => "core.lambda"
  | .leanCore        => "core.leanCore"
  -- Quantum
  | .density         => "core.density"
  | .bloch           => "core.bloch"
  | .circuit         => "core.circuit"
  | .contextuality   => "core.contextuality"
  | .activeInf       => "core.activeInf"
  | .vacuum          => "core.vacuum"
  | .oml             => "core.oml"
  -- Algebraic
  | .tropical        => "core.tropical"
  | .tropicalDiff    => "core.tropicalDiff"
  | .modal           => "core.modal"
  | .fca             => "core.fca"
  | .sheafLT         => "core.sheafLT"
  | .operad          => "core.operad"
  | .profunctor      => "core.profunctor"
  | .kTheory         => "core.kTheory"
  -- Process
  | .process         => "core.process"
  | .causal          => "core.causal"
  | .flow            => "core.flow"
  | .cybernetic      => "core.cybernetic"
  | .rewriting       => "core.rewriting"
  | .petriNet        => "core.petriNet"
  | .symbDyn         => "core.symbDyn"
  -- Crypto
  | .zkProof         => "core.zkProof"
  | .fhe             => "core.fhe"
  | .lattice         => "core.lattice"
  | .boolLens        => "core.boolLens"
  | .plonk           => "core.plonk"
  -- Physical
  | .assembly        => "core.assembly"
  | .spinGlass       => "core.spinGlass"
  | .string          => "core.string"
  | .wolfram         => "core.wolfram"
  | .quantumInfo     => "core.quantumInfo"
  | .renormGroup     => "core.renormGroup"
  | .conformal       => "core.conformal"
  -- Topological
  | .locSys          => "core.locSys"
  | .chainComplex    => "core.chainComplex"
  | .groupoid        => "core.groupoid"
  | .jRatchet        => "core.jRatchet"
  | .knot            => "core.knot"
  | .spectral        => "core.spectral"
  | .dimLens         => "core.dimLens"
  | .homotopy        => "core.homotopy"
  | .simplicial      => "core.simplicial"
  | .topos           => "core.topos"
  | .derivedCat      => "core.derivedCat"
  -- Information
  | .probability     => "core.probability"
  | .infoTrace       => "core.infoTrace"
  | .holographic     => "core.holographic"
  | .infoTheory      => "core.infoTheory"
  | .kolmogorov      => "core.kolmogorov"
  | .fisher          => "core.fisher"
  -- Bridges
  | .tensorIntensity   => "core.tensorIntensity"
  | .graphAlexandroff  => "core.graphAlexandroff"
  | .cliffordProjector => "core.cliffordProjector"
  | .cliffordCommutant => "core.cliffordCommutant"
  | .geometric         => "core.geometric"
  | .ctGraph           => "core.ctGraph"
  | .ctTensor          => "core.ctTensor"
  | .ctQuantum         => "core.ctQuantum"
  | .emergence         => "core.emergence"
  -- PCB
  | .pcbSingle       => "core.pcbSingle"
  | .pcbMulti        => "core.pcbMulti"
  | .pcbDistance     => "core.pcbDistance"
  | .lensIR          => "core.lensIR"
  -- Economic
  | .kelly           => "core.kelly"
  | .defi            => "core.defi"
  | .gameTheory      => "core.gameTheory"
  | .auction         => "core.auction"
  -- Representation
  | .matrix          => "core.matrix"
  | .radial          => "core.radial"
  -- Utility
  | .trace           => "core.trace"
  | .truncation      => "core.truncation"
  | .absInt          => "core.absInt"
  -- Differential Geometry
  | .fiberBundle     => "core.fiberBundle"
  | .gauge           => "core.gauge"
  | .riemannian      => "core.riemannian"
  | .symplectic      => "core.symplectic"
  -- TDA
  | .persistence     => "core.persistence"
  | .mapper          => "core.mapper"
  | .morse           => "core.morse"
  -- Coalgebraic
  | .coalgebra       => "core.coalgebra"
  | .stream          => "core.stream"
  | .automaton       => "core.automaton"
  -- Optimal Transport
  | .wasserstein     => "core.wasserstein"
  | .ot              => "core.ot"
  -- Signal/Harmonic
  | .fourier         => "core.fourier"
  | .wavelet         => "core.wavelet"
  | .laplacian       => "core.laplacian"

/-- Descriptions for documentation. -/
def descriptionOf : CoreLensTag → String
  -- Foundational
  | .omega           => "Laws of Form eigenform / re-entry fixed points"
  | .tensor          => "Tensor / eigenvalue spectral representation"
  | .graph           => "Spectral graph / adjacency representation"
  | .clifford        => "Clifford algebra grade decomposition"
  | .topology        => "Topological invariants (homology, Betti)"
  | .matula          => "Matula number/rooted-tree arborification representation"
  -- Generative
  | .surreal         => "Surreal number (Conway game) representation"
  | .combinator      => "SKY combinator basis (functional)"
  | .typeTheory      => "Type theory (MLTT, dependent types)"
  | .ordinal         => "Ordinal / well-ordered set representation"
  | .lambda          => "Lambda calculus (Church encoding)"
  | .leanCore        => "Lean core type theory (CIC)"
  -- Quantum
  | .density         => "Density matrix (mixed quantum states)"
  | .bloch           => "Bloch sphere (pure qubit states)"
  | .circuit         => "Quantum circuit (gates, measurements)"
  | .contextuality   => "Contextual valuations (Kochen-Specker)"
  | .activeInf       => "Active inference (free energy principle)"
  | .vacuum          => "Vacuum state (ground state encoding)"
  | .oml             => "Orthomodular lattice (quantum logic)"
  -- Algebraic
  | .tropical        => "Tropical (max-plus) semiring"
  | .tropicalDiff    => "Tropical differential calculus"
  | .modal           => "Modal logic (Kripke semantics)"
  | .fca             => "Formal Concept Analysis (concept lattice)"
  | .sheafLT         => "Sheaf Lawvere-Tierney modalities"
  | .operad          => "Operad (multicategory composition)"
  | .profunctor      => "Profunctor (bimodule / distributor)"
  | .kTheory         => "Algebraic/topological K-theory"
  -- Process
  | .process         => "Process algebra (CCS/CSP)"
  | .causal          => "Causal DAG representation"
  | .flow            => "Flow network (max-flow/min-cut)"
  | .cybernetic      => "Cybernetic feedback systems"
  | .rewriting       => "Rewriting systems (term reduction)"
  | .petriNet        => "Petri net (concurrent system modeling)"
  | .symbDyn         => "Symbolic dynamics (shift space, subshifts)"
  -- Crypto
  | .zkProof         => "Zero-knowledge proof (R1CS/Plonk)"
  | .fhe             => "Fully homomorphic encryption"
  | .lattice         => "Lattice-based cryptography (LWE)"
  | .boolLens        => "Boolean circuit for crypto VM"
  | .plonk           => "Plonk SNARK protocol"
  -- Physical
  | .assembly        => "Assembly theory (J-depth complexity)"
  | .spinGlass       => "Spin glass (disordered magnetism)"
  | .string          => "String theory (worldsheet/target)"
  | .wolfram         => "Wolfram physics (hypergraph rewriting)"
  | .quantumInfo     => "Quantum information theory"
  | .renormGroup     => "Renormalization group (RG flow, universality)"
  | .conformal       => "Conformal field theory (Virasoro algebra)"
  -- Topological
  | .locSys          => "Local systems (locally constant sheaves)"
  | .chainComplex    => "Chain complex (homological algebra)"
  | .groupoid        => "Groupoid (invertible morphisms)"
  | .jRatchet        => "J-ratchet nucleus-induced topology"
  | .knot            => "Knot invariants (topological)"
  | .spectral        => "Spectral analysis (eigenvalues)"
  | .dimLens         => "Dimensional lens (HoTT)"
  | .homotopy        => "Homotopy type (path types)"
  | .simplicial      => "Simplicial set (nerve, Kan complex)"
  | .topos           => "Topos (subobject classifier, internal language)"
  | .derivedCat      => "Derived category (triangulated structure)"
  -- Information
  | .probability     => "Probability distributions (nucleus)"
  | .infoTrace       => "Information trace (flow tracking)"
  | .holographic     => "Holographic principle encoding"
  | .infoTheory      => "Information theory (entropy)"
  | .kolmogorov      => "Kolmogorov complexity (algorithmic information)"
  | .fisher          => "Fisher information metric (information geometry)"
  -- Bridges
  | .tensorIntensity   => "Tensor intensity-based encoding"
  | .graphAlexandroff  => "Graph Alexandroff topology"
  | .cliffordProjector => "Clifford projector encoding"
  | .cliffordCommutant => "Clifford commutant subalgebra"
  | .geometric         => "Geometric algebra representation"
  | .ctGraph           => "Category-to-Graph bridge"
  | .ctTensor          => "Category-to-Tensor bridge"
  | .ctQuantum         => "Category-to-Quantum bridge"
  | .emergence         => "Emergence / complexity metrics"
  -- PCB
  | .pcbSingle       => "PCB single-board representation"
  | .pcbMulti        => "PCB multi-board representation"
  | .pcbDistance     => "PCB distance metrics"
  | .lensIR          => "Compiled lens IR"
  -- Economic
  | .kelly           => "Kelly criterion (optimal betting)"
  | .defi            => "DeFi protocol structures"
  | .gameTheory      => "Nash equilibrium (game-theoretic solution)"
  | .auction         => "Mechanism design (auction theory)"
  -- Representation
  | .matrix          => "Matrix / linear algebra"
  | .radial          => "Radial / ring-based encoding"
  -- Utility
  | .trace           => "Execution trace representation"
  | .truncation      => "Truncation / approximation"
  | .absInt          => "Abstract interpretation domains"
  -- Differential Geometry
  | .fiberBundle     => "Fiber bundle (connection, curvature, gauge)"
  | .gauge           => "Gauge field (principal bundle connection)"
  | .riemannian      => "Riemannian metric (geodesics, curvature tensor)"
  | .symplectic      => "Symplectic manifold (Hamiltonian mechanics)"
  -- TDA
  | .persistence     => "Persistent homology (barcodes, TDA filtrations)"
  | .mapper          => "Mapper / Reeb graph (TDA shape summarization)"
  | .morse           => "Morse theory (critical points, handle decomposition)"
  -- Coalgebraic
  | .coalgebra       => "F-coalgebra (bisimulation, final coalgebra)"
  | .stream          => "Coinductive streams (infinite sequences)"
  | .automaton       => "Finite automaton (regular language recognition)"
  -- Optimal Transport
  | .wasserstein     => "Wasserstein / earth mover's distance"
  | .ot              => "Optimal transport plan (Monge-Kantorovich)"
  -- Signal/Harmonic
  | .fourier         => "Fourier transform (spectral decomposition)"
  | .wavelet         => "Wavelet (multiresolution analysis)"
  | .laplacian       => "Graph/manifold Laplacian (diffusion kernel)"

/-- Category for organization. -/
inductive Category where
  | foundational
  | generative
  | quantum
  | algebraic
  | process
  | crypto
  | physical
  | topological
  | information
  | bridge
  | pcb
  | economic
  | representation
  | utility
  | diffGeometry
  | tda
  | coalgebraic
  | optTransport
  | signal
  deriving DecidableEq, Repr

/-- Get the category of a lens tag. -/
def categoryOf : CoreLensTag → Category
  -- Foundational
  | .omega | .tensor | .graph | .clifford | .topology | .matula => .foundational
  -- Generative
  | .surreal | .combinator | .typeTheory | .ordinal | .lambda | .leanCore => .generative
  -- Quantum
  | .density | .bloch | .circuit | .contextuality | .activeInf | .vacuum | .oml => .quantum
  -- Algebraic
  | .tropical | .tropicalDiff | .modal | .fca | .sheafLT
  | .operad | .profunctor | .kTheory => .algebraic
  -- Process
  | .process | .causal | .flow | .cybernetic | .rewriting
  | .petriNet | .symbDyn => .process
  -- Crypto
  | .zkProof | .fhe | .lattice | .boolLens | .plonk => .crypto
  -- Physical
  | .assembly | .spinGlass | .string | .wolfram | .quantumInfo
  | .renormGroup | .conformal => .physical
  -- Topological
  | .locSys | .chainComplex | .groupoid | .jRatchet | .knot | .spectral | .dimLens | .homotopy
  | .simplicial | .topos | .derivedCat => .topological
  -- Information
  | .probability | .infoTrace | .holographic | .infoTheory
  | .kolmogorov | .fisher => .information
  -- Bridges
  | .tensorIntensity | .graphAlexandroff | .cliffordProjector | .cliffordCommutant
  | .geometric | .ctGraph | .ctTensor | .ctQuantum | .emergence => .bridge
  -- PCB
  | .pcbSingle | .pcbMulti | .pcbDistance | .lensIR => .pcb
  -- Economic
  | .kelly | .defi | .gameTheory | .auction => .economic
  -- Representation
  | .matrix | .radial => .representation
  -- Utility
  | .trace | .truncation | .absInt => .utility
  -- Differential Geometry
  | .fiberBundle | .gauge | .riemannian | .symplectic => .diffGeometry
  -- TDA
  | .persistence | .mapper | .morse => .tda
  -- Coalgebraic
  | .coalgebra | .stream | .automaton => .coalgebraic
  -- Optimal Transport
  | .wasserstein | .ot => .optTransport
  -- Signal / Harmonic
  | .fourier | .wavelet | .laplacian => .signal

/-- All core lens tags as a list. -/
def all : List CoreLensTag :=
  [ -- Foundational (6)
    .omega, .tensor, .graph, .clifford, .topology, .matula,
    -- Generative (6)
    .surreal, .combinator, .typeTheory, .ordinal, .lambda, .leanCore,
    -- Quantum (7)
    .density, .bloch, .circuit, .contextuality, .activeInf, .vacuum, .oml,
    -- Algebraic (8)
    .tropical, .tropicalDiff, .modal, .fca, .sheafLT, .operad, .profunctor, .kTheory,
    -- Process (7)
    .process, .causal, .flow, .cybernetic, .rewriting, .petriNet, .symbDyn,
    -- Crypto (5)
    .zkProof, .fhe, .lattice, .boolLens, .plonk,
    -- Physical (7)
    .assembly, .spinGlass, .string, .wolfram, .quantumInfo, .renormGroup, .conformal,
    -- Topological (11)
    .locSys, .chainComplex, .groupoid, .jRatchet, .knot, .spectral, .dimLens, .homotopy,
    .simplicial, .topos, .derivedCat,
    -- Information (6)
    .probability, .infoTrace, .holographic, .infoTheory, .kolmogorov, .fisher,
    -- Bridges (9)
    .tensorIntensity, .graphAlexandroff, .cliffordProjector, .cliffordCommutant,
    .geometric, .ctGraph, .ctTensor, .ctQuantum, .emergence,
    -- PCB (4)
    .pcbSingle, .pcbMulti, .pcbDistance, .lensIR,
    -- Economic (4)
    .kelly, .defi, .gameTheory, .auction,
    -- Representation (2)
    .matrix, .radial,
    -- Utility (3)
    .trace, .truncation, .absInt,
    -- Differential Geometry (4)
    .fiberBundle, .gauge, .riemannian, .symplectic,
    -- TDA (3)
    .persistence, .mapper, .morse,
    -- Coalgebraic (3)
    .coalgebra, .stream, .automaton,
    -- Optimal Transport (2)
    .wasserstein, .ot,
    -- Signal / Harmonic (3)
    .fourier, .wavelet, .laplacian
  ]

/-- Every core lens tag appears in `CoreLensTag.all`. -/
theorem mem_all (tag : CoreLensTag) : tag ∈ all := by
  cases tag <;> simp [all]

/-- Count of core lenses. -/
def count : ℕ := 100

/-- Get all lenses in a category. -/
def inCategory (c : Category) : List CoreLensTag :=
  all.filter (fun t => categoryOf t == c)

end CoreLensTag

/-! ## LensTag Instance for CoreLensTag -/

instance : LensTag CoreLensTag where
  name := CoreLensTag.nameOf
  id := CoreLensTag.idOf
  description := CoreLensTag.descriptionOf

/-! ## Foundational Lens Groupings -/

/-- The 6 foundational lenses that form the minimal adelic basis. -/
def foundationalLenses : List CoreLensTag :=
  [.omega, .tensor, .graph, .clifford, .topology, .matula]

/-- The 6 generative stack lenses. -/
def generativeLenses : List CoreLensTag :=
  [.surreal, .combinator, .typeTheory, .ordinal, .lambda, .leanCore]

/-- The 7 quantum lenses. -/
def quantumLenses : List CoreLensTag :=
  [.density, .bloch, .circuit, .contextuality, .activeInf, .vacuum, .oml]

/-- The 8 algebraic lenses. -/
def algebraicLenses : List CoreLensTag :=
  [.tropical, .tropicalDiff, .modal, .fca, .sheafLT, .operad, .profunctor, .kTheory]

/-- The 7 process/flow lenses. -/
def processLenses : List CoreLensTag :=
  [.process, .causal, .flow, .cybernetic, .rewriting, .petriNet, .symbDyn]

/-- The 5 cryptographic lenses. -/
def cryptoLenses : List CoreLensTag :=
  [.zkProof, .fhe, .lattice, .boolLens, .plonk]

/-- The 7 physical lenses. -/
def physicalLenses : List CoreLensTag :=
  [.assembly, .spinGlass, .string, .wolfram, .quantumInfo, .renormGroup, .conformal]

/-- The 11 topological/categorical lenses. -/
def topologicalLenses : List CoreLensTag :=
  [.locSys, .chainComplex, .groupoid, .jRatchet, .knot, .spectral, .dimLens, .homotopy,
   .simplicial, .topos, .derivedCat]

/-- The 6 information-theoretic lenses. -/
def informationLenses : List CoreLensTag :=
  [.probability, .infoTrace, .holographic, .infoTheory, .kolmogorov, .fisher]

/-- The 9 bridge variant lenses. -/
def bridgeLenses : List CoreLensTag :=
  [.tensorIntensity, .graphAlexandroff, .cliffordProjector, .cliffordCommutant,
   .geometric, .ctGraph, .ctTensor, .ctQuantum, .emergence]

/-- The 4 PCB/hardware lenses. -/
def pcbLenses : List CoreLensTag :=
  [.pcbSingle, .pcbMulti, .pcbDistance, .lensIR]

/-- The 4 economic lenses. -/
def economicLenses : List CoreLensTag :=
  [.kelly, .defi, .gameTheory, .auction]

/-- The 2 representation lenses. -/
def representationLenses : List CoreLensTag :=
  [.matrix, .radial]

/-- The 3 utility lenses. -/
def utilityLenses : List CoreLensTag :=
  [.trace, .truncation, .absInt]

/-- The 4 differential geometry lenses. -/
def diffGeometryLenses : List CoreLensTag :=
  [.fiberBundle, .gauge, .riemannian, .symplectic]

/-- The 3 topological data analysis lenses. -/
def tdaLenses : List CoreLensTag :=
  [.persistence, .mapper, .morse]

/-- The 3 coalgebraic / coinductive lenses. -/
def coalgebraicLenses : List CoreLensTag :=
  [.coalgebra, .stream, .automaton]

/-- The 2 optimal transport lenses. -/
def optTransportLenses : List CoreLensTag :=
  [.wasserstein, .ot]

/-- The 3 signal / harmonic analysis lenses. -/
def signalLenses : List CoreLensTag :=
  [.fourier, .wavelet, .laplacian]

end Embeddings
end HeytingLean
