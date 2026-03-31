import HeytingLean.Epiplexity.Prelude
import HeytingLean.Epiplexity.Programs
import HeytingLean.Epiplexity.Info
import HeytingLean.Epiplexity.MDL
import HeytingLean.Epiplexity.Core
import HeytingLean.Epiplexity.Bounds
import HeytingLean.Epiplexity.Conditional
import HeytingLean.Epiplexity.Emergence
import HeytingLean.Epiplexity.Crypto.Axioms
import HeytingLean.Epiplexity.Crypto.CSPRNG
import HeytingLean.Epiplexity.Crypto.HeavySet
import HeytingLean.Epiplexity.Crypto.PRFHighEpiplexity
import HeytingLean.Epiplexity.Crypto.Factorization
import HeytingLean.Epiplexity.Extensions

/-!
# Epiplexity (umbrella)

Local Lean formalization of core definitions from “From Entropy to Epiplexity” (Finzi et al., 2026):

- MDL-style epiplexity `S_T` and time-bounded entropy `H_T`,
- conditional epiplexity / time-bounded conditional entropy,
- epiplexity-emergence predicate,
- cryptographic hypothesis predicates and the heavy-set lemmas used in the paper’s bounds.
-/
