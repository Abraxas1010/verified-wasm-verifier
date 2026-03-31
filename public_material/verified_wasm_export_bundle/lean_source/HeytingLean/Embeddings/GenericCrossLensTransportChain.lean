import HeytingLean.Util.VirtualChain
import HeytingLean.Embeddings.GenericCrossLensTransport

namespace HeytingLean
namespace Embeddings
namespace GenericCrossLensTransport

open HeytingLean.Util

universe u v

/-- A single transport step between two tags. -/
abbrev Step (τ : Type u) (Carrier : τ → Type v) (src dst : τ) : Type v :=
  Carrier src → Carrier dst

/-- A chain of transport steps. -/
abbrev Chain (τ : Type u) (Carrier : τ → Type v) (src dst : τ) : Type _ :=
  VirtualChain (Step τ Carrier) src dst

/-- Compile a chain into one function by composing its steps. -/
def compile {τ : Type u} {Carrier : τ → Type v} {src dst : τ} :
    Chain τ Carrier src dst → (Carrier src → Carrier dst)
  | .nil _ => fun x => x
  | .cons f rest => (compile rest) ∘ f

/-- Forward composition via the Platonic factorization.
Convenience theorem at the chain layer. -/
theorem forward_comp {τ : Type u} {Carrier : τ → Type v} {Plato : Type v}
    (T : GenericTransport τ Carrier Plato) (src mid dst : τ) (x : Carrier src) :
    T.forward src dst x = T.forward mid dst (T.forward src mid x) := by
  simpa using (GenericTransport.forward_comp T src mid dst x)

end GenericCrossLensTransport
end Embeddings
end HeytingLean
