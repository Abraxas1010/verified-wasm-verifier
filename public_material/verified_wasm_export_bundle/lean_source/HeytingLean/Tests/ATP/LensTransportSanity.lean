import HeytingLean.ATP.LensTransport.FaithfulTransportGraph
import HeytingLean.ATP.LensTransport.LensMove
import HeytingLean.ATP.LensTransport.GlueComposer

/-
- source_type: test infrastructure
- attribution_status: n/a
- claim_status: n/a
- proof_status: proved
-/

namespace HeytingLean
namespace Tests
namespace ATP
namespace LensTransportSanity

open HeytingLean.Embeddings
open HeytingLean.ATP.LensTransport

-- Transport graph sanity
#eval transportClass .omega .tensor
#eval transportClass .region .omega
#eval transportClass .graph .tensor
#eval transportClass .omega .omega
#eval isSafeTransport .omega .region
#eval isSafeTransport .region .omega
#eval isSafeTransport .graph .tensor

-- Faithful targets from omega
#eval faithfulTargets .omega

-- Available moves from a fresh proof state
#eval availableLensMoves {
  currentLens := .graph
  state := []
  goal := []
  lensHistory := [.graph]
  depth := 0
}

-- Cycle prevention
#eval canTransition
  { currentLens := .topology
    state := []
    goal := []
    lensHistory := [.omega, .graph, .topology]
    depth := 2 }
  .omega

-- Budget exhaustion
#eval canTransition
  { currentLens := .topology
    state := []
    goal := []
    lensHistory := [.omega, .graph, .topology]
    depth := 3 }
  .region

example : transportClass .omega .tensor = .retract := by native_decide
example : transportClass .region .omega = .expansion := by native_decide
example : transportClass .graph .tensor = .incomparable := by native_decide
example : isSafeTransport .omega .region = true := by native_decide
example : isSafeTransport .region .omega = false := by native_decide
example : isSafeTransport .graph .tensor = false := by native_decide

end LensTransportSanity
end ATP
end Tests
end HeytingLean
