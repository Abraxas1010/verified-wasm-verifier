import HeytingLean.NucleusPOD.Foundation

namespace HeytingLean
namespace NucleusPOD

/-!
Layer 3: Sheaf Gluing and Transport
Generated from `NucleusPOD_Lean_Proof_Catalog.docx`.
-/

def transportForward (t : AgentTransport {agentId := 0} {agentId := 0}) (x : Nat) : Nat :=
  t.forward x

def transportBackward (t : AgentTransport {agentId := 0} {agentId := 0}) (x : Nat) : Nat :=
  t.backward x

theorem transport_exact_for_R_closed
    (t : AgentTransport {agentId := 0} {agentId := 0})
    (x : Nat)
    (hClosed : closure x = x) :
    transportBackward t (transportForward t x) = x := by
  have hRoundTrip : transportBackward t (transportForward t (closure x)) = closure x := by
    simpa [transportBackward, transportForward] using t.roundTripClosed x
  have hx :
      transportBackward t (transportForward t x)
        = transportBackward t (transportForward t (closure x)) := by
    exact congrArg (fun y => transportBackward t (transportForward t y)) hClosed.symm
  calc
    transportBackward t (transportForward t x)
        = transportBackward t (transportForward t (closure x)) := hx
    _ = closure x := hRoundTrip
    _ = x := hClosed

end NucleusPOD
end HeytingLean
