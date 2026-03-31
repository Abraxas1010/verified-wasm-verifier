import HeytingLean.Constructor.SurrealUC

namespace HeytingLean
namespace Tests
namespace Constructor

open HeytingLean.Constructor
open HeytingLean.Constructor.SurrealUC

/-- A tiny universal constructor instance whose tape already contains its own
code; this witnesses the `selfRepro` field using the current `runsTo` interface. -/
def trivialUC : UC :=
  { code := Code.mk 0
    init := { state := 0, tape := [Code.mk 0] }
    selfRepro := by
      refine ⟨{ state := 0, tape := [Code.mk 0] }, ?_, ?_⟩
      · trivial
      ·
        -- The final configuration's tape contains the constructor's code.
        simp [tapeContains] }

/-- Smoke-test that the Surreal UC bridge can be used to interpret a UC
instance as a carrier element. -/
example : SurrealAdapter.Carrier :=
  ucCarrier trivialUC

end Constructor
end Tests
end HeytingLean
