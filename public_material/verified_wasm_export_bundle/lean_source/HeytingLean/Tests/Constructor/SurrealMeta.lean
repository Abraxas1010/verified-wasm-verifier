import HeytingLean.Constructor.SurrealAdapter

namespace HeytingLean
namespace Tests
namespace Constructor

open HeytingLean.Constructor
open HeytingLean.Constructor.SurrealAdapter

/-- Smoke-test that the Surreal closure nucleus carries a `Meta` instance. -/
noncomputable example : Meta (α := Carrier) Rcl :=
  inferInstance

end Constructor
end Tests
end HeytingLean
