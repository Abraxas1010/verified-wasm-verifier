import HeytingLean.Reasoning.Rules
import HeytingLean.Reasoning.Engine

/-
Compile-only sanity for the reasoning scaffold.
-/

namespace HeytingLean
namespace Tests
namespace Reasoning

open HeytingLean.Reasoning

def facts0 : Array String := #[("A"), ("A→B")]  -- note: extra symbols tolerated

def r1 : Reasoning.Rule String :=
  { premises := #[("A")], concl := ("B") }

def r2 : Reasoning.Rule String :=
  { premises := #[("B")], concl := ("C") }

def r3 : Reasoning.Rule String :=
  { premises := #[("B"), ("C")], concl := ("D") }

def rules : Array (Reasoning.Rule String) := #[r1, r2, r3]

def closure : Array String := Reasoning.saturate rules facts0 8

end Reasoning
end Tests
end HeytingLean

