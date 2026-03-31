import HeytingLean.Reasoning.Rules
import HeytingLean.Reasoning.Engine

namespace HeytingLean
namespace CLI

open HeytingLean.Reasoning

def ReasonDemo.run : IO Unit := do
  let facts : Array String := #["A", "A→B"]
  let rules : Array (Rule String) := #[
    { premises := #["A"], concl := "B" },
    { premises := #["B"], concl := "C" },
    { premises := #["B", "C"], concl := "D" }
  ]
  let closure := saturate rules facts 8
  IO.println s!"Reasoning demo — facts: {facts}"
  IO.println s!"closure: {closure}"

end CLI
end HeytingLean

def main : IO Unit :=
  HeytingLean.CLI.ReasonDemo.run

