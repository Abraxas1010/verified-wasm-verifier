import HeytingLean.CLI.TheoremDiagramExport

/-
# theorem_diagram_export executable entrypoint

This module exists so that other Lean modules can import
`HeytingLean.CLI.TheoremDiagramExport` without pulling a root-level `main`
definition into the global namespace.
-/

def main (argv : List String) : IO UInt32 :=
  HeytingLean.CLI.TheoremDiagramExport.main argv

