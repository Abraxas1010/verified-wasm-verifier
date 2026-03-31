import HeytingLean.LeanCP.Lang.CSyntax

/-!
# LeanCP C Declarations

Raw function/program declaration carriers for code-generation paths that target
the LeanCP-owned C syntax before separation-logic specifications are attached.
These carriers are intentionally lighter-weight than `CFunSpec`: they record the
typed executable surface without overclaiming verification coverage.
-/

namespace HeytingLean.LeanCP

/-- A typed C function declaration without proof obligations. -/
structure CFunDecl where
  name : String
  params : List (String × CType)
  retType : CType := .int
  body : CStmt

/-- A collection of raw LeanCP-owned C declarations with an explicit entry point. -/
structure CProgramDecl where
  defs : List CFunDecl
  main : CFunDecl

end HeytingLean.LeanCP
