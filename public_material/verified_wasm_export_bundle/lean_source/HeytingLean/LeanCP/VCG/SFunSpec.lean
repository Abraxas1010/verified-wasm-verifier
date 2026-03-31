import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LeanCP.Core.SProp

namespace HeytingLean.LeanCP

/-- State-sensitive function specifications over the full LeanCP machine state. -/
structure SFunSpec where
  name : String
  params : List (String × CType)
  retType : CType
  pre : SProp
  post : CVal → SProp
  body : CStmt

/-- Function environment for state-sensitive call specifications. -/
abbrev FunEnv := String → Option SFunSpec

end HeytingLean.LeanCP
