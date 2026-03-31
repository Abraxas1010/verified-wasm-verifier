import HeytingLean.LeanCore.Syntax

namespace HeytingLean
namespace LeanCore

/-- Signature for a primitive constant: a name and its type. -/
structure PrimSig where
  name : String
  ty   : Ty
  deriving Repr, DecidableEq

/-- Finite catalogue of primitive constants available to LeanCore. -/
abbrev PrimEnv := List PrimSig

namespace PrimEnv

/-- Lookup the full signature for a primitive name. -/
def lookupSig (env : PrimEnv) (name : String) : Option PrimSig :=
  env.find? (fun sig => sig.name = name)

/-- Lookup only the type of a primitive constant. -/
def lookupTy (env : PrimEnv) (name : String) : Option Ty :=
  (lookupSig env name).map (·.ty)

/-- Default library of primitives shared across typing + semantics. -/
def default : PrimEnv :=
  [ { name := "zero", ty := Ty.base .nat }
  , { name := "succ", ty := Ty.arrow (Ty.base .nat) (Ty.base .nat) }
  , { name := "true", ty := Ty.base .bool }
  , { name := "false", ty := Ty.base .bool }
  ]

end PrimEnv

end LeanCore
end HeytingLean
