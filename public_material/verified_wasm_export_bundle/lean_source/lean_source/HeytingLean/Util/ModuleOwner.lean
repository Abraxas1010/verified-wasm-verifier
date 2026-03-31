import Lean

namespace HeytingLean.Util

open Lean

/--
Resolve a declaration's defining module from an imported environment.

`Environment.getModuleIdxFor?` only returns imported-module owners. Declarations
belonging to the current main module therefore need an explicit fallback to
`env.mainModule`, otherwise exact-module filters silently drop them.
-/
def moduleOwnerOf (env : Environment) (declName : Name) : Name :=
  match env.getModuleIdxFor? declName with
  | some modIdx => env.allImportedModuleNames[modIdx.toNat]!
  | none =>
      if env.contains declName then
        env.mainModule
      else
        declName.getPrefix

end HeytingLean.Util
