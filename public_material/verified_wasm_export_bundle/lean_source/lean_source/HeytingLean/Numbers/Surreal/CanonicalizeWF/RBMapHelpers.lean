import Std
import Lean.Data.RBMap
import HeytingLean.Numbers.Surreal.CanonicalizeWF.Core

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace CanonicalizeWF
namespace RBMapHelpers

open Lean
open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore

/-- Convenience alias for the string-keyed maps used by the canonicalizer. -/
abbrev StringMap (β : Type u) := RBMap String β compare

/-- Extract the key list from a string-keyed RBMap. -/
def keysOf {β : Type u} (m : StringMap β) : List String :=
  m.toList.map Prod.fst

/-- `keysOf` on the empty map is empty. -/
@[simp] theorem keysOf_empty {β : Type u} :
    keysOf (RBMap.empty : StringMap β) = [] := by
  rfl

/-- The RBMap constructed by `normListCore`. -/
def coreMap (ys : List PreGame) : StringMap PreGame :=
  ys.foldl (init := RBMap.empty) fun acc g =>
    let k := key g
    if acc.contains k then acc else acc.insert k g

/-- The RBMap constructed by `uniqueSortedKeys`. -/
def keyMap (ys : List PreGame) : StringMap Unit :=
  ys.foldl (init := RBMap.empty) fun acc g =>
    let k := key g
    if acc.contains k then acc else acc.insert k ()

@[simp] theorem normListCore_eq (ys : List PreGame) :
    normListCore ys = (coreMap ys).toList.map Prod.snd := by
  rfl

@[simp] theorem uniqueSortedKeys_eq (ys : List PreGame) :
    uniqueSortedKeys ys = keysOf (keyMap ys) := by
  rfl

@[simp] theorem keysOf_coreMap (ys : List PreGame) :
    keysOf (coreMap ys) = (coreMap ys).toList.map Prod.fst := by
  rfl

end RBMapHelpers
end CanonicalizeWF
end Surreal
end Numbers
end HeytingLean
