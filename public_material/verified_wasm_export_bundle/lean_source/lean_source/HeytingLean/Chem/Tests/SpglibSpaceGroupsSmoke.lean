import HeytingLean.Chem.Materials.Symmetry.SpglibSpaceGroups
import Mathlib.Tactic

namespace HeytingLean
namespace Chem
namespace Tests

open HeytingLean.Chem.Materials
open HeytingLean.Chem.Materials.Symmetry
open HeytingLean.Chem.Materials.Symmetry.Spglib

example : (byNumber? 1).map (fun e => e.internationalShort) = some "P1" := by
  native_decide

example : (byNumber? 1).map (fun e => e.ops.length) = some 1 := by
  native_decide

example : (byNumber? 225).map (fun e => e.internationalShort) = some "Fm-3m" := by
  native_decide

example : (byNumber? 225).map (fun e => e.ops.length) = some 192 := by
  native_decide

example :
    (spaceGroupData? 225).map (fun sg => sg.ops.length) = some 192 := by
  native_decide

end Tests
end Chem
end HeytingLean
