import HeytingLean.Export.ExportableLens
import HeytingLean.Tests.Bridges.ComputableTestKit
import HeytingLean.Tests.Bridges.BoolComputable
import HeytingLean.Tests.Bridges.ThreeComputable
import HeytingLean.Tests.Bridges.FiveComputable
import HeytingLean.Tests.Bridges.Chain6Computable

/-!
# Lens Definitions

Pre-built ExportableLens instances for common Heyting algebras.
-/

namespace HeytingLean.Export.LensDefinitions

open HeytingLean.Export
open HeytingLean.Tests.Bridges.ComputableTestKit (Diamond)
open HeytingLean.Tests.Bridges.BoolComputable (Bool2)
open HeytingLean.Tests.Bridges.ThreeComputable (Three)
open HeytingLean.Tests.Bridges.FiveComputable (Five)
open HeytingLean.Tests.Bridges.Chain6Computable (Chain6)

/-! ## Helper Functions -/

/-- Build a binary operation table from a function -/
def mkBinaryTable {α : Type} [DecidableEq α]
    (elements : List α) (op : α → α → α) (encode : α → Int) : Array (Array Int) :=
  elements.toArray.map fun x =>
    elements.toArray.map fun y =>
      encode (op x y)

/-- Build a unary operation table from a function -/
def mkUnaryTable {α : Type}
    (elements : List α) (op : α → α) (encode : α → Int) : Array Int :=
  elements.toArray.map fun x => encode (op x)

/-- Build a predicate table from a function -/
def mkPredTable {α : Type}
    (elements : List α) (pred : α → α → Bool) : Array (Array Bool) :=
  elements.toArray.map fun x =>
    elements.toArray.map fun y =>
      pred x y

/-! ## Diamond Lens (4 elements) -/

def diamondLens : ExportableLens := {
  lensId := "diamond"
  displayName := "Diamond Lattice"
  description := "4-element Heyting algebra with orthogonal atoms"
  carrierName := "Diamond"
  elements := #["bot", "left", "right", "top"]
  binaryOps := #[
    { name := "inf"
      cName := "diamond_inf"
      table := mkBinaryTable Diamond.all Diamond.inf' Diamond.toInt },
    { name := "sup"
      cName := "diamond_sup"
      table := mkBinaryTable Diamond.all Diamond.sup' Diamond.toInt },
    { name := "himp"
      cName := "diamond_himp"
      table := mkBinaryTable Diamond.all Diamond.himp' Diamond.toInt }
  ]
  unaryOps := #[
    { name := "compl"
      cName := "diamond_compl"
      table := mkUnaryTable Diamond.all Diamond.compl' Diamond.toInt }
  ]
  predicates := #[
    { name := "le"
      cName := "diamond_le"
      table := mkPredTable Diamond.all Diamond.le' }
  ]
  leanModules := #[
    "HeytingLean.Tests.Bridges.ComputableTestKit"
  ]
  theorems := #[
    "Diamond.le_refl", "Diamond.le_trans", "Diamond.le_antisymm",
    "Diamond.inf_le_left", "Diamond.inf_le_right", "Diamond.le_inf",
    "Diamond.le_sup_left", "Diamond.le_sup_right", "Diamond.sup_le",
    "Diamond.le_himp_iff", "Diamond.himp_bot"
  ]
}

/-! ## Bool2 Lens (2 elements) -/

def bool2Lens : ExportableLens := {
  lensId := "bool2"
  displayName := "Boolean Algebra (2-element)"
  description := "Simplest Boolean algebra with 2 elements"
  carrierName := "Bool2"
  elements := #["bot", "top"]
  binaryOps := #[
    { name := "inf"
      cName := "bool2_inf"
      table := mkBinaryTable Bool2.all Bool2.inf' Bool2.toInt },
    { name := "sup"
      cName := "bool2_sup"
      table := mkBinaryTable Bool2.all Bool2.sup' Bool2.toInt },
    { name := "himp"
      cName := "bool2_himp"
      table := mkBinaryTable Bool2.all Bool2.himp' Bool2.toInt }
  ]
  unaryOps := #[
    { name := "compl"
      cName := "bool2_compl"
      table := mkUnaryTable Bool2.all Bool2.compl' Bool2.toInt }
  ]
  predicates := #[
    { name := "le"
      cName := "bool2_le"
      table := mkPredTable Bool2.all Bool2.le' }
  ]
  leanModules := #[
    "HeytingLean.Tests.Bridges.BoolComputable"
  ]
  theorems := #[
    "Bool2.le_refl", "Bool2.le_trans", "Bool2.le_antisymm",
    "Bool2.inf_le_left", "Bool2.inf_le_right", "Bool2.le_inf",
    "Bool2.le_sup_left", "Bool2.le_sup_right", "Bool2.sup_le",
    "Bool2.le_himp_iff", "Bool2.himp_bot",
    "Bool2.inf_compl_le_bot", "Bool2.top_le_sup_compl"
  ]
  provenanceExtra := some <| Lean.Json.mkObj [
    ("is_boolean", Lean.Json.bool true),
    ("note", Lean.Json.str "Also satisfies Boolean algebra axioms")
  ]
}

/-! ## Three Lens (3-element chain) -/

def threeLens : ExportableLens := {
  lensId := "three"
  displayName := "Three-Element Chain"
  description := "3-element linear chain Heyting algebra (not Boolean)"
  carrierName := "Three"
  elements := #["bot", "mid", "top"]
  binaryOps := #[
    { name := "inf"
      cName := "three_inf"
      table := mkBinaryTable Three.all Three.inf' Three.toInt },
    { name := "sup"
      cName := "three_sup"
      table := mkBinaryTable Three.all Three.sup' Three.toInt },
    { name := "himp"
      cName := "three_himp"
      table := mkBinaryTable Three.all Three.himp' Three.toInt }
  ]
  unaryOps := #[
    { name := "compl"
      cName := "three_compl"
      table := mkUnaryTable Three.all Three.compl' Three.toInt }
  ]
  predicates := #[
    { name := "le"
      cName := "three_le"
      table := mkPredTable Three.all Three.le' }
  ]
  leanModules := #[
    "HeytingLean.Tests.Bridges.ThreeComputable"
  ]
  theorems := #[
    "Three.le_refl", "Three.le_trans", "Three.le_antisymm",
    "Three.inf_le_left", "Three.inf_le_right", "Three.le_inf",
    "Three.le_sup_left", "Three.le_sup_right", "Three.sup_le",
    "Three.le_himp_iff", "Three.himp_bot"
  ]
  provenanceExtra := some <| Lean.Json.mkObj [
    ("is_boolean", Lean.Json.bool false),
    ("note", Lean.Json.str "NOT Boolean: mid ⊔ ¬mid = mid ≠ ⊤")
  ]
}

/-! ## Five Lens (5-element chain) -/

def fiveLens : ExportableLens := {
  lensId := "five"
  displayName := "Five-Element Chain"
  description := "5-element linear chain Heyting algebra (not Boolean)"
  carrierName := "Five"
  elements := #["bot", "low", "mid", "high", "top"]
  binaryOps := #[
    { name := "inf"
      cName := "five_inf"
      table := mkBinaryTable Five.all Five.inf' Five.toInt },
    { name := "sup"
      cName := "five_sup"
      table := mkBinaryTable Five.all Five.sup' Five.toInt },
    { name := "himp"
      cName := "five_himp"
      table := mkBinaryTable Five.all Five.himp' Five.toInt }
  ]
  unaryOps := #[
    { name := "compl"
      cName := "five_compl"
      table := mkUnaryTable Five.all Five.compl' Five.toInt }
  ]
  predicates := #[
    { name := "le"
      cName := "five_le"
      table := mkPredTable Five.all Five.le' }
  ]
  leanModules := #[
    "HeytingLean.Tests.Bridges.FiveComputable"
  ]
  theorems := #[
    "Five.le_refl", "Five.le_trans", "Five.le_antisymm",
    "Five.inf_le_left", "Five.inf_le_right", "Five.le_inf",
    "Five.le_sup_left", "Five.le_sup_right", "Five.sup_le",
    "Five.le_himp_iff", "Five.himp_bot"
  ]
  provenanceExtra := some <| Lean.Json.mkObj [
    ("is_boolean", Lean.Json.bool false),
    ("note", Lean.Json.str "NOT Boolean: mid ⊔ ¬mid = mid ≠ ⊤")
  ]
}

/-! ## Chain6 Lens (6-element chain) -/

def chain6Lens : ExportableLens := {
  lensId := "chain6"
  displayName := "Six-Element Chain"
  description := "6-element linear chain Heyting algebra (not Boolean)"
  carrierName := "Chain6"
  elements := #["bot", "e1", "e2", "e3", "e4", "top"]
  binaryOps := #[
    { name := "inf"
      cName := "chain6_inf"
      table := mkBinaryTable Chain6.all Chain6.inf' Chain6.toInt },
    { name := "sup"
      cName := "chain6_sup"
      table := mkBinaryTable Chain6.all Chain6.sup' Chain6.toInt },
    { name := "himp"
      cName := "chain6_himp"
      table := mkBinaryTable Chain6.all Chain6.himp' Chain6.toInt }
  ]
  unaryOps := #[
    { name := "compl"
      cName := "chain6_compl"
      table := mkUnaryTable Chain6.all Chain6.compl' Chain6.toInt }
  ]
  predicates := #[
    { name := "le"
      cName := "chain6_le"
      table := mkPredTable Chain6.all Chain6.le' }
  ]
  leanModules := #[
    "HeytingLean.Tests.Bridges.Chain6Computable"
  ]
  theorems := #[
    "Chain6.le_refl", "Chain6.le_trans", "Chain6.le_antisymm",
    "Chain6.inf_le_left", "Chain6.inf_le_right", "Chain6.le_inf",
    "Chain6.le_sup_left", "Chain6.le_sup_right", "Chain6.sup_le",
    "Chain6.le_himp_iff", "Chain6.himp_bot"
  ]
  provenanceExtra := some <| Lean.Json.mkObj [
    ("is_boolean", Lean.Json.bool false),
    ("note", Lean.Json.str "NOT Boolean: e2 ⊔ ¬e2 = e2 ≠ ⊤")
  ]
}

/-! ## Lens Registry -/

/-- All available lenses -/
def allLenses : List ExportableLens := [
  diamondLens,
  bool2Lens,
  threeLens,
  fiveLens,
  chain6Lens
]

/-- Look up a lens by ID -/
def findLens (id : String) : Option ExportableLens :=
  allLenses.find? fun lens => lens.lensId == id

/-- List all lens IDs -/
def lensIds : List String := allLenses.map (·.lensId)

end HeytingLean.Export.LensDefinitions
