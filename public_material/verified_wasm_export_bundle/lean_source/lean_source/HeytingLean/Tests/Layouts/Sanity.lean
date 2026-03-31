import HeytingLean.Layouts

/-!
# Layouts sanity (CuTe flat layer)

These are lightweight compile-time checks for the new `HeytingLean.Layouts` modules.
-/

namespace HeytingLean.Tests.Layouts

open HeytingLean.Layouts
open HeytingLean.Layouts.Flat
open HeytingLean.Layouts.Tuple
open HeytingLean.Layouts.Nested

def L23 : FlatLayout :=
  [ ⟨(2 : ℕ+), 1⟩
  , ⟨(3 : ℕ+), 2⟩
  ]

example : FlatLayout.toCoords L23 5 = [1, 2] := by decide
example : FlatLayout.applyIndex L23 5 = 5 := by decide

def L22555 : FlatLayout :=
  [ ⟨(2 : ℕ+), 1⟩
  , ⟨(2 : ℕ+), 2⟩
  , ⟨(5 : ℕ+), 8⟩
  , ⟨(5 : ℕ+), 40⟩
  , ⟨(5 : ℕ+), 200⟩
  ]

def L4_125 : FlatLayout :=
  [ ⟨(4 : ℕ+), 1⟩
  , ⟨(125 : ℕ+), 8⟩
  ]

example : FlatLayout.coalesce L22555 = L4_125 := by decide

def L222 : FlatLayout :=
  [ ⟨(2 : ℕ+), 1⟩
  , ⟨(2 : ℕ+), 6⟩
  , ⟨(2 : ℕ+), 60⟩
  ]

def comp222_120 : FlatLayout :=
  [ ⟨(1 : ℕ+), 1⟩
  , ⟨(3 : ℕ+), 2⟩
  , ⟨(5 : ℕ+), 12⟩
  , ⟨(1 : ℕ+), 120⟩
  ]

def comp222_120_squeezed : FlatLayout :=
  [ ⟨(3 : ℕ+), 2⟩
  , ⟨(5 : ℕ+), 12⟩
  ]

example : FlatLayout.complement? L222 120 = some comp222_120 := by decide
example : FlatLayout.squeezeOnes comp222_120 = comp222_120_squeezed := by decide

def S23 : Tuple.Obj := [2, 3]

def id23 : Tuple.Mor S23 S23 := Tuple.Mor.id S23

example : id23.toLayout = L23 := by decide
example : id23.evalCoords [1, 2] = 5 := by decide

def T66 : NestedTuple :=
  NestedTuple.node [NestedTuple.leaf (6 : ℕ+), NestedTuple.leaf (6 : ℕ+)]

def U266 : NestedTuple :=
  NestedTuple.node [NestedTuple.leaf (2 : ℕ+), NestedTuple.leaf (6 : ℕ+), NestedTuple.leaf (6 : ℕ+)]

def T66' : NestedTuple :=
  NestedTuple.node
    [ NestedTuple.node [NestedTuple.leaf (2 : ℕ+), NestedTuple.leaf (3 : ℕ+)]
    , NestedTuple.node [NestedTuple.leaf (2 : ℕ+), NestedTuple.leaf (3 : ℕ+)]
    ]

def U266' : NestedTuple :=
  NestedTuple.node
    [ NestedTuple.leaf (2 : ℕ+)
    , NestedTuple.node [NestedTuple.leaf (3 : ℕ+), NestedTuple.leaf (2 : ℕ+)]
    , NestedTuple.node [NestedTuple.leaf (3 : ℕ+), NestedTuple.leaf (2 : ℕ+)]
    ]

example : NestedTuple.mutualRefinement? T66 U266 = some (T66', U266') := by native_decide

def idT66 : NestMorphism :=
  ⟨T66, T66, [1, 2]⟩

def idU266 : NestMorphism :=
  ⟨U266, U266, [1, 2, 3]⟩

example : idT66.isValid = true := by native_decide
example : idU266.isValid = true := by native_decide

def weak_id_example : Option NestMorphism :=
  NestMorphism.weakComposite? idT66 idU266

example : weak_id_example.isSome = true := by native_decide

end HeytingLean.Tests.Layouts
