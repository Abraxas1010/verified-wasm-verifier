namespace HeytingLean.LeanCP

/-- A struct layout maps field names to offsets within a contiguous block. -/
structure StructLayout where
  name : String
  fields : List (String × Nat)
  blockSize : Nat
  deriving Repr, Inhabited

namespace StructLayout

/-- Look up the offset of a field within a layout. -/
def fieldOffset (layout : StructLayout) (field : String) : Option Nat :=
  (layout.fields.find? (fun entry => entry.1 == field)).map (·.2)

/-- Default layout for singly-linked list nodes. -/
def listLayout : StructLayout :=
  { name := "list", fields := [("data", 0), ("next", 1)], blockSize := 2 }

/-- Default layout for binary-tree nodes. -/
def treeLayout : StructLayout :=
  { name := "tree", fields := [("data", 0), ("left", 1), ("right", 2)], blockSize := 3 }

/-- Default layout for doubly-linked list nodes. -/
def dllLayout : StructLayout :=
  { name := "dll", fields := [("data", 0), ("next", 1), ("prev", 2)], blockSize := 3 }

/-- Global default registry for the built-in LeanCP struct shapes. -/
def defaultRegistry : String → Option StructLayout
  | "list" => some listLayout
  | "tree" => some treeLayout
  | "dll" => some dllLayout
  | _ => none

/-- Resolve a field offset by scanning the built-in layouts. -/
def defaultFieldOffset (field : String) : Nat :=
  let layouts := [listLayout, treeLayout, dllLayout]
  match layouts.findSome? (fun layout => fieldOffset layout field) with
  | some off => off
  | none => 0

@[simp] theorem defaultFieldOffset_data : defaultFieldOffset "data" = 0 := by
  simp [defaultFieldOffset, fieldOffset, listLayout, treeLayout, dllLayout]

@[simp] theorem defaultFieldOffset_next : defaultFieldOffset "next" = 1 := by
  simp [defaultFieldOffset, fieldOffset, listLayout, treeLayout, dllLayout]

@[simp] theorem defaultFieldOffset_left : defaultFieldOffset "left" = 1 := by
  simp [defaultFieldOffset, fieldOffset, listLayout, treeLayout, dllLayout]

@[simp] theorem defaultFieldOffset_right : defaultFieldOffset "right" = 2 := by
  simp [defaultFieldOffset, fieldOffset, listLayout, treeLayout, dllLayout]

@[simp] theorem defaultFieldOffset_prev : defaultFieldOffset "prev" = 2 := by
  simp [defaultFieldOffset, fieldOffset, listLayout, treeLayout, dllLayout]

/-- Compute the concrete address of a named field within a struct block. -/
def fieldAddr (layout : StructLayout) (base : Nat) (field : String) : Option Nat :=
  (fieldOffset layout field).map (base + ·)

end StructLayout
end HeytingLean.LeanCP
