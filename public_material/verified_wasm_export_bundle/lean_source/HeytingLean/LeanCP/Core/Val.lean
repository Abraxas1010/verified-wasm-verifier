/-!
# LeanCP Value Types

C values for the LeanCP memory model: integers, unsigned integers, pointers,
aggregate values, null, and uninitialized memory.
-/

namespace HeytingLean.LeanCP

set_option autoImplicit false

/-- Memory block identifier shared by values and the memory model. -/
abbrev Block := Nat

/-- Offset within a block. -/
abbrev Offset := Int

/-- Native pointer identity: block plus block-local offset. -/
structure Addr where
  block : Block
  offset : Offset
  deriving Repr, DecidableEq, Inhabited

instance instOfNatAddr (n : Nat) : OfNat Addr n where
  ofNat := {
    block := 0
    offset := Int.ofNat n
  }

instance : Coe Nat Addr := ⟨fun n => {
  block := 0
  offset := Int.ofNat n
}⟩

abbrev PtrVal := Addr

namespace Addr

/-- LeanCP currently supports only nonnegative pointer shifts. -/
def addOffset (ptr : Addr) (delta : Int) : Option Addr :=
  if 0 ≤ delta then
    some {
      block := ptr.block
      offset := ptr.offset + delta
    }
  else
    none

end Addr

namespace PtrVal

abbrev addOffset := Addr.addOffset

end PtrVal

@[simp] theorem ptr_addOffset_nat (base delta : Nat) :
    PtrVal.addOffset (base : PtrVal) (Int.ofNat delta) = some ((base + delta : Nat) : PtrVal) := by
  simp [PtrVal.addOffset, Addr.addOffset]

/-- Supported machine integer sizes for the expanded C surface. -/
inductive IntSize where
  | I8
  | I16
  | I32
  | I64
  deriving DecidableEq, Repr, Inhabited

namespace IntSize

/-- Bit width of a machine integer size. -/
def bits : IntSize → Nat
  | .I8 => 8
  | .I16 => 16
  | .I32 => 32
  | .I64 => 64

end IntSize

/-- C values: the domain of heap cells and expression evaluation. -/
inductive CVal where
  | int : Int → CVal
  | uint : Nat → IntSize → CVal
  | float : Float → CVal
  | ptr : Block → Offset → CVal
  | null : CVal
  | undef : CVal
  | structVal : List (String × CVal) → CVal
  | unionVal : String → CVal → CVal
  deriving Repr, Inhabited


/-- Operational DecidableEq for Float via IEEE 754 bit representation. -/
private unsafe def floatDecEqUnsafe (a b : Float) : Decidable (a = b) :=
  if a.toBits == b.toBits then .isTrue lcProof else .isFalse lcProof

@[implemented_by floatDecEqUnsafe]
private opaque floatDecEq (a b : Float) : Decidable (a = b)

instance : DecidableEq Float := floatDecEq

mutual

  private def cvalFieldsDecEq : (xs ys : List (String × CVal)) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | (kx, vx) :: xs, (ky, vy) :: ys =>
        match decEq kx ky, cvalDecEq vx vy, cvalFieldsDecEq xs ys with
        | isTrue hk, isTrue hv, isTrue hrest =>
            isTrue (by cases hk; cases hv; cases hrest; rfl)
        | isFalse hk, _, _ =>
            isFalse (by intro h; cases h; exact hk rfl)
        | _, isFalse hv, _ =>
            isFalse (by intro h; cases h; exact hv rfl)
        | _, _, isFalse hrest =>
            isFalse (by intro h; cases h; exact hrest rfl)

  private def cvalDecEq : (a b : CVal) → Decidable (a = b)
    | .int a, .int b =>
        match decEq a b with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hEq; cases hEq; exact h rfl)
    | .uint a sa, .uint b sb =>
        match decEq a b, decEq sa sb with
        | isTrue ha, isTrue hs =>
            isTrue (by cases ha; cases hs; rfl)
        | isFalse ha, _ =>
            isFalse (by intro hEq; cases hEq; exact ha rfl)
        | _, isFalse hs =>
            isFalse (by intro hEq; cases hEq; exact hs rfl)
    | .float a, .float b =>
        match floatDecEq a b with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hEq; cases hEq; exact h rfl)
    | .ptr ba oa, .ptr bb ob =>
        match decEq ba bb, decEq oa ob with
        | isTrue hb, isTrue ho =>
            isTrue (by cases hb; cases ho; rfl)
        | isFalse hb, _ =>
            isFalse (by intro hEq; cases hEq; exact hb rfl)
        | _, isFalse ho =>
            isFalse (by intro hEq; cases hEq; exact ho rfl)
    | .null, .null => isTrue rfl
    | .undef, .undef => isTrue rfl
    | .structVal xs, .structVal ys =>
        match cvalFieldsDecEq xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hEq; cases hEq; exact h rfl)
    | .unionVal tx vx, .unionVal ty vy =>
        match decEq tx ty, cvalDecEq vx vy with
        | isTrue ht, isTrue hv =>
            isTrue (by cases ht; cases hv; rfl)
        | isFalse ht, _ =>
            isFalse (by intro hEq; cases hEq; exact ht rfl)
        | _, isFalse hv =>
            isFalse (by intro hEq; cases hEq; exact hv rfl)
    | .int _, .uint _ _ => isFalse (by intro h; cases h)
    | .int _, .float _ => isFalse (by intro h; cases h)
    | .int _, .ptr _ _ => isFalse (by intro h; cases h)
    | .int _, .null => isFalse (by intro h; cases h)
    | .int _, .undef => isFalse (by intro h; cases h)
    | .int _, .structVal _ => isFalse (by intro h; cases h)
    | .int _, .unionVal _ _ => isFalse (by intro h; cases h)
    | .uint _ _, .int _ => isFalse (by intro h; cases h)
    | .uint _ _, .float _ => isFalse (by intro h; cases h)
    | .uint _ _, .ptr _ _ => isFalse (by intro h; cases h)
    | .uint _ _, .null => isFalse (by intro h; cases h)
    | .uint _ _, .undef => isFalse (by intro h; cases h)
    | .uint _ _, .structVal _ => isFalse (by intro h; cases h)
    | .uint _ _, .unionVal _ _ => isFalse (by intro h; cases h)
    | .float _, .int _ => isFalse (by intro h; cases h)
    | .float _, .uint _ _ => isFalse (by intro h; cases h)
    | .float _, .ptr _ _ => isFalse (by intro h; cases h)
    | .float _, .null => isFalse (by intro h; cases h)
    | .float _, .undef => isFalse (by intro h; cases h)
    | .float _, .structVal _ => isFalse (by intro h; cases h)
    | .float _, .unionVal _ _ => isFalse (by intro h; cases h)
    | .ptr _ _, .int _ => isFalse (by intro h; cases h)
    | .ptr _ _, .uint _ _ => isFalse (by intro h; cases h)
    | .ptr _ _, .float _ => isFalse (by intro h; cases h)
    | .ptr _ _, .null => isFalse (by intro h; cases h)
    | .ptr _ _, .undef => isFalse (by intro h; cases h)
    | .ptr _ _, .structVal _ => isFalse (by intro h; cases h)
    | .ptr _ _, .unionVal _ _ => isFalse (by intro h; cases h)
    | .null, .int _ => isFalse (by intro h; cases h)
    | .null, .uint _ _ => isFalse (by intro h; cases h)
    | .null, .float _ => isFalse (by intro h; cases h)
    | .null, .ptr _ _ => isFalse (by intro h; cases h)
    | .null, .undef => isFalse (by intro h; cases h)
    | .null, .structVal _ => isFalse (by intro h; cases h)
    | .null, .unionVal _ _ => isFalse (by intro h; cases h)
    | .undef, .int _ => isFalse (by intro h; cases h)
    | .undef, .uint _ _ => isFalse (by intro h; cases h)
    | .undef, .float _ => isFalse (by intro h; cases h)
    | .undef, .ptr _ _ => isFalse (by intro h; cases h)
    | .undef, .null => isFalse (by intro h; cases h)
    | .undef, .structVal _ => isFalse (by intro h; cases h)
    | .undef, .unionVal _ _ => isFalse (by intro h; cases h)
    | .structVal _, .int _ => isFalse (by intro h; cases h)
    | .structVal _, .uint _ _ => isFalse (by intro h; cases h)
    | .structVal _, .float _ => isFalse (by intro h; cases h)
    | .structVal _, .ptr _ _ => isFalse (by intro h; cases h)
    | .structVal _, .null => isFalse (by intro h; cases h)
    | .structVal _, .undef => isFalse (by intro h; cases h)
    | .structVal _, .unionVal _ _ => isFalse (by intro h; cases h)
    | .unionVal _ _, .int _ => isFalse (by intro h; cases h)
    | .unionVal _ _, .uint _ _ => isFalse (by intro h; cases h)
    | .unionVal _ _, .float _ => isFalse (by intro h; cases h)
    | .unionVal _ _, .ptr _ _ => isFalse (by intro h; cases h)
    | .unionVal _ _, .null => isFalse (by intro h; cases h)
    | .unionVal _ _, .undef => isFalse (by intro h; cases h)
    | .unionVal _ _, .structVal _ => isFalse (by intro h; cases h)

end

instance : DecidableEq CVal := cvalDecEq

namespace CVal

/-- Smart constructor from an address record. -/
def ptrAddr (addr : Addr) : CVal :=
  .ptr addr.block addr.offset

/-- Recover an address record from a pointer value. -/
def toAddr? : CVal → Option Addr
  | .ptr block offset => some { block := block, offset := offset }
  | _ => none

end CVal

end HeytingLean.LeanCP
