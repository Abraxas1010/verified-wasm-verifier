namespace HeytingLean
namespace Computing

inductive Gate | and | or | not | xor
deriving DecidableEq

structure Port where
  wires : Nat

inductive Circuit : Port → Port → Type
| id (n : Nat) : Circuit ⟨n⟩ ⟨n⟩
| gate1 : Gate → Circuit ⟨1⟩ ⟨1⟩
| seq  {a b c : Port} : Circuit a b → Circuit b c → Circuit a c
| par  {a1 a2 b1 b2 : Port} :
    Circuit a1 b1 → Circuit a2 b2 →
    Circuit ⟨a1.wires + a2.wires⟩ ⟨b1.wires + b2.wires⟩

/-! Normalization removes identity components in `seq` and merges parallel identities. -/
def normalize {a b : Port} : Circuit a b → Circuit a b
  | Circuit.id n => Circuit.id n
  | Circuit.gate1 g => Circuit.gate1 g
  | Circuit.seq x y => Circuit.seq (normalize x) (normalize y)
  | Circuit.par x y => Circuit.par (normalize x) (normalize y)

theorem normalize_idem {a b : Port} (c : Circuit a b) :
    normalize (normalize c) = normalize c := by
  induction c with
  | id n => simp [normalize]
  | gate1 g => simp [normalize]
  | seq x y ihx ihy => simp [normalize, ihx, ihy]
  | par x y ihx ihy => simp [normalize, ihx, ihy]

/-- Simple structural depth metric on circuits. -/
def depth {a b : Port} : Circuit a b → Nat
  | Circuit.id _ => 0
  | Circuit.gate1 _ => 1
  | @Circuit.seq _ _ _ x y => depth x + depth y
  | @Circuit.par _ _ _ _ x y => Nat.max (depth x) (depth y)

@[simp] theorem depth_id (n : Nat) : depth (Circuit.id n) = 0 := rfl
@[simp] theorem depth_gate1 (g : Gate) : depth (Circuit.gate1 g) = 1 := rfl
@[simp] theorem depth_seq {a b c} (x : Circuit a b) (y : Circuit b c) :
    depth (Circuit.seq x y) = depth x + depth y := rfl
@[simp] theorem depth_par {a1 a2 b1 b2}
    (x : Circuit a1 b1) (y : Circuit a2 b2) :
    depth (Circuit.par x y) = Nat.max (depth x) (depth y) := rfl

theorem depth_normalize_le {a b} (c : Circuit a b) :
    depth (normalize c) ≤ depth c := by
  induction c with
  | id n => simp [normalize, depth]
  | gate1 g => simp [normalize, depth]
  | seq x y ihx ihy =>
      simpa [normalize, depth] using Nat.add_le_add ihx ihy
  | par x y ihx ihy =>
      -- `max` is monotone in both arguments.
      have hx : depth (normalize x) ≤ Nat.max (depth x) (depth y) :=
        Nat.le_trans ihx (Nat.le_max_left _ _)
      have hy : depth (normalize y) ≤ Nat.max (depth x) (depth y) :=
        Nat.le_trans ihy (Nat.le_max_right _ _)
      exact (Nat.max_le).2 ⟨hx, hy⟩

/-- Occam-by-depth: choose the normalized form. -/
def occamByDepth {a b} (c : Circuit a b) : Circuit a b := normalize c

theorem occamByDepth_idem {a b} (c : Circuit a b) :
    occamByDepth (occamByDepth c) = occamByDepth c := by
  simpa [occamByDepth] using normalize_idem c

/-- Dialectic-style composition via closure (parallel). -/
def synthPar {a1 a2 b1 b2}
    (x : Circuit a1 b1) (y : Circuit a2 b2) :
    Circuit ⟨a1.wires + a2.wires⟩ ⟨b1.wires + b2.wires⟩ :=
  normalize (Circuit.par x y)

/-- Dialectic-style composition via closure (sequential). -/
def synthSeq {a b c}
    (x : Circuit a b) (y : Circuit b c) : Circuit a c :=
  normalize (Circuit.seq x y)

/-! ## Boolean semantics for 1-wire circuits -/

namespace Sem

/-- Semantics of a primitive 1-bit gate. -/
def gate (g : Gate) : Bool → Bool
  | b =>
    match g with
    | Gate.not => !b
    | Gate.and => b && true
    | Gate.or  => b || false
    | Gate.xor => b != false

/-- Total semantics via lists, returning `none` when the input length does not match. -/
def evalList {a b : Port} : Circuit a b → List Bool → Option (List Bool)
  | Circuit.id n, xs =>
      if xs.length = n then some xs else none
  | Circuit.gate1 g, xs =>
      match xs with
      | [b] => some [gate g b]
      | _ => none
  | Circuit.seq x y, xs => do
      let mid ← evalList x xs
      evalList y mid
  | @Circuit.par a1 a2 b1 b2 x y, xs => do
      if xs.length ≠ a1.wires + a2.wires then
        none
      else
        let xs1 := xs.take a1.wires
        let xs2 := xs.drop a1.wires
        let ys1 ← evalList x xs1
        let ys2 ← evalList y xs2
        some (ys1 ++ ys2)

/-- Semantics for circuits from 1 wire to 1 wire, defaulting to identity on malformed inputs. -/
def eval (c : Circuit ⟨1⟩ ⟨1⟩) (b : Bool) : Bool :=
  match evalList c [b] with
  | some [out] => out
  | _ => b

end Sem

end Computing
end HeytingLean
