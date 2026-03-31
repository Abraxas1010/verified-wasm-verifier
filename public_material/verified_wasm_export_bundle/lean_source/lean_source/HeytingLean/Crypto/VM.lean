import HeytingLean.Crypto.Prog
import HeytingLean.Crypto.Lens.Class
import HeytingLean.Crypto.Lens.Semantics

namespace HeytingLean
namespace Crypto

open HeytingLean.LoF

universe u v

variable {α : Type u} [PrimaryAlgebra α]
variable {R : Reentry α}

namespace Lens

/-- Operand stack for the postfix VM (top-of-stack is the list head). -/
abbrev Stack (L : Lens (R := R)) := List L.Carrier

/-- Execution trace storing the stack before the first instruction and after every step. -/
abbrev Trace (L : Lens (R := R)) := List (Stack L)

/-- Apply a binary operator to the top two stack entries. -/
private def applyBinary (L : Lens (R := R))
    (op : L.Carrier → L.Carrier → L.Carrier) :
    Stack L → Stack L
  | x :: y :: stk => op y x :: stk
  | stk => stk

/-- Execute a single instruction. -/
def step (L : Lens (R := R)) {n : ℕ} (ρ : L.EnvL n) :
    Instr n → Stack L → Stack L
  | .pushTop, stk => L.top :: stk
  | .pushBot, stk => L.bot :: stk
  | .pushVar idx, stk => ρ idx :: stk
  | .applyAnd, stk => applyBinary L L.and stk
  | .applyOr, stk => applyBinary L L.or stk
  | .applyImp, stk => applyBinary L L.imp stk

/-- Execute a program, threading the stack. -/
def exec (L : Lens (R := R)) {n : ℕ} (ρ : L.EnvL n) :
    Program n → Stack L → Stack L
  | [], stk => stk
  | instr :: prog, stk =>
      exec L ρ prog (step L ρ instr stk)

/-- Collect stack snapshots along execution. -/
def traceFrom (L : Lens (R := R)) {n : ℕ} (ρ : L.EnvL n) :
    Program n → Stack L → Trace L
  | [], stk => [stk]
  | instr :: prog, stk =>
      let stk' := step L ρ instr stk
      stk :: traceFrom L ρ prog stk'

/-- Run a program from an empty stack, returning snapshots and the final top-of-stack.
The default `bot` return is unused once we restrict to compiled programs. -/
def run (L : Lens (R := R)) {n : ℕ} (prog : Program n) (ρ : L.EnvL n) :
    Trace L × L.Carrier :=
  let trace := traceFrom L ρ prog []
  let finalStack := exec L ρ prog []
  (trace, finalStack.headD L.bot)

section

variable (L : Lens (R := R))

@[simp] lemma applyBinary_cons_cons {op : L.Carrier → L.Carrier → L.Carrier}
    (x y : L.Carrier) (stk : Stack L) :
    applyBinary L op (x :: y :: stk) = op y x :: stk := rfl

@[simp] lemma exec_nil {n : ℕ} (ρ : L.EnvL n) (stk : Stack L) :
    exec L ρ [] stk = stk := rfl

@[simp] lemma exec_cons {n : ℕ} (ρ : L.EnvL n) (instr : Instr n)
    (prog : Program n) (stk : Stack L) :
    exec L ρ (instr :: prog) stk =
      exec L ρ prog (step L ρ instr stk) := rfl

lemma exec_append {n : ℕ} (ρ : L.EnvL n)
    (prog₁ prog₂ : Program n) (stk : Stack L) :
    exec L ρ (prog₁ ++ prog₂) stk =
      exec L ρ prog₂ (exec L ρ prog₁ stk) := by
  induction prog₁ generalizing stk with
  | nil =>
      simp
  | cons instr prog₁ ih =>
      simp [List.cons_append, ih]

@[simp] lemma traceFrom_nil {n : ℕ} (ρ : L.EnvL n) (stk : Stack L) :
    traceFrom L ρ [] stk = [stk] := rfl

@[simp] lemma traceFrom_cons {n : ℕ} (ρ : L.EnvL n)
    (instr : Instr n) (prog : Program n) (stk : Stack L) :
    traceFrom L ρ (instr :: prog) stk =
      stk :: traceFrom L ρ prog (step L ρ instr stk) := rfl

end

end Lens

end Crypto
end HeytingLean
