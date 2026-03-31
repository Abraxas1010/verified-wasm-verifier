import HeytingLean.Crypto.Form
import HeytingLean.Crypto.Prog
import HeytingLean.Crypto.Compile

namespace HeytingLean
namespace Crypto
namespace BoolLens

/-- Boolean environments for formulas over `Fin n`. -/
abbrev Env (n : ℕ) := Fin n → Bool

/-- Interpret a `Form` in the two-valued Heyting algebra (`Bool`). -/
def eval : Form n → Env n → Bool
  | .top, _ => true
  | .bot, _ => false
  | .var idx, ρ => ρ idx
  | .and φ ψ, ρ => eval φ ρ && eval ψ ρ
  | .or φ ψ, ρ => eval φ ρ || eval ψ ρ
  | .imp φ ψ, ρ => (! eval φ ρ) || eval ψ ρ

/-- Operand stack (head = top) for the boolean VM. -/
abbrev Stack := List Bool

/-- Trace of stack snapshots during execution. -/
abbrev Trace := List Stack

/-- Apply a binary operator to the top two operands. -/
private def applyBinary (op : Bool → Bool → Bool) :
    Stack → Stack
  | x :: y :: stk => op y x :: stk
  | stk => stk

/-- Evaluate a single instruction under environment `ρ`. -/
def step {n : ℕ} (ρ : Env n) :
    Instr n → Stack → Stack
  | .pushTop, stk => true :: stk
  | .pushBot, stk => false :: stk
  | .pushVar idx, stk => ρ idx :: stk
  | .applyAnd, stk => applyBinary (· && ·) stk
  | .applyOr, stk => applyBinary (· || ·) stk
  | .applyImp, stk => applyBinary (fun x y => (! x) || y) stk

/-- Execute a program, threading the operand stack. -/
def exec {n : ℕ} (ρ : Env n) :
    Program n → Stack → Stack
  | [], stk => stk
  | instr :: prog, stk =>
      exec ρ prog (step ρ instr stk)

/-- Collect stack snapshots along an execution. -/
def traceFrom {n : ℕ} (ρ : Env n) :
    Program n → Stack → Trace
  | [], stk => [stk]
  | instr :: prog, stk =>
      let stk' := step ρ instr stk
      stk :: traceFrom ρ prog stk'

/-- Run a program from the empty stack; return trace and final top operand.
Undefined behaviour (underflow) defaults to `false`; compilation prevents it. -/
def run {n : ℕ} (prog : Program n) (ρ : Env n) :
    Trace × Bool :=
  let trace := traceFrom ρ prog []
  let finalStack := exec ρ prog []
  (trace, finalStack.headD false)

@[simp] lemma exec_nil {n : ℕ} (ρ : Env n) (stk : Stack) :
    exec ρ [] stk = stk := rfl

@[simp] lemma exec_cons {n : ℕ} (ρ : Env n) (instr : Instr n)
    (prog : Program n) (stk : Stack) :
    exec ρ (instr :: prog) stk =
      exec ρ prog (step ρ instr stk) := rfl

lemma exec_append {n : ℕ} (ρ : Env n)
    (prog₁ prog₂ : Program n) (stk : Stack) :
    exec ρ (prog₁ ++ prog₂) stk =
      exec ρ prog₂ (exec ρ prog₁ stk) := by
  induction prog₁ generalizing stk with
  | nil =>
      simp
  | cons instr prog₁ ih =>
      simp [List.cons_append, ih]

@[simp] lemma traceFrom_nil {n : ℕ} (ρ : Env n) (stk : Stack) :
    traceFrom ρ [] stk = [stk] := rfl

@[simp] lemma traceFrom_cons {n : ℕ} (ρ : Env n) (instr : Instr n)
    (prog : Program n) (stk : Stack) :
    traceFrom ρ (instr :: prog) stk =
      stk :: traceFrom ρ prog (step ρ instr stk) := rfl

lemma traceFrom_cons_head {n : ℕ} (ρ : Env n) (prog : Program n)
    (stk : Stack) :
    ∃ tail, traceFrom ρ prog stk = stk :: tail := by
  cases prog with
  | nil =>
      exact ⟨[], by simp [traceFrom]⟩
  | cons instr prog =>
      exact ⟨traceFrom ρ prog (step ρ instr stk), by simp [traceFrom]⟩

@[simp] lemma applyBinary_cons_cons (op : Bool → Bool → Bool)
    (x y : Bool) (stk : Stack) :
    applyBinary op (x :: y :: stk) = op y x :: stk := rfl

/-- Executing the compiled form pushes its boolean evaluation on the stack. -/
@[simp] lemma exec_compile_aux {n : ℕ}
    (ρ : Env n) (φ : Form n) (stk : Stack) :
    exec ρ (Form.compile φ) stk =
      eval φ ρ :: stk := by
  induction φ generalizing stk with
  | top =>
      simp [Form.compile, eval, step]
  | bot =>
      simp [Form.compile, eval, step]
  | var idx =>
      simp [Form.compile, eval, step]
  | and φ ψ ihφ ihψ =>
      simp [Form.compile, eval, exec_append, List.append_assoc,
        ihφ, ihψ, step, applyBinary_cons_cons]
  | or φ ψ ihφ ihψ =>
      simp [Form.compile, eval, exec_append, List.append_assoc,
        ihφ, ihψ, step, applyBinary_cons_cons]
  | imp φ ψ ihφ ihψ =>
      simp [Form.compile, eval, exec_append, List.append_assoc,
        ihφ, ihψ, step, applyBinary_cons_cons]

lemma run_compile_value {n : ℕ} (ρ : Env n) (φ : Form n) :
    (run (Form.compile φ) ρ).2 = eval φ ρ := by
  simp [run, exec_compile_aux (ρ := ρ) (φ := φ)]

/-- Canonical boolean trace produced by running a compiled form. -/
def canonicalTrace {n : ℕ} (φ : Form n) (ρ : Env n) :
    Trace :=
  (run (Form.compile φ) ρ).1

/-- Canonical boolean value (top of stack) for a compiled form. -/
def canonicalValue {n : ℕ} (φ : Form n) (ρ : Env n) :
    Bool :=
  (run (Form.compile φ) ρ).2

@[simp] lemma canonicalValue_eq_eval {n : ℕ}
    (φ : Form n) (ρ : Env n) :
    canonicalValue φ ρ = eval φ ρ :=
  run_compile_value (ρ := ρ) (φ := φ)

end BoolLens
end Crypto
end HeytingLean
