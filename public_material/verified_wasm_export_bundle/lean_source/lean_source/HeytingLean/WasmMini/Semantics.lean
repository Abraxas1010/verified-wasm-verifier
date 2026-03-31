import HeytingLean.WasmMini.Syntax

namespace HeytingLean
namespace WasmMini

/-!
# HeytingLean.WasmMini.Semantics

Fuel-bounded big-step semantics for the `WasmMini` instruction subset.

This semantics is intended for:
- proving `MiniC → WasmMini` compilation correctness (Phase 1),
- serving as a Lean-level oracle for differential testing against `wasmtime`.

It is **not** a complete formalization of the WebAssembly spec.
-/

def Store.update (σ : Store) (x : String) (v : Int) : Store :=
  fun y => if y = x then v else σ y

inductive Outcome where
  | normal (σ : Store) (stack : Stack)
  | br (lbl : Label) (σ : Store) (stack : Stack)
  | returned (v : Int)

def pop1 : Stack → Option (Int × Stack)
  | [] => none
  | v :: vs => some (v, vs)

def pop2 : Stack → Option (Int × Int × Stack)
  | v₂ :: v₁ :: vs => some (v₂, v₁, vs)
  | _ => none

def push (v : Int) (st : Stack) : Stack := v :: st

def bool01 (b : Bool) : Int := if b then 1 else 0

mutual
  /-- Execute a list of instructions with fuel. -/
  def execInstrsFuel : Nat → List Instr → Store → Stack → Option Outcome
    | 0, _, _, _ => none
    | _ + 1, [], σ, st => some (.normal σ st)
    | fuel + 1, i :: is, σ, st => do
        let out ← execInstrFuel fuel i σ st
        match out with
        | .normal σ' st' => execInstrsFuel fuel is σ' st'
        | .br l σ' st' => some (.br l σ' st')
        | .returned v => some (.returned v)

  /-- Execute a single instruction with fuel. -/
  def execInstrFuel : Nat → Instr → Store → Stack → Option Outcome
    | 0, _, _, _ => none
    | _ + 1, .i64Const n, σ, st =>
        some (.normal σ (push n st))
    | _ + 1, .localGet x, σ, st =>
        some (.normal σ (push (σ x) st))
    | _ + 1, .localSet x, σ, st => do
        let (v, st') ← pop1 st
        some (.normal (σ.update x v) st')
    | _ + 1, .i64Add, σ, st => do
        let (v₂, v₁, st') ← pop2 st
        some (.normal σ (push (v₁ + v₂) st'))
    | _ + 1, .i64Sub, σ, st => do
        let (v₂, v₁, st') ← pop2 st
        some (.normal σ (push (v₁ - v₂) st'))
    | _ + 1, .i64Mul, σ, st => do
        let (v₂, v₁, st') ← pop2 st
        some (.normal σ (push (v₁ * v₂) st'))
    | _ + 1, .i64LeS, σ, st => do
        let (v₂, v₁, st') ← pop2 st
        some (.normal σ (push (bool01 (decide (v₁ ≤ v₂))) st'))
    | _ + 1, .i64Eq, σ, st => do
        let (v₂, v₁, st') ← pop2 st
        some (.normal σ (push (bool01 (decide (v₁ = v₂))) st'))
    | _ + 1, .i64Ne, σ, st => do
        let (v₂, v₁, st') ← pop2 st
        some (.normal σ (push (bool01 (decide (v₁ ≠ v₂))) st'))
    | _ + 1, .i64Eqz, σ, st => do
        let (v, st') ← pop1 st
        some (.normal σ (push (bool01 (decide (v = 0))) st'))
    | _ + 1, .i64ExtendI32u, σ, st =>
        -- In our Phase-1 model booleans are already 0/1 integers, so this is an identity.
        some (.normal σ st)
    | fuel + 1, .if_ then_ else_, σ, st => do
        let (c, st') ← pop1 st
        let branch := if c ≠ 0 then then_ else else_
        match ← execInstrsFuel fuel branch σ st' with
        | .normal σ' st'' => some (.normal σ' st'')
        | .br l σ' st'' => some (.br l σ' st'')
        | .returned v => some (.returned v)
    | fuel + 1, .block lbl body, σ, st => do
        match ← execInstrsFuel fuel body σ st with
        | .normal σ' st' => some (.normal σ' st')
        | .returned v => some (.returned v)
        | .br l σ' st' =>
            if l = lbl then
              some (.normal σ' st')
            else
              some (.br l σ' st')
    | fuel + 1, .loop lbl body, σ, st => do
        match ← execInstrsFuel fuel body σ st with
        | .normal σ' st' => some (.normal σ' st')
        | .returned v => some (.returned v)
        | .br l σ' st' =>
            if l = lbl then
              execInstrFuel fuel (.loop lbl body) σ' st'
            else
              some (.br l σ' st')
    | _ + 1, .br lbl, σ, st =>
        some (.br lbl σ st)
    | _ + 1, .return_, _σ, st => do
        let (v, _) ← pop1 st
        some (.returned v)
end

def execInstrs (is : List Instr) (σ : Store) (st : Stack := []) (fuel : Nat := 10000) : Option Outcome :=
  execInstrsFuel fuel is σ st

private def bindParamsAux : List String → List Int → Store → Option Store
  | [], [], σ => some σ
  | p :: ps, v :: vs, σ => bindParamsAux ps vs (σ.update p v)
  | _, _, _ => none

def bindParams (params : List String) (args : List Int) : Option Store :=
  bindParamsAux params args (fun _ => 0)

def runFun (fn : Fun) (args : List Int) (fuel : Nat := 10000) : Option Int := do
  let σ ← bindParams fn.params args
  match execInstrsFuel fuel fn.body σ [] with
  | some (.returned v) => some v
  | _ => none

/-!
## While-free fragment semantics (structural)

For proof work we often restrict to the while-free fragment (mirroring
`MiniC.Stmt.execFrag`). This avoids fuel plumbing in compilation correctness
statements for the existing certified Nat kernels.
-/

inductive FragResult where
  | normal (σ : Store) (stack : Stack)
  | returned (v : Int)

-- Structural executor for the fragment (no `block/loop/br`).
partial def execFrag : List Instr → Store → Stack → Option FragResult
  | [], σ, st => some (.normal σ st)
  | i :: is, σ, st => do
      match i with
      | .i64Const n =>
          execFrag is σ (n :: st)
      | .localGet x =>
          execFrag is σ ((σ x) :: st)
      | .localSet x =>
          let (v, st') ← pop1 st
          execFrag is (σ.update x v) st'
      | .i64Add =>
          let (v₂, v₁, st') ← pop2 st
          execFrag is σ ((v₁ + v₂) :: st')
      | .i64Sub =>
          let (v₂, v₁, st') ← pop2 st
          execFrag is σ ((v₁ - v₂) :: st')
      | .i64Mul =>
          let (v₂, v₁, st') ← pop2 st
          execFrag is σ ((v₁ * v₂) :: st')
      | .i64LeS =>
          let (v₂, v₁, st') ← pop2 st
          execFrag is σ ((bool01 (decide (v₁ ≤ v₂))) :: st')
      | .i64Eq =>
          let (v₂, v₁, st') ← pop2 st
          execFrag is σ ((bool01 (decide (v₁ = v₂))) :: st')
      | .i64Ne =>
          let (v₂, v₁, st') ← pop2 st
          execFrag is σ ((bool01 (decide (v₁ ≠ v₂))) :: st')
      | .i64Eqz =>
          let (v, st') ← pop1 st
          execFrag is σ ((bool01 (decide (v = 0))) :: st')
      | .i64ExtendI32u =>
          execFrag is σ st
      | .if_ then_ else_ =>
          let (c, st') ← pop1 st
          let branch := if c ≠ 0 then then_ else else_
          match ← execFrag branch σ st' with
          | .normal σ' st'' => execFrag is σ' st''
          | .returned v => some (.returned v)
      | .return_ =>
          let (v, _) ← pop1 st
          some (.returned v)
      | .block _ _ | .loop _ _ | .br _ =>
          none

def runFrag (is : List Instr) (σ : Store) : Option Int := do
  match ← execFrag is σ [] with
  | .returned v => some v
  | _ => none

/-!
## Expression-only evaluator (structural)

This evaluator is used for compilation correctness of `MiniC.Expr` into stack
code. It supports only the pure, expression-level instruction subset and
rejects control flow and store mutation.
-/

def evalExprCode : List Instr → Store → Stack → Option Stack
  | [], _, st => some st
  | i :: is, σ, st => do
      let st' ←
        match i with
        | .i64Const n => some (n :: st)
        | .localGet x => some ((σ x) :: st)
        | .i64Add => do
            let (v₂, v₁, st0) ← pop2 st
            some ((v₁ + v₂) :: st0)
        | .i64Sub => do
            let (v₂, v₁, st0) ← pop2 st
            some ((v₁ - v₂) :: st0)
        | .i64Mul => do
            let (v₂, v₁, st0) ← pop2 st
            some ((v₁ * v₂) :: st0)
        | .i64LeS => do
            let (v₂, v₁, st0) ← pop2 st
            some ((bool01 (decide (v₁ ≤ v₂))) :: st0)
        | .i64Eq => do
            let (v₂, v₁, st0) ← pop2 st
            some ((bool01 (decide (v₁ = v₂))) :: st0)
        | .i64Ne => do
            let (v₂, v₁, st0) ← pop2 st
            some ((bool01 (decide (v₁ ≠ v₂))) :: st0)
        | .i64Eqz => do
            let (v, st0) ← pop1 st
            some ((bool01 (decide (v = 0))) :: st0)
        | .i64ExtendI32u =>
            some st
        | _ =>
            none
      evalExprCode is σ st'

end WasmMini
end HeytingLean
