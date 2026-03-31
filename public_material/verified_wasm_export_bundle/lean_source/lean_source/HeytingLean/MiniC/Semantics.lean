import HeytingLean.MiniC.Syntax

namespace HeytingLean
namespace MiniC

/-- Runtime values for MiniC. -/
inductive Val
  | int (n : Int)
  | bool (b : Bool)
  deriving Repr, DecidableEq

/-- Encode a natural number as a MiniC value. -/
@[simp] def natToVal (n : Nat) : Val := Val.int (Int.ofNat n)

@[simp] def Val.asNat? : Val → Option Nat
  | Val.int n =>
      if n ≥ 0 then
        some (Int.toNat n)
      else
        none
  | _ => none

/-- Stores map variable names to optional values. -/
abbrev Store := String → Option Val

/-- Empty store with no bindings. -/
@[simp] def emptyStore : Store := fun _ => none

/-- Lookup a variable in the store. -/
@[simp] def lookup (σ : Store) (name : String) : Option Val := σ name

/-- Update a variable in the store. -/
@[simp] def update (σ : Store) (name : String) (v : Val) : Store :=
  fun y => if y = name then some v else σ y

/-- Logical array length slot name (array encoded in flat store). -/
@[simp] def arrayLengthSlot (name : String) : String :=
  name ++ "#len"

/-- Logical array element slot name (array encoded in flat store). -/
@[simp] def arrayElemSlot (name : String) (idx : Nat) : String :=
  name ++ "#" ++ toString idx

/-- Logical struct field slot name (struct encoded in flat store). -/
@[simp] def structFieldSlot (name field : String) : String :=
  name ++ "$" ++ field

/-- Results of executing a statement. -/
inductive ExecResult
  | normal (σ : Store)
  | returned (v : Val)

/-- Evaluate an expression under the store. -/
def evalExpr : Expr → Store → Option Val
  | Expr.var x, σ => lookup σ x
  | Expr.intLit n, _ => some (Val.int n)
  | Expr.boolLit b, _ => some (Val.bool b)
  | Expr.arrayLit _, _ => none
  | Expr.arrayLength _, _ => none
  | Expr.arrayIndex _ _, _ => none
  | Expr.structLit _ _, _ => none
  | Expr.fieldAccess _ _, _ => none
  | Expr.add e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      match v₁, v₂ with
      | Val.int n₁, Val.int n₂ => pure (Val.int (n₁ + n₂))
      | _, _ => none
  | Expr.sub e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      match v₁, v₂ with
      | Val.int n₁, Val.int n₂ => pure (Val.int (n₁ - n₂))
      | _, _ => none
  | Expr.mul e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      match v₁, v₂ with
      | Val.int n₁, Val.int n₂ => pure (Val.int (n₁ * n₂))
      | _, _ => none
  | Expr.le e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      match v₁, v₂ with
      | Val.int n₁, Val.int n₂ => pure (Val.bool (decide (n₁ ≤ n₂)))
      | _, _ => none
  | Expr.eq e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      match v₁, v₂ with
      | Val.int n₁, Val.int n₂ => pure (Val.bool (decide (n₁ = n₂)))
      | Val.bool b₁, Val.bool b₂ => pure (Val.bool (decide (b₁ = b₂)))
      | _, _ => none
  | Expr.not e, σ => do
      let v ← evalExpr e σ
      match v with
      | Val.bool b => pure (Val.bool (!b))
      | _ => none
  | Expr.and e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      match v₁, v₂ with
      | Val.bool b₁, Val.bool b₂ => pure (Val.bool (b₁ && b₂))
      | _, _ => none
  | Expr.or e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      match v₁, v₂ with
      | Val.bool b₁, Val.bool b₂ => pure (Val.bool (b₁ || b₂))
      | _, _ => none

def bindParamsIntoStore : Store → List String → List Val → Option Store
  | σ, [], [] => some σ
  | σ, p :: ps, v :: vs => bindParamsIntoStore (update σ p v) ps vs
  | _, _, _ => none

def findFun (defs : List Fun) (fname : String) : Option Fun :=
  defs.find? (fun fn => fn.name = fname)

/- Partial big-step executor for MiniC statements. -/
mutual
  def execFuel : Nat → Stmt → Store → (defs : List Fun := []) → Option ExecResult
    | 0, _, _, _ => none
    | _ + 1, Stmt.skip, σ, _ => some (ExecResult.normal σ)
    | _ + 1, Stmt.assign x rhs, σ, _ => do
      let v ← evalExpr rhs σ
      pure (ExecResult.normal (update σ x v))
    | _ + 1, Stmt.arrayUpdate name idxExpr valExpr, σ, _ => do
      let idxVal ← evalExpr idxExpr σ
      let rhsVal ← evalExpr valExpr σ
      match idxVal, rhsVal with
      | .int i, .int rhs =>
          if i ≥ 0 then
            match lookup σ (arrayLengthSlot name) with
            | some (.int len) =>
                if i < len then
                  let slot := arrayElemSlot name (Int.toNat i)
                  pure (ExecResult.normal (update σ slot (.int rhs)))
                else
                  none
            | _ => none
          else
            none
      | _, _ => none
    | _ + 1, Stmt.structUpdate name field rhsExpr, σ, _ => do
      let rhsVal ← evalExpr rhsExpr σ
      pure (ExecResult.normal (update σ (structFieldSlot name field) rhsVal))
    | fuel + 1, Stmt.call fname args ret, σ, defs => do
        let argVals ← args.mapM (fun e => evalExpr e σ)
        let rv ← callByValuesFuel fuel σ fname argVals defs
        pure (ExecResult.normal (update σ ret rv))
    | fuel + 1, Stmt.seq s₁ s₂, σ, defs => do
      match execFuel fuel s₁ σ defs with
      | some (ExecResult.normal σ') => execFuel fuel s₂ σ' defs
      | some (ExecResult.returned v) => pure (ExecResult.returned v)
      | none => none
    | fuel + 1, Stmt.if_ cond then_ else_, σ, defs => do
      let v ← evalExpr cond σ
      match v with
      | Val.bool true  => execFuel fuel then_ σ defs
      | Val.bool false => execFuel fuel else_ σ defs
      | _ => none
    | fuel + 1, Stmt.while cond body, σ, defs => do
      let v ← evalExpr cond σ
      match v with
      | Val.bool true =>
          match execFuel fuel body σ defs with
          | some (ExecResult.normal σ') => execFuel fuel (Stmt.while cond body) σ' defs
          | some (ExecResult.returned w) => pure (ExecResult.returned w)
          | none => none
      | Val.bool false => pure (ExecResult.normal σ)
      | _ => none
    | _ + 1, Stmt.return e, σ, _ => do
      let v ← evalExpr e σ
      pure (ExecResult.returned v)

  def callByValuesFuel : Nat → Store → String → List Val →
      (defs : List Fun := []) → Option Val
    | 0, _, _, _, _ => none
    | fuel + 1, σ, fname, argVals, defs =>
        match findFun defs fname with
        | none => none
        | some fn =>
            match bindParamsIntoStore σ fn.params argVals with
            | none => none
            | some σCall =>
                match execFuel fuel fn.body σCall defs with
                | some (ExecResult.returned v) => some v
                | _ => none
end

private def ensureMainDef (defs : List Fun) (fn : Fun) : List Fun :=
  if defs.any (fun g => g.name = fn.name) then defs else fn :: defs

def execWithDefs (defs : List Fun) (s : Stmt) (σ : Store) (fuel : Nat := 10000) :
    Option ExecResult :=
  execFuel fuel s σ defs

def exec (s : Stmt) (σ : Store) (fuel : Nat := 10000) : Option ExecResult :=
  execFuel fuel s σ

/-- Bind parameters to arguments, returning an initial store. -/
@[simp] def bindParams : List String → List Val → Option Store
  | [], [] => some emptyStore
  | p :: ps, v :: vs => do
      let σ ← bindParams ps vs
      pure (update σ p v)
  | _, _ => none

/-- Execute a function with argument values against an explicit definition list. -/
def runFunWithDefs (defs : List Fun) (fn : Fun) (args : List Val) : Option Val := do
  let σ ← bindParams fn.params args
  let defs' := ensureMainDef defs fn
  match execFuel 10000 fn.body σ defs' with
  | some (ExecResult.normal _) => none
  | some (ExecResult.returned v) => some v
  | none => none

/-- Execute a function with argument values. -/
def runFun (fn : Fun) (args : List Val) : Option Val :=
  runFunWithDefs [fn] fn args

/-- Run the main function of a program. -/
def runProgram (prog : Program) (args : List Val) : Option Val :=
  runFunWithDefs (prog.main :: prog.defs) prog.main args

/-- Specialised helper for single-argument nat→nat functions. -/
def runNatFun (fn : Fun) (n : Nat) : Option Nat := do
  let v ← runFun fn [natToVal n]
  Val.asNat? v

/-- Fragment-only semantics for the nat→nat subset emitted by the compiler. -/
def execFrag : Stmt → Store → Option ExecResult
  | Stmt.return e, σ => do
      let v ← evalExpr e σ
      pure (ExecResult.returned v)
  | Stmt.if_ cond then_ else_, σ => do
      let v ← evalExpr cond σ
      match v with
      | Val.bool true => execFrag then_ σ
      | Val.bool false => execFrag else_ σ
      | _ => none
  | _, _ => none

@[simp] theorem execFrag_return (e : Expr) (σ : Store) :
    execFrag (Stmt.return e) σ
      = (evalExpr e σ).map ExecResult.returned := by
  cases h : evalExpr e σ <;> simp [execFrag, h]

@[simp] theorem execFrag_return_of_eval {e : Expr} {σ : Store} {v : Val}
    (h : evalExpr e σ = some v) :
    execFrag (Stmt.return e) σ = some (ExecResult.returned v) := by
  dsimp [execFrag]
  simp [h]

@[simp] theorem execFrag_if_true
    (cond : Expr) (then_ else_ : Stmt) (σ : Store)
    (h : evalExpr cond σ = some (Val.bool true)) :
    execFrag (Stmt.if_ cond then_ else_) σ = execFrag then_ σ := by
  dsimp [execFrag]
  simp [h]

@[simp] theorem execFrag_if_false
    (cond : Expr) (then_ else_ : Stmt) (σ : Store)
    (h : evalExpr cond σ = some (Val.bool false)) :
    execFrag (Stmt.if_ cond then_ else_) σ = execFrag else_ σ := by
  dsimp [execFrag]
  simp [h]

/-- Fragment-only runner for nat→nat functions. -/
def runNatFunFrag (fn : Fun) (paramName : String) (n : Nat) : Option Nat := do
  guard (fn.params = [paramName])
  let σ : Store := fun x => if x = paramName then some (natToVal n) else none
  match execFrag fn.body σ with
  | some (ExecResult.returned v) => Val.asNat? v
  | _ => none

/-- Fragment-only runner for nat→nat→nat functions (curried as two parameters). -/
def runNat2FunFrag (fn : Fun) (param1 param2 : String)
    (x y : Nat) : Option Nat := do
  guard (fn.params = [param1, param2])
  let σ : Store :=
    fun name =>
      if name = param1 then
        some (natToVal x)
      else if name = param2 then
        some (natToVal y)
      else
        none
  match execFrag fn.body σ with
  | some (ExecResult.returned v) => Val.asNat? v
  | _ => none

/-!
## Total (denotational) semantics (0/1 booleans)

This layer is used as a reference semantics for compilation correctness
statements where the target (tiny C) computes integers and encodes booleans
as `0/1`.

It is intentionally *total* on stores (`String → Int`) and *total* on expression
evaluation (`Expr.eval : Expr → TotalStore → Int`).

Note: the existing `evalExpr/exec/execFrag` above are value-typed (`Val`) and
partial (`Option`) and remain the semantics used by older proofs.
-/

/-- A total store maps variable names to integers. -/
abbrev TotalStore := String → Int

def bindParamsIntoTotalStore : TotalStore → List String → List Int → Option TotalStore
  | σ, [], [] => some σ
  | σ, p :: ps, v :: vs =>
      bindParamsIntoTotalStore (fun y => if y = p then v else σ y) ps vs
  | _, _, _ => none

/-- Total evaluation of MiniC expressions. Booleans are encoded as 0/1. -/
def Expr.eval : Expr → TotalStore → Int
  | .intLit n, _ => n
  | .boolLit b, _ => if b then 1 else 0
  | .var x, σ => σ x
  -- Array constructs are currently erased in the total bridge semantics used by
  -- MiniC→C expression correctness.
  | .arrayLit _, _ => 0
  | .arrayLength _, _ => 0
  | .arrayIndex _ _, _ => 0
  | .structLit _ _, _ => 0
  | .fieldAccess obj field, σ =>
      match obj with
      | .var name => σ (structFieldSlot name field)
      | _ => 0
  | .add e₁ e₂, σ => e₁.eval σ + e₂.eval σ
  | .sub e₁ e₂, σ => e₁.eval σ - e₂.eval σ
  | .mul e₁ e₂, σ => e₁.eval σ * e₂.eval σ
  | .le e₁ e₂, σ => if e₁.eval σ ≤ e₂.eval σ then 1 else 0
  | .eq e₁ e₂, σ => if e₁.eval σ = e₂.eval σ then 1 else 0
  | .not e, σ => if e.eval σ = 0 then 1 else 0
  | .and e₁ e₂, σ => if e₁.eval σ ≠ 0 ∧ e₂.eval σ ≠ 0 then 1 else 0
  | .or e₁ e₂, σ => if e₁.eval σ ≠ 0 ∨ e₂.eval σ ≠ 0 then 1 else 0

/-- Result of executing a MiniC statement under total semantics. -/
inductive ExecResultTotal where
  | normal (σ : TotalStore)
  | returned (v : Int)

/- Big-step execution of MiniC statements with fuel (for while loops). -/
mutual
  def Stmt.execFuel : Nat → Stmt → TotalStore → (defs : List Fun := []) → Option ExecResultTotal
    | 0, _, _, _ => none
    | _ + 1, .skip, σ, _ => some (.normal σ)
    | _ + 1, .return e, σ, _ => some (.returned (e.eval σ))
    | _ + 1, .assign x e, σ, _ => some (.normal (fun y => if y = x then e.eval σ else σ y))
    | _ + 1, .arrayUpdate name idxExpr valExpr, σ, _ =>
      let i := idxExpr.eval σ
      let rhs := valExpr.eval σ
      if i ≥ 0 then
        if i < σ (arrayLengthSlot name) then
          some (.normal (fun y =>
            if y = arrayElemSlot name (Int.toNat i) then rhs else σ y))
        else
          none
      else
        none
    | _ + 1, .structUpdate name field rhsExpr, σ, _ =>
      let rhs := rhsExpr.eval σ
      some (.normal (fun y => if y = structFieldSlot name field then rhs else σ y))
    | fuel + 1, .call fname args ret, σ, defs =>
        let argVals := args.map (fun e => e.eval σ)
        match callByValuesFuelTotal fuel defs σ fname argVals with
        | some rv => some (.normal (fun y => if y = ret then rv else σ y))
        | none => none
    | fuel + 1, .seq s₁ s₂, σ, defs =>
      match s₁.execFuel fuel σ defs with
      | some (.normal σ') => s₂.execFuel fuel σ' defs
      | other => other
    | fuel + 1, .if_ c t e, σ, defs =>
      if c.eval σ ≠ 0 then t.execFuel fuel σ defs else e.execFuel fuel σ defs
    | fuel + 1, .while c b, σ, defs =>
      if c.eval σ = 0 then some (.normal σ)
      else
        match b.execFuel fuel σ defs with
        | some (.normal σ') => (Stmt.while c b).execFuel fuel σ' defs
        | other => other

  def callByValuesFuelTotal : Nat → List Fun → TotalStore → String → List Int → Option Int
    | 0, _, _, _, _ => none
    | fuel + 1, defs, σ, fname, argVals =>
        match findFun defs fname with
        | none => none
        | some fn =>
            match bindParamsIntoTotalStore σ fn.params argVals with
            | none => none
            | some σCall =>
                match Stmt.execFuel fuel fn.body σCall defs with
                | some (.returned v) => some v
                | _ => none
end

/-- Execute with default fuel. -/
def Stmt.exec (s : Stmt) (σ : TotalStore) (fuel : Nat := 10000) : Option ExecResultTotal :=
  s.execFuel fuel σ

/-!
### While-free fragment execution (structural)

This fragment matches the public `HeytingLean.C.execFragC` semantics: it only
supports `return` and `if_` and rejects all other statements.
-/

/-- Fragment execution (no while, structurally recursive). -/
def Stmt.execFrag : Stmt → TotalStore → Option ExecResultTotal
  | .return e, σ => some (.returned (e.eval σ))
  | .if_ c t e, σ => if c.eval σ ≠ 0 then t.execFrag σ else e.execFrag σ
  | _, _ => none

/-! ### Minimal typing for the 0/1 bridge proofs -/

/-- A simple type environment (names → types). -/
abbrev TyEnv := String → Ty

/-- `σ` respects `Γ` when every boolean-typed variable is 0/1 encoded. -/
def StoreRespects (Γ : TyEnv) (σ : TotalStore) : Prop :=
  ∀ x, Γ x = Ty.bool → (σ x = 0 ∨ σ x = 1)

inductive HasType : TyEnv → Expr → Ty → Prop
  | var {Γ} {x} {τ} : Γ x = τ → HasType Γ (.var x) τ
  | intLit {Γ} (n : Int) : HasType Γ (.intLit n) .int
  | boolLit {Γ} (b : Bool) : HasType Γ (.boolLit b) .bool
  | arrayLit {Γ elems} : HasType Γ (.arrayLit elems) (.array .int elems.length)
  | arrayIndex {Γ arr idx n} :
      HasType Γ arr (.array .int n) → HasType Γ idx .int → HasType Γ (.arrayIndex arr idx) .int
  | arrayLength {Γ arr n} :
      HasType Γ arr (.array .int n) → HasType Γ (.arrayLength arr) .int
  | structLit {Γ name fields} :
      HasType Γ (.structLit name fields) (.struct name)
  | fieldAccess {Γ obj name field} :
      HasType Γ obj (.struct name) → HasType Γ (.fieldAccess obj field) .int
  | add {Γ e₁ e₂} : HasType Γ e₁ .int → HasType Γ e₂ .int → HasType Γ (.add e₁ e₂) .int
  | sub {Γ e₁ e₂} : HasType Γ e₁ .int → HasType Γ e₂ .int → HasType Γ (.sub e₁ e₂) .int
  | mul {Γ e₁ e₂} : HasType Γ e₁ .int → HasType Γ e₂ .int → HasType Γ (.mul e₁ e₂) .int
  | le  {Γ e₁ e₂} : HasType Γ e₁ .int → HasType Γ e₂ .int → HasType Γ (.le e₁ e₂) .bool
  | eq  {Γ e₁ e₂ τ} : HasType Γ e₁ τ → HasType Γ e₂ τ → HasType Γ (.eq e₁ e₂) .bool
  | not {Γ e} : HasType Γ e .bool → HasType Γ (.not e) .bool
  | and {Γ e₁ e₂} : HasType Γ e₁ .bool → HasType Γ e₂ .bool → HasType Γ (.and e₁ e₂) .bool
  | or  {Γ e₁ e₂} : HasType Γ e₁ .bool → HasType Γ e₂ .bool → HasType Γ (.or e₁ e₂) .bool

theorem eval_is01_of_hasType_bool {Γ : TyEnv} {σ : TotalStore} {e : Expr}
    (hσ : StoreRespects Γ σ) (ht : HasType Γ e .bool) :
    e.eval σ = 0 ∨ e.eval σ = 1 := by
  cases ht with
  | var hx =>
      exact hσ _ hx
  | boolLit b =>
      cases b <;> simp [Expr.eval]
  | le ht1 ht2 =>
      rename_i e₁ e₂
      by_cases h : e₁.eval σ ≤ e₂.eval σ <;> simp [Expr.eval, h]
  | eq ht1 ht2 =>
      rename_i e₁ e₂ τ
      by_cases h : e₁.eval σ = e₂.eval σ <;> simp [Expr.eval, h]
  | not ht =>
      rename_i e
      by_cases h : e.eval σ = 0 <;> simp [Expr.eval, h]
  | and ht1 ht2 =>
      rename_i e₁ e₂
      by_cases h : (e₁.eval σ ≠ 0 ∧ e₂.eval σ ≠ 0) <;> simp [Expr.eval, h]
  | or ht1 ht2 =>
      rename_i e₁ e₂
      by_cases h : (e₁.eval σ ≠ 0 ∨ e₂.eval σ ≠ 0) <;> simp [Expr.eval, h]

end MiniC
end HeytingLean
