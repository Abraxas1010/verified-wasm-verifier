import Std
import HeytingLean.BountyHunter.Solc.YulTextMini.Types
import HeytingLean.BountyHunter.AlgebraIR.Types
import HeytingLean.BountyHunter.AlgebraIR.SlotRef

/-!
# HeytingLean.BountyHunter.Solc.YulTextMini.Effects

Shared (deterministic) extraction of `AlgebraIR.Effect`s from the minimal Yul-text AST.

This is used by:
- `ToAlgebraIR` (to label CFG nodes with effects), and
- `Solc.Audit` (to compute expected effects from the AST).

It includes a lightweight environment that can substitute `let`/`:=`-bound variables
when they are used as storage slot expressions, so `sstore(tmpSlot, ...)` can be
reported as `storageWriteDyn(<expanded expr>)` instead of `storageWriteDyn(ident tmpSlot)`.
-/

namespace HeytingLean.BountyHunter.Solc.YulTextMini

open HeytingLean.BountyHunter.AlgebraIR

abbrev Env := Std.HashMap String Expr

def envEmpty : Env := Std.HashMap.emptyWithCapacity 8

partial def exprRender (e : Expr) : String :=
  match e with
  | .ident name => name
  | .nat n => toString n
  | .str s => s!"\"{s}\""
  | .bool true => "true"
  | .bool false => "false"
  | .call fn args =>
      let inner := String.intercalate "," (args.toList.map exprRender)
      s!"{fn}({inner})"

private partial def substExpr (env : Env) (e : Expr) (fuel : Nat := 20) : Expr :=
  if fuel = 0 then
    e
  else
    match e with
    | .ident name =>
        match env.get? name with
        | none => e
        | some e' => substExpr env e' (fuel - 1)
    | .call fn args =>
        .call fn (args.map (fun a => substExpr env a (fuel - 1)))
    | other => other

private def natBinOp? (fn : String) : Option (Nat → Nat → Nat) :=
  match fn with
  | "add" => some (· + ·)
  | "sub" => some (fun a b => a - b)
  | "mul" => some (· * ·)
  | "shl" => some (fun a b => b <<< a)
  | "shr" => some (fun a b => b >>> a)
  | "and" => some (fun a b => Nat.land a b)
  | "or" => some (fun a b => Nat.lor a b)
  | "xor" => some (fun a b => Nat.xor a b)
  | _ => none

private partial def constFoldNat? (env : Env) (e : Expr) (fuel : Nat := 30) : Option Nat :=
  if fuel = 0 then
    none
  else
    match substExpr env e fuel with
    | .nat n => some n
    | .call fn args =>
        match natBinOp? fn, args[0]?, args[1]? with
        | some op, some a, some b =>
            match constFoldNat? env a (fuel - 1), constFoldNat? env b (fuel - 1) with
            | some x, some y => some (op x y)
            | _, _ => none
        | _, _, _ => none
    | _ => none

private def keyOfExpr (env : Env) (e : Expr) : SlotKey :=
  match substExpr env e 10 with
  | .call "caller" #[] => .caller
  | .ident "caller" => .caller
  | .call "address" #[.ident "this"] => .this
  | .ident "address(this)" => .this
  | .nat n => .nat n
  | .ident nm => .ident nm
  | other => .raw (exprRender other)

partial def slotRefOfExpr (env : Env) (e : Expr) (fuel : Nat := 25) : HeytingLean.BountyHunter.AlgebraIR.SlotRef :=
  if fuel = 0 then
    .raw (exprRender (substExpr env e 1))
  else
    match constFoldNat? env e with
    | some n => .literal n
    | none =>
        match substExpr env e 20 with
        | .call fn args =>
            if fn.startsWith "convert_array_" then
              match args[0]? with
              | some a => slotRefOfExpr env a (fuel - 1)
              | none => .raw (exprRender (.call fn args))
            else if fn = "keccak" then
              match args[0]? with
              | some a => .keccak (slotRefOfExpr env a (fuel - 1))
              | none => .raw (exprRender (.call fn args))
            else if fn = "keccak256" then
              -- Solc often emits `keccak256(ptr,len)` for mapping/struct slot computations.
              -- We don't attempt to decode the memory contents; we just keep a stable, parseable
              -- token so downstream grouping can treat these as related dynamic slots.
              match args[0]?, args[1]? with
              | some ptrE, some lenE =>
                  let ptrS := exprRender (substExpr env ptrE 5)
                  let lenS := exprRender (substExpr env lenE 5)
                  .keccak (.raw s!"mem[{ptrS},{lenS}]")
              | _, _ =>
                  .raw (exprRender (.call fn args))
            else if fn.startsWith "mapping_index_access" then
              match args[0]?, args[1]? with
              | some baseE, some keyE =>
                  let base := slotRefOfExpr env baseE (fuel - 1)
                  let key := keyOfExpr env keyE
                  .mapping base key
              | _, _ => .raw (exprRender (.call fn args))
            else if fn = "add" then
              match args[0]?, args[1]? with
              | some a, some b =>
                  match slotRefOfExpr env a (fuel - 1), constFoldNat? env b with
                  | r, some off => .add r (.nat off)
                  | r, none => .add r (.key (keyOfExpr env b))
              | _, _ => .raw (exprRender (.call fn args))
            else
              .raw (exprRender (.call fn args))
        | other => .raw (exprRender other)

private def slotEffect (mkConst : Nat → Effect) (mkDyn : String → Effect) (env : Env) (slotExpr : Expr) : Effect :=
  match slotRefOfExpr env slotExpr with
  | .literal n => mkConst n
  | r => mkDyn (HeytingLean.BountyHunter.AlgebraIR.slotRefToString r)

partial def effectsOfExpr (env : Env) : Expr → Array Effect
  | .ident _ => #[]
  | .nat _ => #[]
  | .str _ => #[]
  | .bool _ => #[]
  | .call fn args =>
      let nested := args.foldl (fun acc a => acc ++ effectsOfExpr env a) #[]
      let eff :=
        match fn, args[0]? with
        | "sload", some slotE =>
            #[slotEffect Effect.storageRead Effect.storageReadDyn env slotE]
        | "sstore", some slotE =>
            #[slotEffect Effect.storageWrite Effect.storageWriteDyn env slotE]
        | "call", _ => #[Effect.boundaryCall "call"]
        | "delegatecall", _ => #[Effect.boundaryCall "delegatecall"]
        | "staticcall", _ => #[Effect.boundaryCall "staticcall"]
        | "callcode", _ => #[Effect.boundaryCall "callcode"]
        | _, _ =>
            if fn.startsWith "update_storage_value_offset_" then
              match args[0]? with
              | some slotE =>
                  let base := slotRefOfExpr env slotE
                  -- Try to capture packed-field updates by parsing the byte offset + value size from the helper name.
                  let packed? : Option (Nat × Nat) :=
                    let off? : Option Nat :=
                      match (fn.drop "update_storage_value_offset_".length).splitOn "_" with
                      | offStr :: _ => offStr.toNat?
                      | _ => none
                    let natPrefix? (s : String) : Option Nat :=
                      let rec go (cs : List Char) (acc : List Char) : Option Nat :=
                        match cs with
                        | [] =>
                            if acc.isEmpty then none else (String.mk acc.reverse).toNat?
                        | c :: rest =>
                            if c.isDigit then
                              go rest (c :: acc)
                            else
                              if acc.isEmpty then none else (String.mk acc.reverse).toNat?
                      go s.data []
                    let bits? : Option Nat :=
                      let parts := (fn.splitOn "t_uint").toArray
                      match parts[1]? with
                      | none => none
                      | some after => natPrefix? after
                    match off?, bits? with
                    | some off, some bits =>
                        if bits % 8 = 0 && bits ≤ 256 then
                          some (off, bits / 8)
                        else
                          none
                    | _, _ => none
                  match packed? with
                  | some (off, bytes) =>
                      if off = 0 && bytes = 32 then
                        #[slotEffect Effect.storageWrite Effect.storageWriteDyn env slotE]
                      else
                        #[Effect.storageWriteDyn (HeytingLean.BountyHunter.AlgebraIR.slotRefToString (.packed base off bytes))]
                  | none =>
                      #[slotEffect Effect.storageWrite Effect.storageWriteDyn env slotE]
              | none => #[]
            else if fn.startsWith "update_storage_value_" then
              -- Some solc helpers pass (slot, offset, value) without encoding the offset in the name.
              match args[0]? with
              | some slotE => #[slotEffect Effect.storageWrite Effect.storageWriteDyn env slotE]
              | none => #[]
            else if fn.startsWith "array_push_from_" then
              -- Conservatively model array push as at least writing the array's base slot (length).
              match args[0]? with
              | some selfSlot => #[slotEffect Effect.storageWrite Effect.storageWriteDyn env selfSlot]
              | none => #[]
            else if fn.startsWith "read_from_storage_offset_" then
              match args[0]? with
              | some slotE => #[slotEffect Effect.storageRead Effect.storageReadDyn env slotE]
              | none => #[]
            else if fn.startsWith "read_from_storage_split_offset_" then
              match args[0]? with
              | some slotE => #[slotEffect Effect.storageRead Effect.storageReadDyn env slotE]
              | none => #[]
            else if fn.startsWith "load_from_storage_offset_" then
              match args[0]? with
              | some slotE => #[slotEffect Effect.storageRead Effect.storageReadDyn env slotE]
              | none => #[]
            else
              #[]
      nested ++ eff

/-! Like `effectsOfExpr`, but allows a caller-provided summary of effects for internal calls.

This is used to conservatively inline storage/boundary effects for internal helper calls
(e.g. modifier plumbing such as ReentrancyGuard enter/exit), which would otherwise be
opaque in an intraprocedural scan.
-/
partial def effectsOfExprWithInline (inline : String → Array Effect) (env : Env) (e : Expr) : Array Effect :=
  let base := effectsOfExpr env e
  match substExpr env e 1 with
  | .call fn _ => base ++ inline fn
  | _ => base

def updateEnv (env : Env) (s : Stmt) : Env :=
  match s with
  | .let_ name rhs => env.insert name rhs
  | .letMany names rhs =>
      -- Best-effort: bind the slot component of array index access so storage updates can see it.
      match names[0]?, names[1]?, rhs with
      | some a, some b, .call fn args =>
          if (fn.splitOn "storage_array_index_access").length > 1 then
            match args[0]?, args[1]? with
            | some baseE, some idxE =>
                let baseE :=
                  -- Dynamic arrays use data starting at `keccak(baseSlot)`.
                  if (fn.splitOn "$dyn_storage").length > 1 then
                    .call "keccak" #[baseE]
                  else
                    baseE
                env.insert a (.call "add" #[baseE, idxE]) |>.insert b (.nat 0)
            | _, _ => env
          else
            env
      | _, _, _ => env
  | .assign name rhs => env.insert name rhs
  | .assignMany names _rhs =>
      -- We do not model tuple semantics. Conservatively drop bindings for the assigned names.
      names.foldl (fun e n => e.erase n) env
  | _ => env

mutual
  partial def expectedEffectsFromStmt (env : Env) (s : Stmt) : Array Effect :=
    match s with
    | .let_ _ rhs => effectsOfExpr env rhs
    | .letMany _ rhs => effectsOfExpr env rhs
    | .assign _ rhs => effectsOfExpr env rhs
    | .assignMany _ rhs => effectsOfExpr env rhs
    | .expr e => effectsOfExpr env e
    | .block ss => expectedEffectsFromStmts env ss
    | .if_ cond thenStmts =>
        -- Do not propagate env changes from inside the branch.
        effectsOfExpr env cond ++ expectedEffectsFromStmts env thenStmts
    | .switch_ scrut cases def? =>
        let fromCases :=
          cases.foldl (fun acc c => acc ++ expectedEffectsFromStmts env c.2) #[]
        let fromDef :=
          match def? with
          | none => #[]
          | some ss => expectedEffectsFromStmts env ss
        effectsOfExpr env scrut ++ fromCases ++ fromDef
    | .for_ init cond post body =>
        -- Conservative: propagate env through init only.
        let initEff := expectedEffectsFromStmts env init
        let env2 := init.foldl (fun e s => updateEnv e s) env
        let condEff := effectsOfExpr env2 cond
        initEff ++ condEff ++ expectedEffectsFromStmts env2 post ++ expectedEffectsFromStmts env2 body
    | .break => #[]
    | .continue => #[]
    | .return_ _ => #[]
    | .revert _ => #[]
    | .leave => #[]

  partial def expectedEffectsFromStmts (env0 : Env) (ss : Array Stmt) : Array Effect :=
    Id.run do
      let mut env := env0
      let mut out : Array Effect := #[]
      for s in ss do
        out := out ++ expectedEffectsFromStmt env s
        env := updateEnv env s
      pure out
end

end HeytingLean.BountyHunter.Solc.YulTextMini
