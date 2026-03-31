import HeytingLean.Hyperseries.Eval
import HeytingLean.Matula.Compute.Decoder
import HeytingLean.Matula.Compute.Encoder

namespace HeytingLean
namespace Matula
namespace Extension
namespace Hyperseries

open HeytingLean.Hyperseries

mutual
  /-- Structural embedding of a rooted tree into hyperseries syntax. -/
  def toHExpr : RTree → HExpr
    | .leaf => HExpr.X
    | .node children => toHExprChildren children

  /-- Right-associated child-product encoding used by `toHExpr`. -/
  private def toHExprChildren : List RTree → HExpr
    | [] => HExpr.C 1
    | t :: ts => HExpr.mul (HExpr.exp (toHExpr t)) (toHExprChildren ts)
end

/--
Partial inverse for `toHExpr` on its image.

`X` decodes to `.leaf`; multiplicative-exp chains decode to `.node children`.
-/
def fromHExpr : HExpr → Option RTree
  | ExprC.X => some .leaf
  | ExprC.C 1 => some (.node [])
  | ExprC.mul (ExprC.exp child) rest => do
      let tChild ← fromHExpr child
      let tRest ← fromHExpr rest
      match tRest with
      | .node children => pure (.node (tChild :: children))
      | .leaf => none
  | _ => none

@[simp] theorem toHExprChildren_nil : toHExprChildren [] = HExpr.C 1 := rfl
@[simp] theorem toHExprChildren_cons (t : RTree) (ts : List RTree) :
    toHExprChildren (t :: ts) = HExpr.mul (HExpr.exp (toHExpr t)) (toHExprChildren ts) := rfl

@[simp] theorem toHExpr_leaf : toHExpr .leaf = HExpr.X := by
  simp [toHExpr]

@[simp] theorem toHExpr_single_leaf :
    toHExpr (.node [.leaf]) = HExpr.mul (HExpr.exp HExpr.X) (HExpr.C 1) := by
  simp [toHExpr]

@[simp] theorem eval_toHExpr_leaf_surreal :
    HExpr.eval surrealModel (toHExpr .leaf) = omegaSurreal := by
  simp

mutual
  @[simp] theorem fromHExpr_toHExpr : ∀ t : RTree, fromHExpr (toHExpr t) = some t
    | .leaf => by
        simp [toHExpr, fromHExpr]
    | .node children => by
        simpa [toHExpr] using fromHExpr_toHExprChildren children

  @[simp] theorem fromHExpr_toHExprChildren :
      ∀ children : List RTree, fromHExpr (toHExprChildren children) = some (.node children)
    | [] => by
        simp [toHExprChildren, fromHExpr]
    | t :: ts => by
        simp [toHExprChildren, fromHExpr, fromHExpr_toHExpr t, fromHExpr_toHExprChildren ts]
end

theorem toHExpr_injective : Function.Injective toHExpr := by
  intro t u h
  have h' := congrArg fromHExpr h
  simpa using h'

/-- Code-level embedding: represent Matula code as an integer constant expression. -/
def toCodeExpr (t : RTree) : HExpr :=
  HExpr.C (matulaEncode t)

/-- Recover a natural from a hyperseries expression when it is a nonnegative constant. -/
def fromCodeExpr : HExpr → Option Nat
  | ExprC.C z =>
      if 0 <= z then
        some z.toNat
      else
        none
  | _ => none

/-- Decode a rooted tree from a constant-coded hyperseries expression. -/
def decodeCodeExpr (e : HExpr) : Option RTree := do
  let n ← fromCodeExpr e
  pure (matulaDecode n)

@[simp] theorem fromCodeExpr_toCodeExpr (t : RTree) :
    fromCodeExpr (toCodeExpr t) = some (matulaEncode t) := by
  simp [fromCodeExpr, toCodeExpr]

@[simp] theorem decodeCodeExpr_toCodeExpr (t : RTree) :
    decodeCodeExpr (toCodeExpr t) = some (matulaDecode (matulaEncode t)) := by
  simp [decodeCodeExpr]

@[simp] theorem fromCodeExpr_nonconst_none (e : HExpr) (h : (∃ z : Int, e = ExprC.C z) → False) :
    fromCodeExpr e = none := by
  cases e with
  | C z =>
      exfalso
      exact h (Exists.intro z rfl)
  | X =>
      simp [fromCodeExpr]
  | add a b =>
      simp [fromCodeExpr]
  | mul a b =>
      simp [fromCodeExpr]
  | neg a =>
      simp [fromCodeExpr]
  | exp a =>
      simp [fromCodeExpr]
  | log a =>
      simp [fromCodeExpr]
  | hyperExp α a =>
      simp [fromCodeExpr]
  | hyperLog α a =>
      simp [fromCodeExpr]

@[simp] theorem eval_toCodeExpr_surreal (t : RTree) :
    HExpr.eval surrealModel (toCodeExpr t) = ((matulaEncode t : Nat) : Surreal) := by
  simp [toCodeExpr]

end Hyperseries
end Extension
end Matula
end HeytingLean
