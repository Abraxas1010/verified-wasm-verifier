import HeytingLean.ATheory.AssemblyCore

/-
# AssemblyRoundTrip: contracts for assembly objects

This module specialises the generic `RoundTrip` style to the Assembly Theory
layer. It defines the basic Deduction / Abduction / Induction shapes over
assembly objects in a way that is compatible with the existing core, without
committing to heavy proofs or implementations yet.
-/

namespace HeytingLean
namespace Contracts
namespace Assembly

open HeytingLean.ATheory

universe u

variable {α : Type u}

/-- Deduction in the assembly setting: joining two assembly objects. This is
just the syntactic `Obj.join` constructor. -/
def Ded (x y : Obj α) : Obj α :=
  Obj.join x y

/-- Abduction in the assembly setting: given a target `x` and an observed
sub-assembly `w`, attempt to infer a complementary sub-assembly that could
pair with `w` to build `x`.

This is a best-effort, syntax-directed residual:
- if `x = join w y` or `x = join y w`, we return `y`;
- otherwise we return `x` itself (no informative residual found).

This keeps the interface executable and non-crashing while remaining
compatible with later, rule-aware abduction algorithms. -/
noncomputable def Abd (x w : Obj α) : Obj α := by
  classical
  cases x with
  | base a => exact Obj.base a
  | join a b =>
      if h : w = a then
        exact b
      else if h' : w = b then
        exact a
      else
        exact Obj.join a b

/-- Extract all primitive parts appearing in an assembly object. -/
def prims : Obj α → List α
  | Obj.base a   => [a]
  | Obj.join x y => prims x ++ prims y

/-- Induction in the assembly setting: infer a permissive rule set from observed
assemblies `B` and `C`.

This returns the maximal rules compatible with the observed primitive alphabet:
any pair of primitives may compose to any primitive that appeared in `B` or `C`.
This is intentionally simple but already nontrivial, executable, and suitable
for downstream QA and pipeline wiring. -/
noncomputable def Ind (B C : Obj α) : Rules α := by
  classical
  let allowed : Finset α := (prims B ++ prims C).toFinset
  exact { compose := fun _ _ => allowed }

end Assembly
end Contracts
end HeytingLean
