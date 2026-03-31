import HeytingLean.C.Syntax
import HeytingLean.MiniC.SDE
import HeytingLean.MiniC.ToC
import HeytingLean.MiniC.ToLeanCP
import HeytingLean.LeanCP.Lang.CDecl
import HeytingLean.Quantum.TWA.ToSDE

/-!
# TWA → SDE → MiniC (Phase 3 wrapper)

Phase 2 builds a *mathematical* SDE interface over `ℝ` (good for algebraic invariants).
Phase 3 introduces a compilable MiniC back-end for SDE stepping, but it requires drift/diffusion
to be supplied as **MiniC expressions** (an explicit discretization / approximation boundary).

This file defines a convenience record `CompiledTWA` that ties together:
- a TWA spec,
- its ideal real-valued SDE,
- a compilable (integer) codegen approximation,
- the generated MiniC program (and its C-compiled counterpart),
- and an explicit correctness proposition to be discharged by later phases.
-/

namespace HeytingLean
namespace Quantum
namespace TWA

open HeytingLean.MiniC

/-- A minimal “C program” container for the existing tiny C AST. -/
structure CProgram where
  defs : List HeytingLean.C.CFun
  main : HeytingLean.C.CFun

namespace CProgram

def ofMiniC (p : MiniC.Program) : CProgram :=
  { defs := p.defs.map MiniC.ToC.compileFun
    main := MiniC.ToC.compileFun p.main }

end CProgram

/-- Phase 3 wrapper bundling the (ideal) real SDE and a compilable MiniC approximation. -/
structure CompiledTWA (S : LindbladSpec) where
  /-- TWA dynamics data (Phase 2 interface). -/
  dyn : Dynamics S

  /-- The ideal real-valued SDE system induced by `dyn`. -/
  sdeReal : HeytingLean.LambdaIR.SDE.SDESystem (StateIndex S.N) (Fin S.nJumps) :=
    dyn.toSDESystem

  /-- A compilable (integer) approximation of the drift/diffusion. -/
  sdeCodegen : MiniC.SDE.CompilableSDESystem (StateIndex S.N) (Fin S.nJumps)

  /-- Number of unrolled steps in the generated `simulate_*` functions. -/
  steps : Nat := 0

  /-- Generated MiniC program containing drift/diffusion/step/simulate families. -/
  minic : MiniC.Program :=
    MiniC.SDE.translateSDESystem (ι := StateIndex S.N) (κ := Fin S.nJumps) sdeCodegen steps

  /-- Compiled tiny-C AST obtained from the MiniC program. -/
  c : CProgram := CProgram.ofMiniC minic

  /-- Checked LeanCP-owned C declarations obtained from the same MiniC program. -/
  leanCP : Except MiniC.ToC.CompileError LeanCP.CProgramDecl :=
    MiniC.ToLeanCP.compileProgramDeclChecked minic

  /-- Correctness hook: relates `sdeReal` to the integer codegen approximation. -/
  correctness : Prop

end TWA
end Quantum
end HeytingLean
