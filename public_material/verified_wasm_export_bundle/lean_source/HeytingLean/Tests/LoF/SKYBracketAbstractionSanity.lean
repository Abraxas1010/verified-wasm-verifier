import HeytingLean.LoF.Combinators.BracketAbstraction
import HeytingLean.LoF.Combinators.BracketAbstractionCorrectness

/-!
Sanity checks for `HeytingLean.LoF.Combinators.BracketAbstraction`.

This is compile-only + small definitional checks on the compiler output.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Combinators.Bracket

namespace SKYBracketAbstractionSanity

def tId : Lam String :=
  .lam "x" (.var "x")

example : Lam.compile (Var := String) tId = CExp.I := by
  simp [tId, Lam.compile, Lam.compileClassic, CExp.bracket, CExp.I]

example : Lam.compileClosedClassic? (Var := String) tId = some Comb.I := by
  simp [Lam.compileClosedClassic?, tId, Lam.compileClassic, CExp.erase?, CExp.bracket, CExp.I, Comb.I]

example : Lam.compileClosedWithMode? (Var := String) .bulk tId = some Comb.I := by
  native_decide

example : Lam.compileClosed? (Var := String) tId = some Comb.I := by
  native_decide

def tConstK : Lam String :=
  .lam "x" (.lam "y" (.var "x"))

example : Lam.compileClosedClassic? (Var := String) tConstK = some Comb.K := by
  simp [Lam.compileClosedClassic?, tConstK, Lam.compileClassic, CExp.erase?, CExp.bracket, CExp.opt, CExp.occurs, CExp.I]

example : Lam.compileClosedWithMode? (Var := String) .bulk tConstK = some Comb.K := by
  native_decide

example : Lam.compileClosed? (Var := String) tConstK = some Comb.K := by
  native_decide

def tScottNat0 : Lam String :=
  .lam "z" (.lam "s" (.var "z"))

def tBulkCounterexample : Lam String :=
  .lam "a" (.lam "b" (.app (.var "a") tScottNat0))

example :
    Lam.compileClosedClassic? (Var := String) tBulkCounterexample ≠
      Lam.compileClosedWithMode? (Var := String) .bulk tBulkCounterexample := by
  native_decide

example :
    Lam.compileClosed? (Var := String) tBulkCounterexample =
      Lam.compileClosedClassic? (Var := String) tBulkCounterexample := by
  native_decide

/-! ### β-simulation sanity checks (Phase 2 Sprint 3) -/

open HeytingLean.LoF.Combinators.Bracket.CExp

def rho : String → Comb := fun s => if s = "f" then Comb.S else Comb.K

def eEta : CExp String :=
  .app (.var "f") (.var "x")

-- Turner η-like optimization: `[x] (f x) = f` when `x` does not occur in `f`.
example : bracket (Var := String) "x" eEta = CExp.var "f" := by
  simp [eEta, CExp.bracket, CExp.opt, CExp.occurs, CExp.I]

example (v : Comb) :
    ∃ r : Comb, Comb.Steps (Comb.app (denote rho (bracket "x" eEta)) v) r ∧
      Comb.Steps (denote (update rho "x" v) eEta) r := by
  simpa [eEta] using (bracket_beta_join (ρ := rho) (x := "x") (e := eEta) (v := v))

-- Turner composition optimization: `S (K e) (K f) ↦ K (e f)`.
def eCompF : CExp String :=
  .app (.app CExp.K (.var "y")) (.var "x")

def eCompA : CExp String :=
  .app (.app CExp.K (.var "z")) (.var "x")

def eComp : CExp String :=
  .app eCompF eCompA

example : bracket (Var := String) "x" eComp = CExp.app CExp.K (CExp.app (.var "y") (.var "z")) := by
  simp [eComp, eCompF, eCompA, CExp.bracket, CExp.opt, CExp.occurs, CExp.I]

example (v : Comb) :
    ∃ r : Comb, Comb.Steps (Comb.app (denote rho (bracket "x" eComp)) v) r ∧
      Comb.Steps (denote (update rho "x" v) eComp) r := by
  simpa [eComp, eCompF, eCompA] using
    (bracket_beta_join (ρ := rho) (x := "x") (e := eComp) (v := v))

end SKYBracketAbstractionSanity

end LoF
end Tests
end HeytingLean
