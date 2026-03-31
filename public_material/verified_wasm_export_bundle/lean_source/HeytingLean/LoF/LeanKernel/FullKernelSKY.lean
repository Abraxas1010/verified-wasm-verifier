import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.LeanKernel.EnvironmentSKY
import HeytingLean.LoF.LeanKernel.WHNFDeltaSKY
import HeytingLean.LoF.LeanKernel.WHNFIotaSKY
import HeytingLean.LoF.LeanKernel.DefEqSKY
import HeytingLean.LoF.LeanKernel.InferSKY
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY

/-!
# LeanKernel.FullKernelSKY (Phase 24)

Integration bundle for the “computation plane” kernel that combines:
- β/ζ WHNF (Phase 16),
- δ-reduction via an encoded constant environment (Phase 22 + Phase 21),
- ι-reduction via encoded `casesOn` rules (Phase 23),
- definitional equality (Phase 17) and inference/checking (Phase 18) parameterized by the full WHNF.

This module mirrors `KernelSKY` (Phase 19) but adds explicit `env` and `rules`
arguments (both Scott-encoded data accessible from SKY).
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

open HeytingLean.LoF
open HeytingLean.LoF.Combinators

namespace FullKernelSKY

open HeytingLean.LoF.LeanKernel.WHNFSKY
open HeytingLean.LoF.LeanKernel.WHNFSKY.L

abbrev L : Type := WHNFSKY.L
abbrev E : Type := Expr Nat Unit Unit Unit

/-! ## Full WHNF (β/ζ/δ/ι) as a λ term -/

def whnfStepFullSky : L :=
  lam3 "env" "rules" "e" <|
    optCase (app2 WHNFIotaSKY.iotaStepSky (v "rules") (v "e"))
      (app2 WHNFDeltaSKY.whnfStepDeltaSky (v "env") (v "e"))
      (lam "e'" (optSome (v "e'")))

def whnfFullSky : L :=
  app .Y <|
    lam "self" <|
      lam "env" <|
        lam "rules" <|
          lam "fuel" <|
            lam "e" <|
              natCase (v "fuel")
                (v "e")
                (lam "n" <|
                  optCase (app3 whnfStepFullSky (v "env") (v "rules") (v "e"))
                    (v "e")
                    (lam "e'"
                      (app4 (v "self") (v "env") (v "rules") (v "n") (v "e'"))))

/-! ## Hooks to parameterize Phase 17/18 algorithms -/

def constTypeFromEnv : L :=
  /- `InferSKY.inferSkyWith` expects `constType? : Name → List ULevel → Option Expr`.
     The Phase 21 environment is already instantiated at a fixed `us`, so we ignore the `us` argument. -/
  lam3 "env" "c" "us" (app2 EnvironmentSKY.constType? (v "env") (v "c"))

def whnfFromEnvRules : L :=
  /- A closure `fuel → Expr → Expr` capturing `env` and `rules`. -/
  lam2 "env" "rules" <|
    lam2 "fuel" "e" (app4 whnfFullSky (v "env") (v "rules") (v "fuel") (v "e"))

def isDefEqFullSky : L :=
  lam2 "env" "rules" <|
    DefEqSKY.isDefEqSkyWith (app2 whnfFromEnvRules (v "env") (v "rules"))

def inferFullSky : L :=
  lam2 "env" "rules" <|
    let whnf := app2 whnfFromEnvRules (v "env") (v "rules")
    let isDefEq := DefEqSKY.isDefEqSkyWith whnf
    let constType? := app constTypeFromEnv (v "env")
    let litTypeNone := lam "l" optNone
    InferSKY.inferSkyWith constType? litTypeNone whnf isDefEq

def checkFullSky : L :=
  lam2 "env" "rules" <|
    let whnf := app2 whnfFromEnvRules (v "env") (v "rules")
    let isDefEq := DefEqSKY.isDefEqSkyWith whnf
    let constType? := app constTypeFromEnv (v "env")
    let litTypeNone := lam "l" optNone
    InferSKY.checkSkyWith constType? litTypeNone whnf isDefEq

def litTypeByNameIdsSky (natName stringName : L) : L :=
  let emptyLevels := InferSKY.listNil
  let natTyL := exprConst natName emptyLevels
  let stringTyL := exprConst stringName emptyLevels
  let natCase := lam "n" <| optSome natTyL
  let stringCase := lam "s" <| optSome stringTyL
  lam "l" <|
    app2 (v "l") natCase stringCase

def inferFullSkyWithLitTypeIds : L :=
  lam4 "env" "rules" "natName" "stringName" <|
    let whnf := app2 whnfFromEnvRules (v "env") (v "rules")
    let isDefEq := DefEqSKY.isDefEqSkyWith whnf
    let constType? := app constTypeFromEnv (v "env")
    let litType? := litTypeByNameIdsSky (v "natName") (v "stringName")
    InferSKY.inferSkyWith constType? litType? whnf isDefEq

def checkFullSkyWithLitTypeIds : L :=
  lam4 "env" "rules" "natName" "stringName" <|
    let whnf := app2 whnfFromEnvRules (v "env") (v "rules")
    let isDefEq := DefEqSKY.isDefEqSkyWith whnf
    let constType? := app constTypeFromEnv (v "env")
    let litType? := litTypeByNameIdsSky (v "natName") (v "stringName")
    InferSKY.checkSkyWith constType? litType? whnf isDefEq

def optExprIsSomeSky : L :=
  lam "o" <|
    optCase (v "o") fls (lam "e" tru)

def optExprIsSomeSortSky : L :=
  let false4 :=
    lam "a" <| lam "b" <| lam "c" <| lam "d" fls
  let false5 :=
    lam "a" <| lam "b" <| lam "c" <| lam "d" <| lam "e" fls
  lam "o" <|
    optCase (v "o") fls <|
      lam "e" <|
        exprCase (v "e")
          (lam "i" fls)
          (lam "m" fls)
          (lam "u" tru)
          (lam "c" <| lam "us" fls)
          (lam "f" <| lam "a" fls)
          false4
          false4
          false5
          (lam "l" fls)

def ulevelIsZeroSky : L :=
  app .Y <|
    lam "self" <|
      let andSky := lam "p" <| lam "q" <| app2 (v "p") (v "q") fls
      lam "u" <|
        app6
          (v "u")
          tru
          (lam "u1" fls)
          (lam "a" <| lam "b" <| app2 andSky (app (v "self") (v "a")) (app (v "self") (v "b")))
          (lam "a" <| lam "b" <| app (v "self") (v "b"))
          (lam "p" fls)
          (lam "m1" fls)

def optExprIsSomeSortZeroSky : L :=
  let false4 :=
    lam "a" <| lam "b" <| lam "c" <| lam "d" fls
  let false5 :=
    lam "a" <| lam "b" <| lam "c" <| lam "d" <| lam "e" fls
  lam "o" <|
    optCase (v "o") fls <|
      lam "e" <|
        exprCase (v "e")
          (lam "i" fls)
          (lam "m" fls)
          ulevelIsZeroSky
          (lam "c" <| lam "us" fls)
          (lam "f" <| lam "a" fls)
          false4
          false4
          false5
          (lam "l" fls)

def exprIsSortZeroSky : L :=
  let false4 :=
    lam "a" <| lam "b" <| lam "c" <| lam "d" fls
  let false5 :=
    lam "a" <| lam "b" <| lam "c" <| lam "d" <| lam "e" fls
  lam "e" <|
    exprCase (v "e")
      (lam "i" fls)
      (lam "m" fls)
      ulevelIsZeroSky
      (lam "c" <| lam "us" fls)
      (lam "f" <| lam "a" fls)
      false4
      false4
      false5
      (lam "l" fls)

def inferIsSomeSortZeroFullSkyWithLitTypeIds : L :=
  lam4 "env" "rules" "natName" "stringName" <|
    let infer :=
      app4 inferFullSkyWithLitTypeIds
        (v "env")
        (v "rules")
        (v "natName")
        (v "stringName")
    lam3 "fuel" "ctx" "e" <|
      optCase (app3 infer (v "fuel") (v "ctx") (v "e"))
        fls
        (lam "out" <| app exprIsSortZeroSky (v "out"))

/-! ## Closed compilation bundle -/

def compileClosedWithMode? (mode : Bracket.BracketMode) (t : L) : Option Comb :=
  match mode with
  | .classic => Bracket.Lam.compileClosedClassic? t
  | .bulk => Bracket.Lam.compileClosedClassic? t

def compileClosed? (t : L) : Option Comb :=
  compileClosedWithMode? .classic t

def emptyCtxCombWithMode? (mode : Bracket.BracketMode) : Option Comb :=
  compileClosedWithMode? mode InferSKY.listNil

def emptyCtxComb? : Option Comb :=
  emptyCtxCombWithMode? .classic

def whnfFullCombWithMode? (mode : Bracket.BracketMode) : Option Comb :=
  compileClosedWithMode? mode whnfFullSky

def whnfFullComb? : Option Comb :=
  whnfFullCombWithMode? .classic

def isDefEqFullCombWithMode? (mode : Bracket.BracketMode) : Option Comb :=
  compileClosedWithMode? mode isDefEqFullSky

def isDefEqFullComb? : Option Comb :=
  isDefEqFullCombWithMode? .classic

def inferFullCombWithMode? (mode : Bracket.BracketMode) : Option Comb :=
  compileClosedWithMode? mode inferFullSky

def inferFullComb? : Option Comb :=
  inferFullCombWithMode? .classic

def checkFullCombWithMode? (mode : Bracket.BracketMode) : Option Comb :=
  compileClosedWithMode? mode checkFullSky

def checkFullComb? : Option Comb :=
  checkFullCombWithMode? .classic

def inferFullWithLitTypeIdsCombWithMode? (mode : Bracket.BracketMode) : Option Comb :=
  compileClosedWithMode? mode inferFullSkyWithLitTypeIds

def inferFullWithLitTypeIdsComb? : Option Comb :=
  inferFullWithLitTypeIdsCombWithMode? .classic

def inferIsSomeSortZeroFullWithLitTypeIdsCombWithMode? (mode : Bracket.BracketMode) : Option Comb :=
  compileClosedWithMode? mode inferIsSomeSortZeroFullSkyWithLitTypeIds

def inferIsSomeSortZeroFullWithLitTypeIdsComb? : Option Comb :=
  inferIsSomeSortZeroFullWithLitTypeIdsCombWithMode? .classic

def checkFullWithLitTypeIdsCombWithMode? (mode : Bracket.BracketMode) : Option Comb :=
  compileClosedWithMode? mode checkFullSkyWithLitTypeIds

def checkFullWithLitTypeIdsComb? : Option Comb :=
  checkFullWithLitTypeIdsCombWithMode? .classic

def optExprIsSomeCombWithMode? (mode : Bracket.BracketMode) : Option Comb :=
  compileClosedWithMode? mode optExprIsSomeSky

def optExprIsSomeComb? : Option Comb :=
  optExprIsSomeCombWithMode? .classic

def optExprIsSomeSortCombWithMode? (mode : Bracket.BracketMode) : Option Comb :=
  compileClosedWithMode? mode optExprIsSomeSortSky

def optExprIsSomeSortComb? : Option Comb :=
  optExprIsSomeSortCombWithMode? .classic

def optExprIsSomeSortZeroCombWithMode? (mode : Bracket.BracketMode) : Option Comb :=
  compileClosedWithMode? mode optExprIsSomeSortZeroSky

def optExprIsSomeSortZeroComb? : Option Comb :=
  optExprIsSomeSortZeroCombWithMode? .classic

def exprIsSortZeroCombWithMode? (mode : Bracket.BracketMode) : Option Comb :=
  compileClosedWithMode? mode exprIsSortZeroSky

def exprIsSortZeroComb? : Option Comb :=
  exprIsSortZeroCombWithMode? .classic

def emptyEnvCombWithMode? (mode : Bracket.BracketMode) : Option Comb :=
  compileClosedWithMode? mode EnvironmentSKY.envEmpty

def emptyEnvComb? : Option Comb :=
  emptyEnvCombWithMode? .classic

def emptyRulesCombWithMode? (mode : Bracket.BracketMode) : Option Comb :=
  compileClosedWithMode? mode (WHNFIotaSKY.Enc.iotaRules [])

def emptyRulesComb? : Option Comb :=
  emptyRulesCombWithMode? .classic

structure FullCompiled where
  whnf : Comb
  isDefEq : Comb
  infer : Comb
  check : Comb
  emptyCtx : Comb
  emptyEnv : Comb
  emptyRules : Comb

def compileFullWithMode? (mode : Bracket.BracketMode) : Option FullCompiled := do
  let whnf <- whnfFullCombWithMode? mode
  let isDefEq <- isDefEqFullCombWithMode? mode
  let infer <- inferFullCombWithMode? mode
  let check <- checkFullCombWithMode? mode
  let emptyCtx <- emptyCtxCombWithMode? mode
  let emptyEnv <- emptyEnvCombWithMode? mode
  let emptyRules <- emptyRulesCombWithMode? mode
  pure { whnf, isDefEq, infer, check, emptyCtx, emptyEnv, emptyRules }

def compileFull? : Option FullCompiled :=
  compileFullWithMode? .classic

/-! ## Runners (fuel-bounded, decoding only tags/bools) -/

def encodeNatCombWithMode? (mode : Bracket.BracketMode) (n : Nat) : Option Comb :=
  compileClosedWithMode? mode (Expr.Scott.encodeNat n)

def encodeNatComb? (n : Nat) : Option Comb :=
  encodeNatCombWithMode? .classic n

def compileExprNatUnitWithMode? (mode : Bracket.BracketMode) (e : E) : Option Comb :=
  compileClosedWithMode? mode <|
    Expr.Scott.encode
      Lean4LeanSKY.Enc.nat
      Lean4LeanSKY.Enc.unit
      Lean4LeanSKY.Enc.unit
      Lean4LeanSKY.Enc.unit
      Lean4LeanSKY.Enc.string
      e

def compileExprNatUnit? (e : E) : Option Comb :=
  compileExprNatUnitWithMode? .classic e

def decodeOptExprTagFuel (fuelReduce : Nat) (optExpr : Comb) : Option String :=
  /-
  Scott `Option α` is `λ n s => ...`. When we apply it to `K` and `I`,
  `none` reduces to `K` and `some x` reduces to `x`.
  -/
  let out := SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app optExpr Comb.K) Comb.I)
  if out = Comb.K then
    none
  else
    Lean4LeanSKY.Decode.exprTagFuel fuelReduce out

def decodeOptExprCombFuel (fuelReduce : Nat) (optExpr : Comb) : Option Comb :=
  let out := SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app optExpr Comb.K) Comb.I)
  if out = Comb.K then
    none
  else
    some out

def runWhnfFullTagFuelWith (k : FullCompiled) (fuelWhnf fuelReduce : Nat)
    (envC rulesC : Comb) (e : E) : Option String := do
  let fuelC <- encodeNatComb? fuelWhnf
  let eC <- compileExprNatUnit? e
  let out :=
    SKYExec.reduceFuel fuelReduce <|
      Comb.app (Comb.app (Comb.app (Comb.app k.whnf envC) rulesC) fuelC) eC
  Lean4LeanSKY.Decode.exprTagFuel fuelReduce out

def runWhnfFullCombFuelWith (k : FullCompiled) (fuelWhnf fuelReduce : Nat)
    (envC rulesC : Comb) (e : E) : Option Comb := do
  let fuelC <- encodeNatComb? fuelWhnf
  let eC <- compileExprNatUnit? e
  some <|
    SKYExec.reduceFuel fuelReduce <|
      Comb.app (Comb.app (Comb.app (Comb.app k.whnf envC) rulesC) fuelC) eC

def runIsDefEqFullFuelWith (k : FullCompiled) (fuelDefEq fuelReduce : Nat)
    (envC rulesC : Comb) (e1 e2 : E) : Option Bool := do
  let fuelC <- encodeNatComb? fuelDefEq
  let e1C <- compileExprNatUnit? e1
  let e2C <- compileExprNatUnit? e2
  let out :=
    SKYExec.reduceFuel fuelReduce <|
      Comb.app (Comb.app (Comb.app (Comb.app (Comb.app k.isDefEq envC) rulesC) fuelC) e1C) e2C
  SKYExec.decodeChurchBoolFuel fuelReduce out

def runIsDefEqFullCombFuelWith (k : FullCompiled) (fuelDefEq fuelReduce : Nat)
    (envC rulesC e1C e2C : Comb) : Option Bool := do
  let fuelC <- encodeNatComb? fuelDefEq
  let out :=
    SKYExec.reduceFuel fuelReduce <|
      Comb.app (Comb.app (Comb.app (Comb.app (Comb.app k.isDefEq envC) rulesC) fuelC) e1C) e2C
  SKYExec.decodeChurchBoolFuel fuelReduce out

def runInferFullTagFuelWith (k : FullCompiled) (fuelInfer fuelReduce : Nat)
    (envC rulesC : Comb) (e : E) : Option String := do
  let fuelC <- encodeNatComb? fuelInfer
  let eC <- compileExprNatUnit? e
  let outOpt :=
    SKYExec.reduceFuel fuelReduce <|
      Comb.app (Comb.app (Comb.app (Comb.app (Comb.app k.infer envC) rulesC) fuelC) k.emptyCtx) eC
  decodeOptExprTagFuel fuelReduce outOpt

def runInferFullOptCombFuelWith (k : FullCompiled) (fuelInfer fuelReduce : Nat)
    (envC rulesC : Comb) (e : E) : Option Comb := do
  let fuelC <- encodeNatComb? fuelInfer
  let eC <- compileExprNatUnit? e
  some <|
    SKYExec.reduceFuel fuelReduce <|
      Comb.app (Comb.app (Comb.app (Comb.app (Comb.app k.infer envC) rulesC) fuelC) k.emptyCtx) eC

def runCheckFullFuelWith (k : FullCompiled) (fuel fuelReduce : Nat)
    (envC rulesC : Comb) (e ty : E) : Option Bool := do
  let fuelC <- encodeNatComb? fuel
  let eC <- compileExprNatUnit? e
  let tyC <- compileExprNatUnit? ty
  let out :=
    SKYExec.reduceFuel fuelReduce <|
      Comb.app (Comb.app (Comb.app (Comb.app (Comb.app (Comb.app k.check envC) rulesC) fuelC) k.emptyCtx) eC) tyC
  SKYExec.decodeChurchBoolFuel fuelReduce out

end FullKernelSKY

end LeanKernel
end LoF
end HeytingLean
