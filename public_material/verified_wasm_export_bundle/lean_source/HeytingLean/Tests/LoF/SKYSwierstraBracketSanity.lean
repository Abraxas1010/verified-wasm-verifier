import HeytingLean.LoF.Combinators.BracketAbstraction
import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.Combinators.SwierstraBracket

/-!
Sanity checks for `HeytingLean.LoF.Combinators.SwierstraBracket`.

This file separates two claims:

1. the new intrinsically typed compiler is correctness-first and therefore does
   not promise byte-for-byte agreement with the current classic optimizer, and
2. on a small closed corpus, the new baseline and the current classic compiler
   agree extensionally under a bounded reducer and finite boolean/function
   samples.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Combinators.Bracket
open HeytingLean.LoF.Combinators.SKYExec
open HeytingLean.LoF.Combinators.SwierstraBracket

namespace SKYSwierstraBracketSanity

abbrev L : Type := Lam String

def fuel : Nat := 256

def boolSamples : List Comb :=
  [bTrue, bFalse]

def constTrue : Comb :=
  Comb.app Comb.K bTrue

def constFalse : Comb :=
  Comb.app Comb.K bFalse

def v (s : String) : L := .var s
def app (f a : L) : L := .app f a
def lam (x : String) (body : L) : L := .lam x body

def iL : L := app (app .S .K) .K
def tru : L := .K
def fls : L := app .K iL
def lnot : L := lam "p" (app (app (v "p") fls) tru)

def boolFnSamples : List Comb :=
  [Comb.I, constTrue, constFalse] ++
    match Lam.compileClosed? (Var := String) lnot with
    | some c => [c]
    | none => []

def runBool1 (f x : Comb) : Option Bool :=
  decodeChurchBoolFuel fuel (reduceFuel fuel (Comb.app f x))

def runBool2 (f x y : Comb) : Option Bool :=
  decodeChurchBoolFuel fuel (reduceFuel fuel (Comb.app (Comb.app f x) y))

def runEndo (h g x : Comb) : Option Bool :=
  decodeChurchBoolFuel fuel (reduceFuel fuel (Comb.app (Comb.app h g) x))

def runCompose (h f g x : Comb) : Option Bool :=
  decodeChurchBoolFuel fuel (reduceFuel fuel (Comb.app (Comb.app (Comb.app h f) g) x))

def boundedAgreementId : Bool :=
  boolSamples.all fun x =>
    runBool1 (compileClosed tId) x ==
      runBool1 (Option.getD (compileClosedClassicCurrent? tId) Comb.Y) x

def boundedAgreementConst : Bool :=
  boolSamples.all fun x =>
    boolSamples.all fun y =>
      runBool2 (compileClosed tConst) x y ==
        runBool2 (Option.getD (compileClosedClassicCurrent? tConst) Comb.Y) x y

def boundedAgreementFlipConst : Bool :=
  boolSamples.all fun x =>
    boolSamples.all fun y =>
      runBool2 (compileClosed tFlipConst) x y ==
        runBool2 (Option.getD (compileClosedClassicCurrent? tFlipConst) Comb.Y) x y

def boundedAgreementApply : Bool :=
  boolFnSamples.all fun g =>
    boolSamples.all fun x =>
      runEndo (compileClosed tApply) g x ==
        runEndo (Option.getD (compileClosedClassicCurrent? tApply) Comb.Y) g x

def boundedAgreementCompose : Bool :=
  boolFnSamples.all fun f =>
    boolFnSamples.all fun g =>
      boolSamples.all fun x =>
        runCompose (compileClosed tCompose) f g x ==
          runCompose (Option.getD (compileClosedClassicCurrent? tCompose) Comb.Y) f g x

def boundedAgreementRows : List (String × Bool) :=
  [ ("id", boundedAgreementId)
  , ("const", boundedAgreementConst)
  , ("flipConst", boundedAgreementFlipConst)
  , ("apply", boundedAgreementApply)
  , ("compose", boundedAgreementCompose)
  ]

example : compileClosed tId = Comb.I := by
  native_decide

example : corpusAgreement = false := by
  native_decide

example : boolFnSamples.length = 4 := by
  native_decide

example : boundedAgreementId = true := by
  native_decide

example : boundedAgreementConst = true := by
  native_decide

example : boundedAgreementFlipConst = true := by
  native_decide

example : boundedAgreementApply = true := by
  native_decide

example : boundedAgreementCompose = true := by
  native_decide

example : boundedAgreementRows.all (fun row => row.snd) = true := by
  native_decide

end SKYSwierstraBracketSanity

end LoF
end Tests
end HeytingLean
