import HeytingLean.LoF.ICC.GPUVerifierContract

namespace HeytingLean.CLI.VerifierFixture

open HeytingLean.LoF.ICC
open HeytingLean.LoF.LoFPrimary

def idNat (n : Nat) : Nat :=
  let x := n
  x

def applyId : Nat :=
  idNat 7

def constNat : Nat :=
  let x := 3
  let _y := 4
  x

def zetaChain : Nat :=
  let x := 2
  let y := idNat x
  let z := y
  z

def applyViaDelta : Nat :=
  let f := idNat
  f (idNat 9)

def higherOrderApply : Nat :=
  (fun f => f (idNat 5)) idNat

def recursiveLift : Nat → Nat
  | 0 => 0
  | Nat.succ n =>
      let prev := recursiveLift n
      idNat (Nat.succ prev)

def recursiveLiftThree : Nat :=
  recursiveLift 3

def applyId11 : Nat :=
  idNat 11

def recursiveLiftFour : Nat :=
  recursiveLift 4

def recursiveLiftFive : Nat :=
  recursiveLift 5

private def fixtureModuleName := "HeytingLean.CLI.VerifierFixture"

private def voidExpr : Expr 0 := .void

private def markedVoid : Expr 0 := .mark .void

private def doubleMarkedVoid : Expr 0 := .mark markedVoid

private def juxtVoidMarked : Expr 0 := .juxt voidExpr markedVoid

private def juxtMarkedDouble : Expr 0 := .juxt markedVoid doubleMarkedVoid

def iccVerifierCorpusSeeds : List VerifierCorpusSeed :=
  [ { sourceId := "applyId_calling_void"
      law := .calling
      source := .juxt voidExpr voidExpr
      target := voidExpr
      provenance := "paired with VerifierFixture.applyId for SKY baseline"
      sourceFamily := "fixture_catalog"
      sourceModuleName := fixtureModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierFixture.applyId"
      skyModuleName := fixtureModuleName
      skyDeclName := "HeytingLean.CLI.VerifierFixture.applyId"
      tags := ["generated", "calling", "fixture"] }
  , { sourceId := "constNat_calling_marked_void"
      law := .calling
      source := .juxt markedVoid markedVoid
      target := markedVoid
      provenance := "paired with VerifierFixture.constNat for SKY baseline"
      sourceFamily := "fixture_catalog"
      sourceModuleName := fixtureModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierFixture.constNat"
      skyModuleName := fixtureModuleName
      skyDeclName := "HeytingLean.CLI.VerifierFixture.constNat"
      tags := ["generated", "calling", "fixture"] }
  , { sourceId := "zetaChain_calling_double_marked_void"
      law := .calling
      source := .juxt doubleMarkedVoid doubleMarkedVoid
      target := doubleMarkedVoid
      provenance := "paired with VerifierFixture.zetaChain for SKY baseline"
      sourceFamily := "fixture_catalog"
      sourceModuleName := fixtureModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierFixture.zetaChain"
      skyModuleName := fixtureModuleName
      skyDeclName := "HeytingLean.CLI.VerifierFixture.zetaChain"
      tags := ["generated", "calling", "fixture"] }
  , { sourceId := "applyViaDelta_crossing_void"
      law := .crossing
      source := .mark (.mark voidExpr)
      target := voidExpr
      provenance := "paired with VerifierFixture.applyViaDelta for SKY baseline"
      sourceFamily := "fixture_catalog"
      sourceModuleName := fixtureModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierFixture.applyViaDelta"
      skyModuleName := fixtureModuleName
      skyDeclName := "HeytingLean.CLI.VerifierFixture.applyViaDelta"
      tags := ["generated", "crossing", "fixture"] }
  , { sourceId := "higherOrderApply_crossing_marked_void"
      law := .crossing
      source := .mark (.mark markedVoid)
      target := markedVoid
      provenance := "paired with VerifierFixture.higherOrderApply for SKY baseline"
      sourceFamily := "fixture_catalog"
      sourceModuleName := fixtureModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierFixture.higherOrderApply"
      skyModuleName := fixtureModuleName
      skyDeclName := "HeytingLean.CLI.VerifierFixture.higherOrderApply"
      tags := ["generated", "crossing", "fixture"] }
  , { sourceId := "recursiveLiftThree_crossing_double_marked_void"
      law := .crossing
      source := .mark (.mark doubleMarkedVoid)
      target := doubleMarkedVoid
      provenance := "paired with VerifierFixture.recursiveLiftThree for SKY baseline"
      sourceFamily := "fixture_catalog"
      sourceModuleName := fixtureModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierFixture.recursiveLiftThree"
      skyModuleName := fixtureModuleName
      skyDeclName := "HeytingLean.CLI.VerifierFixture.recursiveLiftThree"
      tags := ["generated", "crossing", "fixture"] }
  ]

end HeytingLean.CLI.VerifierFixture
