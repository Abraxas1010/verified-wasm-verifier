import HeytingLean.CLI.VerifierFixture

namespace HeytingLean.CLI.VerifierProofCorpus

open HeytingLean.CLI.VerifierFixture
open HeytingLean.LoF.ICC
open HeytingLean.LoF.LoFPrimary

def applyId_eq_7 : applyId = 7 := by
  rfl

def constNat_eq_3 : constNat = 3 := by
  rfl

def zetaChain_eq_2 : zetaChain = 2 := by
  rfl

def applyId11_eq_11 : applyId11 = 11 := by
  rfl

theorem recursiveLift_eq_self (n : Nat) : recursiveLift n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [recursiveLift, idNat, ih]

def recursiveLiftThree_eq_3 : recursiveLiftThree = 3 := by
  simpa [recursiveLiftThree] using recursiveLift_eq_self 3

def recursiveLiftFour_eq_4 : recursiveLiftFour = 4 := by
  simpa [recursiveLiftFour] using recursiveLift_eq_self 4

def recursiveLiftFive_eq_5 : recursiveLiftFive = 5 := by
  simpa [recursiveLiftFive] using recursiveLift_eq_self 5

def applyViaDelta_eq_9 : applyViaDelta = 9 := by
  rfl

def higherOrderApply_eq_5 : higherOrderApply = 5 := by
  rfl

def recursiveLift_succ_four : recursiveLiftFive = Nat.succ recursiveLiftFour := by
  change Nat.succ 4 = Nat.succ 4
  rfl

def recursiveLift_succ_three : recursiveLiftFour = Nat.succ recursiveLiftThree := by
  change Nat.succ 3 = Nat.succ 3
  rfl

def idNat_recursiveLiftFour : idNat recursiveLiftFour = 4 := by
  simp [idNat, recursiveLiftFour, recursiveLift_eq_self]

def recursiveLiftSix_eq_6 : recursiveLift 6 = 6 := by
  simpa using recursiveLift_eq_self 6

def recursiveLiftSeven_eq_7 : recursiveLift 7 = 7 := by
  simpa using recursiveLift_eq_self 7

def recursiveLiftEight_eq_8 : recursiveLift 8 = 8 := by
  simpa using recursiveLift_eq_self 8

def recursiveLiftNine_eq_9 : recursiveLift 9 = 9 := by
  simpa using recursiveLift_eq_self 9

def recursiveLiftTen_eq_10 : recursiveLift 10 = 10 := by
  simpa using recursiveLift_eq_self 10

def recursiveLiftEleven_eq_11 : recursiveLift 11 = 11 := by
  simpa using recursiveLift_eq_self 11

def recursiveLiftTwelve_eq_12 : recursiveLift 12 = 12 := by
  simpa using recursiveLift_eq_self 12

def idNat_recursiveLiftTen : idNat (recursiveLift 10) = 10 := by
  simp [idNat, recursiveLift_eq_self]

private def proofModuleName := "HeytingLean.CLI.VerifierProofCorpus"

private def voidExpr : Expr 0 := .void

private def markedVoid : Expr 0 := .mark .void

private def doubleMarkedVoid : Expr 0 := .mark markedVoid

private def tripleMarkedVoid : Expr 0 := .mark doubleMarkedVoid

private def juxtVoidMarked : Expr 0 := .juxt voidExpr markedVoid

private def juxtMarkedDouble : Expr 0 := .juxt markedVoid doubleMarkedVoid

private def repeatMark : Nat → Expr 0 → Expr 0
  | 0, expr => expr
  | n + 1, expr => .mark (repeatMark n expr)

private def balancedJuxt : Nat → Expr 0
  | 0 => voidExpr
  | n + 1 =>
      let child := balancedJuxt n
      .juxt child child

private def stressJuxtFour : Expr 0 := balancedJuxt 4

private def stressJuxtFive : Expr 0 := balancedJuxt 5

private def stressJuxtSix : Expr 0 := balancedJuxt 6

private def stressMarkedVoidTwelve : Expr 0 := repeatMark 12 voidExpr

private def stressMarkedVoidEighteen : Expr 0 := repeatMark 18 voidExpr

private def stressMarkedJuxt : Expr 0 := repeatMark 8 stressJuxtFive

def iccVerifierCorpusSeeds : List VerifierCorpusSeed :=
  [ { sourceId := "applyId_eq_7_calling_triple_marked_void"
      law := .calling
      source := .juxt tripleMarkedVoid tripleMarkedVoid
      target := tripleMarkedVoid
      provenance := "paired with VerifierProofCorpus.applyId_eq_7 proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.applyId_eq_7"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.applyId_eq_7"
      tags := ["generated", "calling", "theorem_corpus"] }
  , { sourceId := "constNat_eq_3_calling_juxt_void_marked"
      law := .calling
      source := .juxt juxtVoidMarked juxtVoidMarked
      target := juxtVoidMarked
      provenance := "paired with VerifierProofCorpus.constNat_eq_3 proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.constNat_eq_3"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.constNat_eq_3"
      tags := ["generated", "calling", "theorem_corpus"] }
  , { sourceId := "zetaChain_eq_2_calling_juxt_marked_double"
      law := .calling
      source := .juxt juxtMarkedDouble juxtMarkedDouble
      target := juxtMarkedDouble
      provenance := "paired with VerifierProofCorpus.zetaChain_eq_2 proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.zetaChain_eq_2"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.zetaChain_eq_2"
      tags := ["generated", "calling", "theorem_corpus"] }
  , { sourceId := "applyId11_eq_11_calling_void"
      law := .calling
      source := .juxt voidExpr voidExpr
      target := voidExpr
      provenance := "paired with VerifierProofCorpus.applyId11_eq_11 proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.applyId11_eq_11"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.applyId11_eq_11"
      tags := ["generated", "calling", "theorem_corpus"] }
  , { sourceId := "recursiveLiftThree_eq_3_calling_marked_void"
      law := .calling
      source := .juxt markedVoid markedVoid
      target := markedVoid
      provenance := "paired with VerifierProofCorpus.recursiveLiftThree_eq_3 proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftThree_eq_3"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftThree_eq_3"
      tags := ["generated", "calling", "theorem_corpus"] }
  , { sourceId := "recursiveLiftFour_eq_4_calling_double_marked_void"
      law := .calling
      source := .juxt doubleMarkedVoid doubleMarkedVoid
      target := doubleMarkedVoid
      provenance := "paired with VerifierProofCorpus.recursiveLiftFour_eq_4 proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftFour_eq_4"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftFour_eq_4"
      tags := ["generated", "calling", "theorem_corpus"] }
  , { sourceId := "recursiveLiftFive_eq_5_crossing_triple_marked_void"
      law := .crossing
      source := .mark (.mark tripleMarkedVoid)
      target := tripleMarkedVoid
      provenance := "paired with VerifierProofCorpus.recursiveLiftFive_eq_5 proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftFive_eq_5"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftFive_eq_5"
      tags := ["generated", "crossing", "theorem_corpus"] }
  , { sourceId := "applyViaDelta_eq_9_crossing_juxt_void_marked"
      law := .crossing
      source := .mark (.mark juxtVoidMarked)
      target := juxtVoidMarked
      provenance := "paired with VerifierProofCorpus.applyViaDelta_eq_9 proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.applyViaDelta_eq_9"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.applyViaDelta_eq_9"
      tags := ["generated", "crossing", "theorem_corpus"] }
  , { sourceId := "higherOrderApply_eq_5_crossing_juxt_marked_double"
      law := .crossing
      source := .mark (.mark juxtMarkedDouble)
      target := juxtMarkedDouble
      provenance := "paired with VerifierProofCorpus.higherOrderApply_eq_5 proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.higherOrderApply_eq_5"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.higherOrderApply_eq_5"
      tags := ["generated", "crossing", "theorem_corpus"] }
  , { sourceId := "recursiveLift_succ_four_crossing_void"
      law := .crossing
      source := .mark (.mark voidExpr)
      target := voidExpr
      provenance := "paired with VerifierProofCorpus.recursiveLift_succ_four proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLift_succ_four"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLift_succ_four"
      tags := ["generated", "crossing", "theorem_corpus"] }
  , { sourceId := "recursiveLift_succ_three_crossing_marked_void"
      law := .crossing
      source := .mark (.mark markedVoid)
      target := markedVoid
      provenance := "paired with VerifierProofCorpus.recursiveLift_succ_three proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLift_succ_three"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLift_succ_three"
      tags := ["generated", "crossing", "theorem_corpus"] }
  , { sourceId := "idNat_recursiveLiftFour_crossing_double_marked_void"
      law := .crossing
      source := .mark (.mark doubleMarkedVoid)
      target := doubleMarkedVoid
      provenance := "paired with VerifierProofCorpus.idNat_recursiveLiftFour proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.idNat_recursiveLiftFour"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.idNat_recursiveLiftFour"
      tags := ["generated", "crossing", "theorem_corpus"] }
  , { sourceId := "recursiveLiftSix_eq_6_calling_stress_juxt_four"
      law := .calling
      source := .juxt stressJuxtFour stressJuxtFour
      target := stressJuxtFour
      provenance := "paired with VerifierProofCorpus.recursiveLiftSix_eq_6 proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftSix_eq_6"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftSix_eq_6"
      tags := ["generated", "calling", "theorem_corpus", "stress", "large_obligation"] }
  , { sourceId := "recursiveLiftSeven_eq_7_calling_stress_juxt_five"
      law := .calling
      source := .juxt stressJuxtFive stressJuxtFive
      target := stressJuxtFive
      provenance := "paired with VerifierProofCorpus.recursiveLiftSeven_eq_7 proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftSeven_eq_7"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftSeven_eq_7"
      tags := ["generated", "calling", "theorem_corpus", "stress", "large_obligation"] }
  , { sourceId := "recursiveLiftEight_eq_8_calling_stress_juxt_six"
      law := .calling
      source := .juxt stressJuxtSix stressJuxtSix
      target := stressJuxtSix
      provenance := "paired with VerifierProofCorpus.recursiveLiftEight_eq_8 proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftEight_eq_8"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftEight_eq_8"
      tags := ["generated", "calling", "theorem_corpus", "stress", "large_obligation"] }
  , { sourceId := "recursiveLiftNine_eq_9_calling_stress_marked_juxt"
      law := .calling
      source := .juxt stressMarkedJuxt stressMarkedJuxt
      target := stressMarkedJuxt
      provenance := "paired with VerifierProofCorpus.recursiveLiftNine_eq_9 proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftNine_eq_9"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftNine_eq_9"
      tags := ["generated", "calling", "theorem_corpus", "stress", "large_obligation"] }
  , { sourceId := "recursiveLiftTen_eq_10_crossing_stress_juxt_six"
      law := .crossing
      source := .mark (.mark stressJuxtSix)
      target := stressJuxtSix
      provenance := "paired with VerifierProofCorpus.recursiveLiftTen_eq_10 proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftTen_eq_10"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftTen_eq_10"
      tags := ["generated", "crossing", "theorem_corpus", "stress", "large_obligation"] }
  , { sourceId := "recursiveLiftEleven_eq_11_crossing_stress_mark_twelve"
      law := .crossing
      source := .mark (.mark stressMarkedVoidTwelve)
      target := stressMarkedVoidTwelve
      provenance := "paired with VerifierProofCorpus.recursiveLiftEleven_eq_11 proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftEleven_eq_11"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftEleven_eq_11"
      tags := ["generated", "crossing", "theorem_corpus", "stress", "large_obligation"] }
  , { sourceId := "recursiveLiftTwelve_eq_12_crossing_stress_mark_eighteen"
      law := .crossing
      source := .mark (.mark stressMarkedVoidEighteen)
      target := stressMarkedVoidEighteen
      provenance := "paired with VerifierProofCorpus.recursiveLiftTwelve_eq_12 proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftTwelve_eq_12"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.recursiveLiftTwelve_eq_12"
      tags := ["generated", "crossing", "theorem_corpus", "stress", "large_obligation"] }
  , { sourceId := "idNat_recursiveLiftTen_crossing_stress_marked_juxt"
      law := .crossing
      source := .mark (.mark stressMarkedJuxt)
      target := stressMarkedJuxt
      provenance := "paired with VerifierProofCorpus.idNat_recursiveLiftTen proof object"
      sourceFamily := "theorem_catalog"
      sourceModuleName := proofModuleName
      sourceDeclName := "HeytingLean.CLI.VerifierProofCorpus.idNat_recursiveLiftTen"
      skyModuleName := proofModuleName
      skyDeclName := "HeytingLean.CLI.VerifierProofCorpus.idNat_recursiveLiftTen"
      tags := ["generated", "crossing", "theorem_corpus", "stress", "large_obligation"] }
  ]

end HeytingLean.CLI.VerifierProofCorpus
