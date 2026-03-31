import HeytingLean.LoF.ICC.GPUVerifierTranslate

namespace HeytingLean
namespace LoF
namespace ICC

open HeytingLean.LoF.LoFPrimary

/--
Compatibility wrapper retaining the original seed witness surface on top of the
general source-witness translator.
-/

def callingSourceWitness (expr : LoFPrimary.Expr 0) : SourceWitness :=
  { sourceId := s!"calling_seed::{repr expr}"
    law := .calling
    source := .juxt expr expr
    target := expr
    provenance := "seed compatibility witness"
    sourceFamily := "compat_seed"
    tags := ["seed", "calling"] }

def crossingSourceWitness (expr : LoFPrimary.Expr 0) : SourceWitness :=
  { sourceId := s!"crossing_seed::{repr expr}"
    law := .crossing
    source := .mark (.mark expr)
    target := expr
    provenance := "seed compatibility witness"
    sourceFamily := "compat_seed"
    tags := ["seed", "crossing"] }

def callingWitness (expr : LoFPrimary.Expr 0) : TinyLawWitness :=
  buildWitness (callingSourceWitness expr) expr

def crossingWitness (expr : LoFPrimary.Expr 0) : TinyLawWitness :=
  buildWitness (crossingSourceWitness expr) expr

theorem callingWitness_accepts (expr : LoFPrimary.Expr 0) :
    accepts (callingWitness expr) := by
  exact buildWitness_accepts_of_target_eq (callingSourceWitness expr) expr rfl

theorem crossingWitness_accepts (expr : LoFPrimary.Expr 0) :
    accepts (crossingWitness expr) := by
  exact buildWitness_accepts_of_target_eq (crossingSourceWitness expr) expr rfl

def callingVoid : TinyLawWitness := callingWitness .void

def callingMarkedVoid : TinyLawWitness := callingWitness (.mark .void)

def crossingVoid : TinyLawWitness := crossingWitness .void

def crossingJuxtVoidMarkedVoid : TinyLawWitness := crossingWitness (.juxt .void (.mark .void))

def witnessFixtures : List (String × TinyLawWitness) :=
  [ ("calling_void", callingVoid)
  , ("calling_marked_void", callingMarkedVoid)
  , ("crossing_void", crossingVoid)
  , ("crossing_juxt_void_marked_void", crossingJuxtVoidMarkedVoid)
  ]

end ICC
end LoF
end HeytingLean
