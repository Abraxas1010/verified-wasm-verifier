import HeytingLean.CAB.Certified
import HeytingLean.Certified.Basic
import HeytingLean.Erasure.Marker
import HeytingLean.Lens.Compile
import HeytingLean.Nucleus.Compile
import HeytingLean.Nucleus.Certified

namespace HeytingLean
namespace Tests
namespace MLTT

open HeytingLean.Certified
open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment
open HeytingLean.MiniC

/-! ## Certified (core) -/

def testCertifiedNat : Certified Nat (fun n => n = 42) :=
  ⟨42, rfl⟩

example : testCertifiedNat.extract = 42 := rfl

def testCertifiedMap : Certified Nat (fun n => n = 43) :=
  testCertifiedNat.map (fun n => n + 1) (by
    intro a ha
    simp [ha])

example : testCertifiedMap.val = 43 := rfl

def testCertifiedBind : Certified Nat (fun n => n = 44) :=
  testCertifiedNat.bind (fun a ha => ⟨a + 2, by simp [ha]⟩)

example : testCertifiedBind.val = 44 := rfl

/-! ## Erasure markers -/

def g1 : HeytingLean.Erasure.Ghost True := ⟨trivial⟩
def g2 : HeytingLean.Erasure.Ghost True := ⟨True.intro⟩

example : g1 = g2 :=
  HeytingLean.Erasure.Ghost.irrelevant g1 g2

/-! ## Nucleus fixed points -/

def natIdNucleus : HeytingLean.Nucleus.CertifiedNucleus Nat := (⊥ : _root_.Nucleus Nat)

def natIdClosed (n : Nat) : HeytingLean.Nucleus.CertifiedFixedPoint natIdNucleus :=
  HeytingLean.Nucleus.close natIdNucleus n

example (n : Nat) : natIdNucleus (natIdClosed n).val = (natIdClosed n).val :=
  (natIdClosed n).ok

/-! ## CAB hash verification -/

def proofBytes : ByteArray :=
  "mltt-proof".toUTF8

def cabMeta : HeytingLean.CAB.CABMetadata :=
  { fragment := .Nat1
    dimension := .D1
    lensCompatibility := []
    timestamp := 0 }

def cabNat42 : HeytingLean.CAB Nat (fun n => n = 42) :=
  { artifact := 42
    spec := rfl
    proofCommitment :=
      { hash := HeytingLean.Util.SHA256.sha256Bytes proofBytes
        algorithm := "SHA256" }
    metadata := cabMeta }

example : HeytingLean.CAB.verify cabNat42 proofBytes = true := by
  simp [HeytingLean.CAB.verify, cabNat42, proofBytes]

/-! ## Nat¹ compilation (nucleus + lens) -/

def termNatId : Term [] (Ty.arrow Ty.nat Ty.nat) :=
  Term.lam (Term.var Var.vz)

theorem termNatId_isNatFun : IsNatFun termNatId := by
  refine ⟨Term.var Var.vz, rfl, ?_⟩
  exact IsNatBody.expr IsNatExpr.var

theorem termNatId_sem (n : Nat) :
    LambdaIR.evalClosed (Term.app termNatId (Term.constNat n)) = n := by
  simp [termNatId, LambdaIR.evalClosed, LambdaIR.eval]

def natIdNucleusIR :
    HeytingLean.Nucleus.Nat1NucleusIR natIdNucleus :=
  { funName := "id_nucleus"
    paramName := "x"
    term := termNatId
    isNatFun := termNatId_isNatFun
    sem := by
      intro n
      simpa [natIdNucleus] using termNatId_sem n }

def natIdNucleusMiniC :=
  natIdNucleusIR.compileMiniC

example : runNatFunFrag natIdNucleusMiniC.val "x" 7 = some 7 := by
  have h := (natIdNucleusMiniC.ok.2 7)
  simpa [natIdNucleus] using h

def natIdNucleusC :=
  natIdNucleusIR.compileC

example : HeytingLean.C.runCFunFrag natIdNucleusC.val [(7 : Int)] = some (Int.ofNat 7) := by
  have h := (natIdNucleusC.ok.2 7)
  simpa [natIdNucleus] using h

def natIdLens : HeytingLean.Lens.CertifiedLens Nat Nat :=
  { forward := fun n => n
    backward := fun n => n
    rtLevel := .RT1
    rt1_proof := by
      intro _ a
      rfl
    rt2_bound := by
      intro hRT
      cases hRT }

def natIdLensIR : HeytingLean.Lens.Nat1LensIR natIdLens :=
  { forwardName := "id_forward"
    forwardParam := "x"
    forwardTerm := termNatId
    forwardIsNatFun := termNatId_isNatFun
    forwardSem := by
      intro n
      simpa [natIdLens] using termNatId_sem n
    backwardName := "id_backward"
    backwardParam := "x"
    backwardTerm := termNatId
    backwardIsNatFun := termNatId_isNatFun
    backwardSem := by
      intro n
      simpa [natIdLens] using termNatId_sem n }

def natIdLensMiniC :=
  natIdLensIR.compileMiniC

example : runNatFunFrag natIdLensMiniC.val.1 "x" 9 = some 9 := by
  have h := (HeytingLean.Lens.Nat1LensMiniCSpec.forward_sem (h := natIdLensMiniC.ok) 9)
  simpa [natIdLens] using h

example : runNatFunFrag natIdLensMiniC.val.2 "x" (natIdLens.forward 9) = some 9 := by
  have hRT : natIdLens.rtLevel = HeytingLean.Lens.RTLevel.RT1 := rfl
  simpa using
    (HeytingLean.Lens.Nat1LensMiniCSpec.rt1_roundtrip (h := natIdLensMiniC.ok) hRT 9)

/-! ## MiniC → C runner bridge (fragment) -/

example :
    HeytingLean.C.runCFunFrag (HeytingLean.MiniC.ToC.compileFun natIdNucleusMiniC.val)
        [(7 : Int)] =
      some (Int.ofNat 7) := by
  have hMini : runNatFunFrag natIdNucleusMiniC.val "x" 7 = some 7 := by
    simpa [natIdNucleus] using (natIdNucleusMiniC.ok.2 7)
  simpa using
    (HeytingLean.MiniC.ToC.runNatFunFrag_correct_toC
      (fn := natIdNucleusMiniC.val) (paramName := "x") (n := 7) (out := 7) hMini)

end MLTT
end Tests
end HeytingLean
