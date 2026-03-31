import HeytingLean.LeanCP.VCG.SymExec
import HeytingLean.LeanCP.Examples.SwapVerified
import HeytingLean.LeanCP.Examples.CountdownVerified
import HeytingLean.LeanCP.Examples.CallerVerified

namespace HeytingLean.LeanCP

open HeytingLean.LeanCP.Examples

def previewsOrEmpty (res : Except VCGenError (List VCPreview)) : List VCPreview :=
  match res with
  | .ok vcs => vcs
  | .error _ => []

def swapVCInput (addrA addrB : Nat) (va vb : CVal) : VerifyInput where
  name := "swap_phase4"
  mode := .swp
  body := swapBody
  pre := (swapSSpec addrA addrB va vb).pre
  post := (swapSSpec addrA addrB va vb).post

def countdownVCInput : VerifyInput where
  name := "countdown_phase4"
  mode := .swp
  body := countdownProgram
  pre := countdownPre
  post := countdownPost
  loops := [{ path := [], inv := countdownInv, fuelHint := 2 }]

def callerVCInput (addr : Nat) (n : Int) : VerifyInput where
  name := "caller_phase4"
  mode := .swpFull
  body := callerBody
  pre := (callerSpec addr n).pre
  post := (callerSpec addr n).post
  funEnv := callerFunEnv addr n

example (addrA addrB : Nat) (va vb : CVal) :
    countKind .main (previewsOrEmpty (generateVCPreviews (swapVCInput addrA addrB va vb))) = 1 := by
  rfl

example (addrA addrB : Nat) (va vb : CVal) :
    countKind .seqBoundary (previewsOrEmpty (generateVCPreviews (swapVCInput addrA addrB va vb))) = 2 := by
  rfl

example :
    countKind .loopInit (previewsOrEmpty (generateVCPreviews countdownVCInput)) = 1 := by
  rfl

example :
    countKind .loopStep (previewsOrEmpty (generateVCPreviews countdownVCInput)) = 1 := by
  rfl

example :
    countKind .loopExit (previewsOrEmpty (generateVCPreviews countdownVCInput)) = 1 := by
  rfl

example (addr : Nat) (n : Int) :
    countKind .seqBoundary (previewsOrEmpty (generateVCPreviews (callerVCInput addr n))) = 1 := by
  rfl

example (addr : Nat) (n : Int) :
    countKind .callBoundary (previewsOrEmpty (generateVCPreviews (callerVCInput addr n))) = 1 := by
  rfl

example :
    generateVCPreviews
      { name := "countdown_missing"
        mode := .swp
        body := countdownProgram
        pre := countdownPre
        post := countdownPost
        funEnv := fun _ => none
        loops := [] } =
      Except.error (.missingLoopHint []) := by
  rfl

end HeytingLean.LeanCP
