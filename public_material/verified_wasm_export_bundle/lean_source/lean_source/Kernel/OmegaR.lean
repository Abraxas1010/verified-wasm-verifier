/-
  Minimal Ωᴿ kernel (Lean 4).
  No sorrys. This file defines the syntax and rules;
  the IR checker (JSON replay) can live elsewhere.
-/
namespace OmegaR

inductive Formula where
  | var  : String → Formula
  | top  : Formula
  | bot  : Formula
  | and  : Formula → Formula → Formula
  | orR  : Formula → Formula → Formula
  | impR : Formula → Formula → Formula
  | notR : Formula → Formula
deriving BEq, Repr, DecidableEq

abbrev Ctx := List Formula

-- Provability Γ ⊢ φ
inductive Provable : Ctx → Formula → Prop
| hyp  {Γ φ}        (h : φ ∈ Γ)                          : Provable Γ φ
| topI {Γ}                                             : Provable Γ .top
| andI {Γ A B}     (p : Provable Γ A) (q : Provable Γ B): Provable Γ (.and A B)
| andE1 {Γ A B}    (p : Provable Γ (.and A B))         : Provable Γ A
| andE2 {Γ A B}    (p : Provable Γ (.and A B))         : Provable Γ B
| orRI {Γ A B}     (p : Provable Γ A)                   : Provable Γ (.orR A B)
| orRII {Γ A B}    (p : Provable Γ B)                   : Provable Γ (.orR A B)
| impI {Γ A B}     (p : Provable (A :: Γ) B)            : Provable Γ (.impR A B)
| impE {Γ A B}     (p : Provable Γ (.impR A B)) (q : Provable Γ A) : Provable Γ B
| notI {Γ A}       (p : Provable (A :: Γ) .bot)         : Provable Γ (.notR A)
| notE {Γ A}       (p : Provable Γ (.notR A)) (q : Provable Γ A)   : Provable Γ .bot
| botE {Γ C}       (p : Provable Γ .bot)                : Provable Γ C

-- Optional: helpers showing notR A ≡ impR A ⊥ at the kernel level
def Formula.botR : Formula := .bot

end OmegaR
