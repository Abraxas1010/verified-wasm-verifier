import HeytingLean.LoF.Combinators.BracketAbstraction
import HeytingLean.LoF.Combinators.STLC

/-!
# SwierstraBracket

An intrinsically typed classic bracket-abstraction baseline.

This module is correctness-first: variables, lambda terms, and SK terms are all
indexed by their typing context and result type, and abstraction is justified by
denotational theorems instead of post-hoc witness chasing.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace SwierstraBracket

open Bracket
open STLC

abbrev Ty := STLC.Ty
abbrev Ctx := List Ty

inductive Var : Ctx → Ty → Type where
  | vz : Var (τ :: Γ) τ
  | vs : Var Γ τ → Var (σ :: Γ) τ
deriving Repr, DecidableEq

inductive Tm : Ctx → Ty → Type where
  | var : Var Γ τ → Tm Γ τ
  | app : Tm Γ (Ty.arrow α β) → Tm Γ α → Tm Γ β
  | lam : Tm (α :: Γ) β → Tm Γ (Ty.arrow α β)
deriving Repr, DecidableEq

inductive SK : Ctx → Ty → Type where
  | var : Var Γ τ → SK Γ τ
  | app : SK Γ (Ty.arrow α β) → SK Γ α → SK Γ β
  | k : SK Γ (Ty.arrow α (Ty.arrow β α))
  | s :
      SK Γ
        (Ty.arrow
          (Ty.arrow α (Ty.arrow β γ))
          (Ty.arrow (Ty.arrow α β) (Ty.arrow α γ)))
deriving Repr, DecidableEq

namespace Ty

def denote : Ty → Type
  | .bool => Bool
  | .arrow α β => denote α → denote β

end Ty

abbrev Env : Ctx → Type
  | [] => PUnit
  | τ :: Γ => Ty.denote τ × Env Γ

namespace Var

def lookup : Var Γ τ → Env Γ → Ty.denote τ
  | .vz, (x, _) => x
  | .vs v, (_, ρ) => lookup v ρ

def toNat : Var Γ τ → Nat
  | .vz => 0
  | .vs v => Nat.succ (toNat v)

private def toBinderNameAux : Var Γ τ → Nat → Nat
  | .vz, n + 1 => n
  | .vs v, n + 1 => toBinderNameAux v n
  | .vz, 0 => 0
  | .vs v, 0 => Nat.succ (toNat v)

def toBinderName (v : Var Γ τ) (depth : Nat) : Nat :=
  toBinderNameAux v depth

end Var

namespace SK

def app2 (f : SK Γ (Ty.arrow α (Ty.arrow β γ))) (a : SK Γ α) (b : SK Γ β) : SK Γ γ :=
  .app (.app f a) b

def i : SK Γ (Ty.arrow α α) :=
  .app
    (.app
      (SK.s (α := α) (β := Ty.arrow α α) (γ := α))
      (SK.k (α := α) (β := Ty.arrow α α)))
    (SK.k (α := α) (β := α))

def eval : SK Γ τ → Env Γ → Ty.denote τ
  | .var v, ρ => Var.lookup v ρ
  | .app f a, ρ => eval f ρ (eval a ρ)
  | .k, _ => fun x _ => x
  | .s, _ => fun f g x => f x (g x)

def dropTop? : SK (σ :: Γ) τ → Option (SK Γ τ)
  | .var .vz => none
  | .var (.vs v) => some (.var v)
  | .app f a => .app <$> dropTop? f <*> dropTop? a
  | .k => some .k
  | .s => some .s

theorem dropTop_sound
    {t : SK (σ :: Γ) τ} {t' : SK Γ τ} (h : dropTop? t = some t')
    (x : Ty.denote σ) (ρ : Env Γ) :
    eval t (x, ρ) = eval t' ρ := by
  induction t with
  | var v =>
      cases v with
      | vz =>
          simp [dropTop?] at h
      | vs v =>
          cases h
          rfl
  | app f a ihf iha =>
      simp [dropTop?] at h
      cases hf : dropTop? f <;> cases ha : dropTop? a <;> simp [hf, ha] at h
      case none.none =>
        cases h
      case some.none =>
        cases h
      case none.some =>
        cases h
      case some.some f' a' =>
        cases h
        simp [eval, ihf hf, iha ha]
  | k =>
      cases h
      rfl
  | s =>
      cases h
      rfl

def etaTop? : SK (σ :: Γ) τ → Option (SK Γ (Ty.arrow σ τ))
  | .app f (.var .vz) =>
      match dropTop? f with
      | some f' => some f'
      | none => none
  | _ => none

theorem etaTop_sound
    {t : SK (σ :: Γ) τ} {t' : SK Γ (Ty.arrow σ τ)} (h : etaTop? t = some t')
    (x : Ty.denote σ) (ρ : Env Γ) :
    eval t' ρ x = eval t (x, ρ) := by
  cases t with
  | var v =>
      cases v <;> simp [etaTop?] at h
  | app f a =>
      cases a with
      | var v =>
          cases v with
          | vz =>
              simp [etaTop?] at h
              cases hdrop : dropTop? f <;> simp [hdrop] at h
              case some f' =>
                cases h
                simpa [eval] using congrArg (fun g => g x) (dropTop_sound hdrop x ρ).symm
          | vs v =>
              simp [etaTop?] at h
      | app f' a' =>
          simp [etaTop?] at h
      | k =>
          simp [etaTop?] at h
      | s =>
          simp [etaTop?] at h
  | k =>
      simp [etaTop?] at h
  | s =>
      simp [etaTop?] at h

def abs : SK (σ :: Γ) τ → SK Γ (Ty.arrow σ τ)
  | .var .vz => i
  | .var (.vs v) => .app .k (.var v)
  | .k => .app .k .k
  | .s => .app .k .s
  | .app f a =>
      match dropTop? (.app f a) with
      | some dropped => .app .k dropped
      | none => app2 .s (abs f) (abs a)

theorem abs_correct (t : SK (σ :: Γ) τ) (ρ : Env Γ) (x : Ty.denote σ) :
    eval (abs t) ρ x = eval t (x, ρ) := by
  induction t with
  | var v =>
      cases v with
      | vz =>
          simp [abs, i, eval, Var.lookup]
      | vs v =>
          rfl
  | app f a ihf iha =>
      simp [abs]
      cases h : dropTop? (SK.app f a) with
      | none =>
          simp [app2, eval, ihf, iha]
      | some dropped =>
          simpa [eval] using (dropTop_sound h x ρ).symm
  | k =>
      rfl
  | s =>
      rfl

def absEta (t : SK (σ :: Γ) τ) : SK Γ (Ty.arrow σ τ) :=
  match etaTop? t with
  | some dropped => dropped
  | none => abs t

theorem absEta_correct (t : SK (σ :: Γ) τ) (ρ : Env Γ) (x : Ty.denote σ) :
    eval (absEta t) ρ x = eval t (x, ρ) := by
  simp [absEta]
  cases h : etaTop? t with
  | none =>
      simpa [h] using abs_correct t ρ x
  | some dropped =>
      simpa [h] using etaTop_sound h x ρ

end SK

namespace Tm

def eval : Tm Γ τ → Env Γ → Ty.denote τ
  | .var v, ρ => Var.lookup v ρ
  | .app f a, ρ => eval f ρ (eval a ρ)
  | .lam body, ρ => fun x => eval body (x, ρ)

def compile : Tm Γ τ → SK Γ τ
  | .var v => .var v
  | .app f a => .app (compile f) (compile a)
  | .lam body => SK.abs (compile body)

def compileEta : Tm Γ τ → SK Γ τ
  | .var v => .var v
  | .app f a => .app (compileEta f) (compileEta a)
  | .lam body => SK.absEta (compileEta body)

theorem compile_correct (t : Tm Γ τ) (ρ : Env Γ) :
    SK.eval (compile t) ρ = eval t ρ := by
  induction t with
  | var v =>
      rfl
  | app f a ihf iha =>
      simp [compile, eval, SK.eval, ihf, iha]
  | lam body ih =>
      funext x
      calc
        SK.eval (compile (.lam body)) ρ x
            = SK.eval (compile body) (x, ρ) := by
                simp [compile, SK.abs_correct]
        _ = eval body (x, ρ) := ih (x, ρ)

theorem compileEta_correct (t : Tm Γ τ) (ρ : Env Γ) :
    SK.eval (compileEta t) ρ = eval t ρ := by
  induction t with
  | var v =>
      rfl
  | app f a ihf iha =>
      simp [compileEta, eval, SK.eval, ihf, iha]
  | lam body ih =>
      funext x
      calc
        SK.eval (compileEta (.lam body)) ρ x
            = SK.eval (compileEta body) (x, ρ) := by
                simp [compileEta, SK.absEta_correct]
        _ = eval body (x, ρ) := ih (x, ρ)

private def eraseAt : Nat → Tm Γ τ → Bracket.Lam Nat
  | depth, .var v => .var (Var.toBinderName v depth)
  | depth, .app f a => .app (eraseAt depth f) (eraseAt depth a)
  | depth, .lam body => .lam depth (eraseAt (depth + 1) body)

def eraseClosed (t : Tm [] τ) : Bracket.Lam Nat :=
  eraseAt 0 t

end Tm

namespace SK

def varNilElim (v : Var [] τ) : α := by
  cases v

def eraseClosed : SK [] τ → Comb
  | .var v => varNilElim v
  | .app f a => .app (eraseClosed f) (eraseClosed a)
  | .k => .K
  | .s => .S

end SK

def compileClosed (t : Tm [] τ) : Comb :=
  SK.eraseClosed (Tm.compile t)

def compileClosedEta (t : Tm [] τ) : Comb :=
  SK.eraseClosed (Tm.compileEta t)

def compileClosedClassicCurrent? (t : Tm [] τ) : Option Comb :=
  (Bracket.Lam.compile (Tm.eraseClosed t)).erase?

/-! ## Small closed corpus -/

def tId : Tm [] (.bool ⟶ .bool) :=
  .lam (.var .vz)

def tConst : Tm [] (.bool ⟶ (.bool ⟶ .bool)) :=
  .lam (.lam (.var (.vs .vz)))

def tFlipConst : Tm [] (.bool ⟶ (.bool ⟶ .bool)) :=
  .lam (.lam (.var .vz))

def tApply : Tm [] ((.bool ⟶ .bool) ⟶ (.bool ⟶ .bool)) :=
  .lam (.lam (.app (.var (.vs .vz)) (.var .vz)))

def tCompose : Tm [] ((.bool ⟶ .bool) ⟶ ((.bool ⟶ .bool) ⟶ (.bool ⟶ .bool))) :=
  .lam (.lam (.lam (.app (.var (.vs (.vs .vz))) (.app (.var (.vs .vz)) (.var .vz)))))

structure ClosedPack where
  label : String
  ty : Ty
  term : Tm [] ty

def closedCorpus : List ClosedPack :=
  [ ⟨"id", .bool ⟶ .bool, tId⟩
  , ⟨"const", .bool ⟶ (.bool ⟶ .bool), tConst⟩
  , ⟨"flipConst", .bool ⟶ (.bool ⟶ .bool), tFlipConst⟩
  , ⟨"apply", (.bool ⟶ .bool) ⟶ (.bool ⟶ .bool), tApply⟩
  , ⟨"compose", (.bool ⟶ .bool) ⟶ ((.bool ⟶ .bool) ⟶ (.bool ⟶ .bool)), tCompose⟩
  ]

def corpusAgreementRow (row : ClosedPack) : Bool :=
  match compileClosedClassicCurrent? row.term with
  | some current => decide (compileClosed row.term = current)
  | none => false

def corpusAgreement : Bool :=
  closedCorpus.all corpusAgreementRow

end SwierstraBracket
end Combinators
end LoF
end HeytingLean
