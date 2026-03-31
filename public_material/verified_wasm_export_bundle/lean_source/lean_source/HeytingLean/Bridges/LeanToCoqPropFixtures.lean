namespace HeytingLean.Bridges.LeanToCoqPropFixtures

set_option linter.unusedVariables false

/-!
Small Prop-fragment fixtures intended for Lean→Coq kernel-term export tests.

Keep these as `def`s (not `theorem`s) so they can be exported via `--include-defs`.
They are intentionally tiny and avoid non-core dependencies.
-/

def modusPonens : ∀ (P Q : Prop), (P → Q) → P → Q :=
  fun P Q h p => h p

def andComm : ∀ (P Q : Prop), (P ∧ Q) → (Q ∧ P) :=
  fun P Q h => And.intro h.right h.left

def orComm : ∀ (P Q : Prop), (P ∨ Q) → (Q ∨ P) :=
  fun P Q h => Or.elim h (fun p => Or.inr p) (fun q => Or.inl q)

def orDistrAnd : ∀ (P Q R : Prop), (P ∨ (Q ∧ R)) → ((P ∨ Q) ∧ (P ∨ R)) :=
  fun P Q R h =>
    Or.elim h
      (fun p => And.intro (Or.inl p) (Or.inl p))
      (fun qr => And.intro (Or.inr qr.left) (Or.inr qr.right))

def andAssoc : ∀ (P Q R : Prop), (P ∧ Q) ∧ R → P ∧ (Q ∧ R) :=
  fun P Q R h => And.intro h.left.left (And.intro h.left.right h.right)

def orAssoc : ∀ (P Q R : Prop), (P ∨ Q) ∨ R → P ∨ (Q ∨ R) :=
  fun P Q R h =>
    Or.elim h
      (fun pq =>
        Or.elim pq
          (fun p => Or.inl p)
          (fun q => Or.inr (Or.inl q)))
      (fun r => Or.inr (Or.inr r))

def impTrans : ∀ (P Q R : Prop), (P → Q) → (Q → R) → P → R :=
  fun P Q R hpq hqr p => hqr (hpq p)

end HeytingLean.Bridges.LeanToCoqPropFixtures
