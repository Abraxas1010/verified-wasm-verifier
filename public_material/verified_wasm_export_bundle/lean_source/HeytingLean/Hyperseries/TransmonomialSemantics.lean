import HeytingLean.Hyperseries.ModelLaws
import HeytingLean.Hyperseries.SurrealExpLogSemantics
import HeytingLean.Hyperseries.Eval
import HeytingLean.Hyperseries.Transmonomials

namespace HeytingLean
namespace Hyperseries

namespace Transmonomial

/-- Integer-valued valuation proxy used for staged transmonomial semantics. -/
def valuation : Transmonomial → ℤ
  | .one => 0
  | .omegaPow e => e
  | .exp m => valuation m + 1
  | .log m => valuation m - 1

@[simp] theorem valuation_one : valuation .one = 0 := rfl
@[simp] theorem valuation_omegaPow (e : ℤ) : valuation (.omegaPow e) = e := rfl
@[simp] theorem valuation_exp (m : Transmonomial) : valuation (.exp m) = valuation m + 1 := rfl
@[simp] theorem valuation_log (m : Transmonomial) : valuation (.log m) = valuation m - 1 := rfl

theorem valuation_iterExp (n : ℕ) (m : Transmonomial) :
    valuation (Transmonomial.iterExp n m) = valuation m + n := by
  induction n generalizing m with
  | zero =>
      simp [Transmonomial.iterExp]
  | succ n ih =>
      simp [Transmonomial.iterExp, ih, add_assoc]

theorem valuation_iterLog (n : ℕ) (m : Transmonomial) :
    valuation (Transmonomial.iterLog n m) = valuation m - n := by
  induction n generalizing m with
  | zero =>
      simp [Transmonomial.iterLog]
  | succ n ih =>
      simp [Transmonomial.iterLog, ih, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

theorem valuation_iterExp_iterLog (n : ℕ) (m : Transmonomial) :
    valuation (Transmonomial.iterExp n (Transmonomial.iterLog n m)) = valuation m := by
  simp [valuation_iterExp, valuation_iterLog, sub_eq_add_neg]

theorem valuation_iterLog_iterExp (n : ℕ) (m : Transmonomial) :
    valuation (Transmonomial.iterLog n (Transmonomial.iterExp n m)) = valuation m := by
  simp [valuation_iterExp, valuation_iterLog, sub_eq_add_neg]

theorem valuation_eq_iterExp_iff (n : ℕ) (a b : Transmonomial) :
    valuation (Transmonomial.iterExp n a) = valuation (Transmonomial.iterExp n b) ↔
      valuation a = valuation b := by
  simp [valuation_iterExp]

theorem valuation_eq_iterLog_iff (n : ℕ) (a b : Transmonomial) :
    valuation (Transmonomial.iterLog n a) = valuation (Transmonomial.iterLog n b) ↔
      valuation a = valuation b := by
  simp [valuation_iterLog, sub_eq_add_neg]

theorem valuation_eq_exp_iff (a b : Transmonomial) :
    valuation (.exp a) = valuation (.exp b) ↔ valuation a = valuation b := by
  simp [valuation]

theorem valuation_eq_log_iff (a b : Transmonomial) :
    valuation (.log a) = valuation (.log b) ↔ valuation a = valuation b := by
  simp [valuation]

theorem valuation_exp_log (m : Transmonomial) :
    valuation (.exp (.log m)) = valuation m := by
  simp [valuation]

theorem valuation_log_exp (m : Transmonomial) :
    valuation (.log (.exp m)) = valuation m := by
  simp [valuation]

/-- Dominance preorder induced by staged valuation. -/
def Dominates (a b : Transmonomial) : Prop :=
  valuation b ≤ valuation a

@[simp] theorem dominates_refl (a : Transmonomial) : Dominates a a := le_rfl

theorem dominates_trans {a b c : Transmonomial}
    (hab : Dominates a b) (hbc : Dominates b c) : Dominates a c :=
  le_trans hbc hab

theorem dominates_total (a b : Transmonomial) : Dominates a b ∨ Dominates b a := by
  unfold Dominates
  exact (le_total (valuation b) (valuation a))

theorem valuation_eq_of_dominates_antisymm {a b : Transmonomial}
    (hab : Dominates a b) (hba : Dominates b a) :
    valuation a = valuation b := by
  exact le_antisymm hba hab

theorem valuation_eq_iff_dominates_antisymm (a b : Transmonomial) :
    valuation a = valuation b ↔ Dominates a b ∧ Dominates b a := by
  constructor
  · intro h
    constructor
    · unfold Dominates
      simp [h]
    · unfold Dominates
      simp [h]
  · intro h
    exact valuation_eq_of_dominates_antisymm h.1 h.2

/-- Asymptotic equivalence proxy induced by staged valuation equality. -/
def Equivalent (a b : Transmonomial) : Prop :=
  valuation a = valuation b

@[simp] theorem equivalent_iff (a b : Transmonomial) :
    Equivalent a b ↔ valuation a = valuation b := Iff.rfl

@[simp] theorem equivalent_refl (a : Transmonomial) : Equivalent a a := rfl

theorem equivalent_symm {a b : Transmonomial} (h : Equivalent a b) :
    Equivalent b a :=
  h.symm

theorem equivalent_trans {a b c : Transmonomial}
    (hab : Equivalent a b) (hbc : Equivalent b c) : Equivalent a c :=
  hab.trans hbc

theorem equivalent_iff_dominates_antisymm (a b : Transmonomial) :
    Equivalent a b ↔ Dominates a b ∧ Dominates b a := by
  simpa [Equivalent] using valuation_eq_iff_dominates_antisymm a b

instance : Setoid Transmonomial where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

/-- Quotient of transmonomials by valuation-equivalence. -/
abbrev AsymptoticClass : Type := Quotient (inferInstance : Setoid Transmonomial)

/-- Canonical class map into `AsymptoticClass`. -/
def toAsymptoticClass (m : Transmonomial) : AsymptoticClass := Quot.mk _ m

@[simp] theorem toAsymptoticClass_eq (a b : Transmonomial) :
    toAsymptoticClass a = toAsymptoticClass b ↔ Equivalent a b := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- Lift `exp` to asymptotic classes. -/
def AsymptoticClass.exp : AsymptoticClass → AsymptoticClass :=
  Quotient.map (fun m => .exp m) (by
    intro a b h
    exact (valuation_eq_exp_iff a b).2 h)

/-- Lift `log` to asymptotic classes. -/
def AsymptoticClass.log : AsymptoticClass → AsymptoticClass :=
  Quotient.map (fun m => .log m) (by
    intro a b h
    exact (valuation_eq_log_iff a b).2 h)

/-- Lift iterated `exp` to asymptotic classes. -/
def AsymptoticClass.iterExp (n : ℕ) : AsymptoticClass → AsymptoticClass :=
  Quotient.map (fun m => Transmonomial.iterExp n m) (by
    intro a b h
    exact (valuation_eq_iterExp_iff n a b).2 h)

/-- Lift iterated `log` to asymptotic classes. -/
def AsymptoticClass.iterLog (n : ℕ) : AsymptoticClass → AsymptoticClass :=
  Quotient.map (fun m => Transmonomial.iterLog n m) (by
    intro a b h
    exact (valuation_eq_iterLog_iff n a b).2 h)

@[simp] theorem asymptoticClass_exp_mk (m : Transmonomial) :
    AsymptoticClass.exp (toAsymptoticClass m) = toAsymptoticClass (.exp m) := by
  rfl

@[simp] theorem asymptoticClass_log_mk (m : Transmonomial) :
    AsymptoticClass.log (toAsymptoticClass m) = toAsymptoticClass (.log m) := by
  rfl

@[simp] theorem asymptoticClass_iterExp_mk (n : ℕ) (m : Transmonomial) :
    AsymptoticClass.iterExp n (toAsymptoticClass m) =
      toAsymptoticClass (Transmonomial.iterExp n m) := by
  rfl

@[simp] theorem asymptoticClass_iterLog_mk (n : ℕ) (m : Transmonomial) :
    AsymptoticClass.iterLog n (toAsymptoticClass m) =
      toAsymptoticClass (Transmonomial.iterLog n m) := by
  rfl

/-- Valuation descends to asymptotic classes. -/
def AsymptoticClass.valuation : AsymptoticClass → ℤ :=
  Quotient.lift Transmonomial.valuation (by
    intro a b h
    exact h)

@[simp] theorem asymptoticClass_valuation_mk (m : Transmonomial) :
    AsymptoticClass.valuation (toAsymptoticClass m) = Transmonomial.valuation m := rfl

@[simp] theorem asymptoticClass_valuation_exp (A : AsymptoticClass) :
    AsymptoticClass.valuation (AsymptoticClass.exp A) = AsymptoticClass.valuation A + 1 := by
  refine Quotient.inductionOn A ?_
  intro a
  simp [AsymptoticClass.exp, AsymptoticClass.valuation]

@[simp] theorem asymptoticClass_valuation_log (A : AsymptoticClass) :
    AsymptoticClass.valuation (AsymptoticClass.log A) = AsymptoticClass.valuation A - 1 := by
  refine Quotient.inductionOn A ?_
  intro a
  simp [AsymptoticClass.log, AsymptoticClass.valuation]

@[simp] theorem asymptoticClass_valuation_iterExp (n : ℕ) (A : AsymptoticClass) :
    AsymptoticClass.valuation (AsymptoticClass.iterExp n A) =
      AsymptoticClass.valuation A + n := by
  refine Quotient.inductionOn A ?_
  intro a
  simp [AsymptoticClass.iterExp, AsymptoticClass.valuation, valuation_iterExp]

@[simp] theorem asymptoticClass_valuation_iterLog (n : ℕ) (A : AsymptoticClass) :
    AsymptoticClass.valuation (AsymptoticClass.iterLog n A) =
      AsymptoticClass.valuation A - n := by
  refine Quotient.inductionOn A ?_
  intro a
  simp [AsymptoticClass.iterLog, AsymptoticClass.valuation, valuation_iterLog]

theorem asymptoticClass_eq_iff_valuation_eq (A B : AsymptoticClass) :
    A = B ↔ AsymptoticClass.valuation A = AsymptoticClass.valuation B := by
  refine Quotient.inductionOn₂ A B ?_
  intro a b
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

theorem asymptoticClass_eq_of_valuation_eq {A B : AsymptoticClass}
    (h : AsymptoticClass.valuation A = AsymptoticClass.valuation B) :
    A = B :=
  (asymptoticClass_eq_iff_valuation_eq A B).2 h

/-- Canonical class representative indexed by integer valuation. -/
def asymptoticClassOfInt (e : ℤ) : AsymptoticClass :=
  toAsymptoticClass (.omegaPow e)

@[simp] theorem asymptoticClass_valuation_ofInt (e : ℤ) :
    AsymptoticClass.valuation (asymptoticClassOfInt e) = e := by
  rfl

@[simp] theorem asymptoticClass_ofInt_valuation (A : AsymptoticClass) :
    asymptoticClassOfInt (AsymptoticClass.valuation A) = A := by
  apply asymptoticClass_eq_of_valuation_eq
  simp [asymptoticClassOfInt]

theorem asymptoticClass_eq_iff_intRep_eq (A B : AsymptoticClass) :
    asymptoticClassOfInt (AsymptoticClass.valuation A) =
      asymptoticClassOfInt (AsymptoticClass.valuation B) ↔ A = B := by
  simp

theorem asymptoticClass_exists_of_valuation (e : ℤ) :
    ∃ A : AsymptoticClass, AsymptoticClass.valuation A = e :=
  ⟨asymptoticClassOfInt e, by simp⟩

theorem asymptoticClass_existsUnique_of_valuation (e : ℤ) :
    ∃! A : AsymptoticClass, AsymptoticClass.valuation A = e := by
  refine ⟨asymptoticClassOfInt e, by simp, ?_⟩
  intro A hA
  apply asymptoticClass_eq_of_valuation_eq
  simpa using hA

def asymptoticClassEquivInt : AsymptoticClass ≃ ℤ where
  toFun := AsymptoticClass.valuation
  invFun := asymptoticClassOfInt
  left_inv := asymptoticClass_ofInt_valuation
  right_inv := asymptoticClass_valuation_ofInt

@[simp] theorem asymptoticClass_exp_ofInt (e : ℤ) :
    AsymptoticClass.exp (asymptoticClassOfInt e) = asymptoticClassOfInt (e + 1) := by
  apply asymptoticClass_eq_of_valuation_eq
  simp [asymptoticClassOfInt]

@[simp] theorem asymptoticClass_log_ofInt (e : ℤ) :
    AsymptoticClass.log (asymptoticClassOfInt e) = asymptoticClassOfInt (e - 1) := by
  apply asymptoticClass_eq_of_valuation_eq
  simp [asymptoticClassOfInt]

@[simp] theorem asymptoticClass_iterExp_ofInt (n : ℕ) (e : ℤ) :
    AsymptoticClass.iterExp n (asymptoticClassOfInt e) = asymptoticClassOfInt (e + n) := by
  apply asymptoticClass_eq_of_valuation_eq
  simp [asymptoticClass_valuation_iterExp, asymptoticClass_valuation_ofInt]

@[simp] theorem asymptoticClass_iterLog_ofInt (n : ℕ) (e : ℤ) :
    AsymptoticClass.iterLog n (asymptoticClassOfInt e) = asymptoticClassOfInt (e - n) := by
  apply asymptoticClass_eq_of_valuation_eq
  simp [asymptoticClass_valuation_iterLog, asymptoticClass_valuation_ofInt]

@[simp] theorem asymptoticClassEquivInt_apply (A : AsymptoticClass) :
    asymptoticClassEquivInt A = AsymptoticClass.valuation A := rfl

@[simp] theorem asymptoticClassEquivInt_symm_apply (e : ℤ) :
    asymptoticClassEquivInt.symm e = asymptoticClassOfInt e := rfl

@[simp] theorem asymptoticClassEquivInt_apply_ofInt (e : ℤ) :
    asymptoticClassEquivInt (asymptoticClassOfInt e) = e := by
  simp [asymptoticClassEquivInt]

@[simp] theorem asymptoticClassEquivInt_exp (A : AsymptoticClass) :
    asymptoticClassEquivInt (AsymptoticClass.exp A) = asymptoticClassEquivInt A + 1 := by
  simp [asymptoticClassEquivInt]

@[simp] theorem asymptoticClassEquivInt_log (A : AsymptoticClass) :
    asymptoticClassEquivInt (AsymptoticClass.log A) = asymptoticClassEquivInt A - 1 := by
  simp [asymptoticClassEquivInt]

@[simp] theorem asymptoticClassEquivInt_iterExp (n : ℕ) (A : AsymptoticClass) :
    asymptoticClassEquivInt (AsymptoticClass.iterExp n A) = asymptoticClassEquivInt A + n := by
  simp [asymptoticClassEquivInt]

@[simp] theorem asymptoticClassEquivInt_iterLog (n : ℕ) (A : AsymptoticClass) :
    asymptoticClassEquivInt (AsymptoticClass.iterLog n A) = asymptoticClassEquivInt A - n := by
  simp [asymptoticClassEquivInt]

theorem asymptoticClass_eq_exp_iff (A B : AsymptoticClass) :
    AsymptoticClass.exp A = AsymptoticClass.exp B ↔ A = B := by
  constructor
  · intro h
    apply asymptoticClass_eq_of_valuation_eq
    have hplus : asymptoticClassEquivInt A + 1 = asymptoticClassEquivInt B + 1 := by
      simpa using congrArg asymptoticClassEquivInt h
    exact add_right_cancel hplus
  · intro h
    simp [h]

theorem asymptoticClass_eq_log_iff (A B : AsymptoticClass) :
    AsymptoticClass.log A = AsymptoticClass.log B ↔ A = B := by
  constructor
  · intro h
    apply asymptoticClass_eq_of_valuation_eq
    have hplus : asymptoticClassEquivInt A + (-1 : ℤ) = asymptoticClassEquivInt B + (-1 : ℤ) := by
      simpa [sub_eq_add_neg] using congrArg asymptoticClassEquivInt h
    exact add_right_cancel hplus
  · intro h
    simp [h]

theorem asymptoticClass_eq_iterExp_iff (n : ℕ) (A B : AsymptoticClass) :
    AsymptoticClass.iterExp n A = AsymptoticClass.iterExp n B ↔ A = B := by
  constructor
  · intro h
    apply asymptoticClass_eq_of_valuation_eq
    have hplus : asymptoticClassEquivInt A + n = asymptoticClassEquivInt B + n := by
      simpa using congrArg asymptoticClassEquivInt h
    exact add_right_cancel hplus
  · intro h
    simp [h]

theorem asymptoticClass_eq_iterLog_iff (n : ℕ) (A B : AsymptoticClass) :
    AsymptoticClass.iterLog n A = AsymptoticClass.iterLog n B ↔ A = B := by
  constructor
  · intro h
    apply asymptoticClass_eq_of_valuation_eq
    have hplus :
        asymptoticClassEquivInt A + (-(n : ℤ)) =
          asymptoticClassEquivInt B + (-(n : ℤ)) := by
      simpa [sub_eq_add_neg] using congrArg asymptoticClassEquivInt h
    exact add_right_cancel hplus
  · intro h
    simp [h]

@[simp] theorem asymptoticClass_exp_log (A : AsymptoticClass) :
    AsymptoticClass.exp (AsymptoticClass.log A) = A := by
  apply asymptoticClass_eq_of_valuation_eq
  simp

@[simp] theorem asymptoticClass_log_exp (A : AsymptoticClass) :
    AsymptoticClass.log (AsymptoticClass.exp A) = A := by
  apply asymptoticClass_eq_of_valuation_eq
  simp

@[simp] theorem asymptoticClass_iterExp_iterLog (n : ℕ) (A : AsymptoticClass) :
    AsymptoticClass.iterExp n (AsymptoticClass.iterLog n A) = A := by
  apply asymptoticClass_eq_of_valuation_eq
  simp [sub_eq_add_neg]

@[simp] theorem asymptoticClass_iterLog_iterExp (n : ℕ) (A : AsymptoticClass) :
    AsymptoticClass.iterLog n (AsymptoticClass.iterExp n A) = A := by
  apply asymptoticClass_eq_of_valuation_eq
  simp [sub_eq_add_neg]

instance : Preorder Transmonomial where
  le := Dominates
  le_refl := dominates_refl
  le_trans := by
    intro a b c hab hbc
    exact dominates_trans hab hbc

theorem equivalent_iterExp_iff (n : ℕ) (a b : Transmonomial) :
    Equivalent (Transmonomial.iterExp n a) (Transmonomial.iterExp n b) ↔ Equivalent a b := by
  simpa [Equivalent] using valuation_eq_iterExp_iff n a b

theorem equivalent_iterLog_iff (n : ℕ) (a b : Transmonomial) :
    Equivalent (Transmonomial.iterLog n a) (Transmonomial.iterLog n b) ↔ Equivalent a b := by
  simpa [Equivalent] using valuation_eq_iterLog_iff n a b

theorem equivalent_iterExp_iterLog_iff (n : ℕ) (a b : Transmonomial) :
    Equivalent (Transmonomial.iterExp n (Transmonomial.iterLog n a))
      (Transmonomial.iterExp n (Transmonomial.iterLog n b)) ↔
      Equivalent a b := by
  simpa [Equivalent] using
    (valuation_eq_iterExp_iff (n := n) (a := Transmonomial.iterLog n a)
      (b := Transmonomial.iterLog n b)).trans (valuation_eq_iterLog_iff n a b)

theorem equivalent_iterLog_iterExp_iff (n : ℕ) (a b : Transmonomial) :
    Equivalent (Transmonomial.iterLog n (Transmonomial.iterExp n a))
      (Transmonomial.iterLog n (Transmonomial.iterExp n b)) ↔
      Equivalent a b := by
  simpa [Equivalent] using
    (valuation_eq_iterLog_iff (n := n) (a := Transmonomial.iterExp n a)
      (b := Transmonomial.iterExp n b)).trans (valuation_eq_iterExp_iff n a b)

theorem equivalent_exp_iff (a b : Transmonomial) :
    Equivalent (.exp a) (.exp b) ↔ Equivalent a b := by
  exact valuation_eq_exp_iff a b

theorem equivalent_log_iff (a b : Transmonomial) :
    Equivalent (.log a) (.log b) ↔ Equivalent a b := by
  exact valuation_eq_log_iff a b

theorem equivalent_exp_log_iff (a b : Transmonomial) :
    Equivalent (.exp (.log a)) (.exp (.log b)) ↔ Equivalent a b := by
  exact (equivalent_exp_iff (.log a) (.log b)).trans (equivalent_log_iff a b)

theorem equivalent_log_exp_iff (a b : Transmonomial) :
    Equivalent (.log (.exp a)) (.log (.exp b)) ↔ Equivalent a b := by
  exact (equivalent_log_iff (.exp a) (.exp b)).trans (equivalent_exp_iff a b)

theorem equivalent_iterExp_iterLog_of_equivalent (n : ℕ) {a b : Transmonomial}
    (h : Equivalent a b) :
    Equivalent (Transmonomial.iterExp n (Transmonomial.iterLog n a))
      (Transmonomial.iterExp n (Transmonomial.iterLog n b)) :=
  (equivalent_iterExp_iterLog_iff n a b).2 h

theorem equivalent_iterLog_iterExp_of_equivalent (n : ℕ) {a b : Transmonomial}
    (h : Equivalent a b) :
    Equivalent (Transmonomial.iterLog n (Transmonomial.iterExp n a))
      (Transmonomial.iterLog n (Transmonomial.iterExp n b)) :=
  (equivalent_iterLog_iterExp_iff n a b).2 h

theorem equivalent_exp_of_equivalent {a b : Transmonomial} (h : Equivalent a b) :
    Equivalent (.exp a) (.exp b) :=
  (equivalent_exp_iff a b).2 h

theorem equivalent_log_of_equivalent {a b : Transmonomial} (h : Equivalent a b) :
    Equivalent (.log a) (.log b) :=
  (equivalent_log_iff a b).2 h

theorem equivalent_exp_log_of_equivalent {a b : Transmonomial} (h : Equivalent a b) :
    Equivalent (.exp (.log a)) (.exp (.log b)) :=
  (equivalent_exp_log_iff a b).2 h

theorem equivalent_log_exp_of_equivalent {a b : Transmonomial} (h : Equivalent a b) :
    Equivalent (.log (.exp a)) (.log (.exp b)) :=
  (equivalent_log_exp_iff a b).2 h

theorem dominates_iterExp_iff (n : ℕ) (a b : Transmonomial) :
    Dominates (Transmonomial.iterExp n a) (Transmonomial.iterExp n b) ↔ Dominates a b := by
  unfold Dominates
  simp [valuation_iterExp]

theorem dominates_iterLog_iff (n : ℕ) (a b : Transmonomial) :
    Dominates (Transmonomial.iterLog n a) (Transmonomial.iterLog n b) ↔ Dominates a b := by
  unfold Dominates
  simp [valuation_iterLog]

theorem dominates_iterExp_iterLog_iff (n : ℕ) (a b : Transmonomial) :
    Dominates (Transmonomial.iterExp n (Transmonomial.iterLog n a))
      (Transmonomial.iterExp n (Transmonomial.iterLog n b)) ↔
      Dominates a b :=
  (dominates_iterExp_iff n (Transmonomial.iterLog n a) (Transmonomial.iterLog n b)).trans
    (dominates_iterLog_iff n a b)

theorem dominates_iterLog_iterExp_iff (n : ℕ) (a b : Transmonomial) :
    Dominates (Transmonomial.iterLog n (Transmonomial.iterExp n a))
      (Transmonomial.iterLog n (Transmonomial.iterExp n b)) ↔
      Dominates a b :=
  (dominates_iterLog_iff n (Transmonomial.iterExp n a) (Transmonomial.iterExp n b)).trans
    (dominates_iterExp_iff n a b)

theorem dominates_iterExp_iterLog_of_dominates (n : ℕ) {a b : Transmonomial}
    (h : Dominates a b) :
    Dominates (Transmonomial.iterExp n (Transmonomial.iterLog n a))
      (Transmonomial.iterExp n (Transmonomial.iterLog n b)) :=
  (dominates_iterExp_iterLog_iff n a b).2 h

theorem dominates_iterLog_iterExp_of_dominates (n : ℕ) {a b : Transmonomial}
    (h : Dominates a b) :
    Dominates (Transmonomial.iterLog n (Transmonomial.iterExp n a))
      (Transmonomial.iterLog n (Transmonomial.iterExp n b)) :=
  (dominates_iterLog_iterExp_iff n a b).2 h

theorem dominates_exp_log_iff (a b : Transmonomial) :
    Dominates (.exp (.log a)) (.exp (.log b)) ↔ Dominates a b := by
  simpa [Transmonomial.iterExp, Transmonomial.iterLog] using
    dominates_iterExp_iterLog_iff (n := 1) a b

theorem dominates_log_exp_iff (a b : Transmonomial) :
    Dominates (.log (.exp a)) (.log (.exp b)) ↔ Dominates a b := by
  simpa [Transmonomial.iterExp, Transmonomial.iterLog] using
    dominates_iterLog_iterExp_iff (n := 1) a b

theorem dominates_exp_log_of_dominates {a b : Transmonomial} (h : Dominates a b) :
    Dominates (.exp (.log a)) (.exp (.log b)) :=
  (dominates_exp_log_iff a b).2 h

theorem dominates_log_exp_of_dominates {a b : Transmonomial} (h : Dominates a b) :
    Dominates (.log (.exp a)) (.log (.exp b)) :=
  (dominates_log_exp_iff a b).2 h

theorem dominates_exp_iff (a b : Transmonomial) :
    Dominates (.exp a) (.exp b) ↔ Dominates a b := by
  simpa [Transmonomial.iterExp] using dominates_iterExp_iff (n := 1) a b

theorem dominates_log_iff (a b : Transmonomial) :
    Dominates (.log a) (.log b) ↔ Dominates a b := by
  simpa [Transmonomial.iterLog] using dominates_iterLog_iff (n := 1) a b

theorem dominates_exp_of_dominates {a b : Transmonomial} (h : Dominates a b) :
    Dominates (.exp a) (.exp b) :=
  (dominates_exp_iff a b).2 h

theorem dominates_log_of_dominates {a b : Transmonomial} (h : Dominates a b) :
    Dominates (.log a) (.log b) :=
  (dominates_log_iff a b).2 h

/-- Dominance relation on asymptotic classes induced from representatives. -/
def AsymptoticClass.Dominates (A B : AsymptoticClass) : Prop :=
  Quotient.liftOn₂ A B Transmonomial.Dominates (by
    intro a b c d hab hcd
    apply propext
    unfold Transmonomial.Dominates
    change Equivalent a c at hab
    change Equivalent b d at hcd
    unfold Equivalent at hab hcd
    constructor
    · intro h
      calc
        d.valuation = b.valuation := hcd.symm
        _ ≤ a.valuation := h
        _ = c.valuation := hab
    · intro h
      calc
        b.valuation = d.valuation := hcd
        _ ≤ c.valuation := h
        _ = a.valuation := hab.symm)

@[simp] theorem asymptoticClass_dominates_mk (a b : Transmonomial) :
    AsymptoticClass.Dominates (toAsymptoticClass a) (toAsymptoticClass b) ↔
      Transmonomial.Dominates a b := by
  simp [AsymptoticClass.Dominates, toAsymptoticClass]

theorem asymptoticClass_dominates_iff_valuation (A B : AsymptoticClass) :
    AsymptoticClass.Dominates A B ↔
      AsymptoticClass.valuation B ≤ AsymptoticClass.valuation A := by
  refine Quotient.inductionOn₂ A B ?_
  intro a b
  simp [AsymptoticClass.Dominates, AsymptoticClass.valuation, Transmonomial.Dominates]

@[simp] theorem asymptoticClass_dominates_ofInt_iff (a b : ℤ) :
    AsymptoticClass.Dominates (asymptoticClassOfInt a) (asymptoticClassOfInt b) ↔ b ≤ a := by
  simp [asymptoticClass_dominates_iff_valuation]

theorem asymptoticClass_dominates_refl (A : AsymptoticClass) :
    AsymptoticClass.Dominates A A := by
  refine Quotient.inductionOn A ?_
  intro a
  change Transmonomial.Dominates a a
  exact Transmonomial.dominates_refl a

theorem asymptoticClass_dominates_trans {A B C : AsymptoticClass}
    (hAB : AsymptoticClass.Dominates A B) (hBC : AsymptoticClass.Dominates B C) :
    AsymptoticClass.Dominates A C := by
  refine Quotient.inductionOn₃ A B C ?_ hAB hBC
  intro a b c hab hbc
  exact Transmonomial.dominates_trans hab hbc

theorem asymptoticClass_dominates_total (A B : AsymptoticClass) :
    AsymptoticClass.Dominates A B ∨ AsymptoticClass.Dominates B A := by
  refine Quotient.inductionOn₂ A B ?_
  intro a b
  exact Transmonomial.dominates_total a b

theorem asymptoticClass_valuation_eq_iff_dominates_antisymm (A B : AsymptoticClass) :
    AsymptoticClass.valuation A = AsymptoticClass.valuation B ↔
      AsymptoticClass.Dominates A B ∧ AsymptoticClass.Dominates B A := by
  constructor
  · intro h
    constructor
    · exact (asymptoticClass_dominates_iff_valuation A B).2 (by simp [h])
    · exact (asymptoticClass_dominates_iff_valuation B A).2 (by simp [h])
  · intro h
    exact le_antisymm
      ((asymptoticClass_dominates_iff_valuation B A).1 h.2)
      ((asymptoticClass_dominates_iff_valuation A B).1 h.1)

theorem asymptoticClass_eq_iff_dominates_antisymm (A B : AsymptoticClass) :
    A = B ↔ AsymptoticClass.Dominates A B ∧ AsymptoticClass.Dominates B A := by
  constructor
  · intro h
    subst h
    exact ⟨asymptoticClass_dominates_refl _, asymptoticClass_dominates_refl _⟩
  · intro h
    exact asymptoticClass_eq_of_valuation_eq
      ((asymptoticClass_valuation_eq_iff_dominates_antisymm A B).2 h)

theorem asymptoticClass_eq_of_dominates_antisymm {A B : AsymptoticClass}
    (hAB : AsymptoticClass.Dominates A B) (hBA : AsymptoticClass.Dominates B A) :
    A = B :=
  (asymptoticClass_eq_iff_dominates_antisymm A B).2 ⟨hAB, hBA⟩

instance : PartialOrder AsymptoticClass where
  le := AsymptoticClass.Dominates
  le_refl := asymptoticClass_dominates_refl
  le_trans := by
    intro A B C hAB hBC
    exact asymptoticClass_dominates_trans hAB hBC
  le_antisymm := by
    intro A B hAB hBA
    exact asymptoticClass_eq_of_dominates_antisymm hAB hBA

instance : DecidableEq AsymptoticClass := by
  intro A B
  exact decidable_of_iff (AsymptoticClass.valuation A = AsymptoticClass.valuation B)
    (asymptoticClass_eq_iff_valuation_eq A B).symm

instance : DecidableLE AsymptoticClass := by
  intro A B
  exact decidable_of_iff (AsymptoticClass.valuation B ≤ AsymptoticClass.valuation A)
    (asymptoticClass_dominates_iff_valuation A B).symm

theorem asymptoticClass_dominates_exp_iff (A B : AsymptoticClass) :
    AsymptoticClass.Dominates (AsymptoticClass.exp A) (AsymptoticClass.exp B) ↔
      AsymptoticClass.Dominates A B := by
  refine Quotient.inductionOn₂ A B ?_
  intro a b
  simpa [AsymptoticClass.Dominates, AsymptoticClass.exp] using
    (Transmonomial.dominates_exp_iff a b)

theorem asymptoticClass_dominates_log_iff (A B : AsymptoticClass) :
    AsymptoticClass.Dominates (AsymptoticClass.log A) (AsymptoticClass.log B) ↔
      AsymptoticClass.Dominates A B := by
  refine Quotient.inductionOn₂ A B ?_
  intro a b
  simpa [AsymptoticClass.Dominates, AsymptoticClass.log] using
    (Transmonomial.dominates_log_iff a b)

theorem asymptoticClass_dominates_iterExp_iff (n : ℕ) (A B : AsymptoticClass) :
    AsymptoticClass.Dominates (AsymptoticClass.iterExp n A) (AsymptoticClass.iterExp n B) ↔
      AsymptoticClass.Dominates A B := by
  refine Quotient.inductionOn₂ A B ?_
  intro a b
  simpa [AsymptoticClass.Dominates, AsymptoticClass.iterExp] using
    (Transmonomial.dominates_iterExp_iff n a b)

theorem asymptoticClass_dominates_iterLog_iff (n : ℕ) (A B : AsymptoticClass) :
    AsymptoticClass.Dominates (AsymptoticClass.iterLog n A) (AsymptoticClass.iterLog n B) ↔
      AsymptoticClass.Dominates A B := by
  refine Quotient.inductionOn₂ A B ?_
  intro a b
  simpa [AsymptoticClass.Dominates, AsymptoticClass.iterLog] using
    (Transmonomial.dominates_iterLog_iff n a b)

theorem asymptoticClass_exp_monotone : Monotone AsymptoticClass.exp := by
  intro A B hAB
  exact (asymptoticClass_dominates_exp_iff A B).2 hAB

theorem asymptoticClass_log_monotone : Monotone AsymptoticClass.log := by
  intro A B hAB
  exact (asymptoticClass_dominates_log_iff A B).2 hAB

theorem asymptoticClass_iterExp_monotone (n : ℕ) :
    Monotone (AsymptoticClass.iterExp n) := by
  intro A B hAB
  exact (asymptoticClass_dominates_iterExp_iff n A B).2 hAB

theorem asymptoticClass_iterLog_monotone (n : ℕ) :
    Monotone (AsymptoticClass.iterLog n) := by
  intro A B hAB
  exact (asymptoticClass_dominates_iterLog_iff n A B).2 hAB

def asymptoticClassExpEquiv : AsymptoticClass ≃ AsymptoticClass where
  toFun := AsymptoticClass.exp
  invFun := AsymptoticClass.log
  left_inv := asymptoticClass_log_exp
  right_inv := asymptoticClass_exp_log

def asymptoticClassExpOrderIso : AsymptoticClass ≃o AsymptoticClass where
  toEquiv := asymptoticClassExpEquiv
  map_rel_iff' := by
    intro A B
    simpa using (asymptoticClass_dominates_exp_iff A B)

def asymptoticClassLogOrderIso : AsymptoticClass ≃o AsymptoticClass :=
  asymptoticClassExpOrderIso.symm

def asymptoticClassIterExpEquiv (n : ℕ) : AsymptoticClass ≃ AsymptoticClass where
  toFun := AsymptoticClass.iterExp n
  invFun := AsymptoticClass.iterLog n
  left_inv := asymptoticClass_iterLog_iterExp n
  right_inv := asymptoticClass_iterExp_iterLog n

def asymptoticClassIterExpOrderIso (n : ℕ) : AsymptoticClass ≃o AsymptoticClass where
  toEquiv := asymptoticClassIterExpEquiv n
  map_rel_iff' := by
    intro A B
    simpa using (asymptoticClass_dominates_iterExp_iff n A B)

def asymptoticClassIterLogOrderIso (n : ℕ) : AsymptoticClass ≃o AsymptoticClass :=
  (asymptoticClassIterExpOrderIso n).symm

def asymptoticClassOrderIsoIntDual : AsymptoticClass ≃o OrderDual ℤ where
  toFun := fun A => (AsymptoticClass.valuation A : OrderDual ℤ)
  invFun := fun e => toAsymptoticClass (.omegaPow (show ℤ from e))
  left_inv := by
    intro A
    apply asymptoticClass_eq_of_valuation_eq
    simp
  right_inv := by
    intro e
    simp
  map_rel_iff' := by
    intro A B
    constructor
    · intro h
      exact (asymptoticClass_dominates_iff_valuation A B).2 (by simpa using h)
    · intro h
      exact (by
        have hval : AsymptoticClass.valuation B ≤ AsymptoticClass.valuation A :=
          (asymptoticClass_dominates_iff_valuation A B).1 h
        simpa using hval)

@[simp] theorem asymptoticClassOrderIsoIntDual_apply (A : AsymptoticClass) :
    asymptoticClassOrderIsoIntDual A = (AsymptoticClass.valuation A : OrderDual ℤ) := rfl

@[simp] theorem asymptoticClassOrderIsoIntDual_apply_eq_equivInt (A : AsymptoticClass) :
    asymptoticClassOrderIsoIntDual A = (asymptoticClassEquivInt A : OrderDual ℤ) := rfl

@[simp] theorem asymptoticClassOrderIsoIntDual_symm_apply (e : OrderDual ℤ) :
    asymptoticClassOrderIsoIntDual.symm e = asymptoticClassOfInt (show ℤ from e) := rfl

@[simp] theorem asymptoticClassOrderIsoIntDual_symm_apply_eq_equivInt (e : OrderDual ℤ) :
    asymptoticClassOrderIsoIntDual.symm e =
      asymptoticClassEquivInt.symm (show ℤ from e) := rfl

@[simp] theorem asymptoticClassOrderIsoIntDual_apply_ofInt (e : ℤ) :
    asymptoticClassOrderIsoIntDual (asymptoticClassOfInt e) = (e : OrderDual ℤ) := by
  simp [asymptoticClassOrderIsoIntDual]

@[simp] theorem asymptoticClassOrderIsoIntDual_exp (A : AsymptoticClass) :
    asymptoticClassOrderIsoIntDual (AsymptoticClass.exp A) =
      (asymptoticClassOrderIsoIntDual A : OrderDual ℤ) + 1 := by
  simp [asymptoticClassOrderIsoIntDual]

@[simp] theorem asymptoticClassOrderIsoIntDual_log (A : AsymptoticClass) :
    asymptoticClassOrderIsoIntDual (AsymptoticClass.log A) =
      (asymptoticClassOrderIsoIntDual A : OrderDual ℤ) - 1 := by
  simp [asymptoticClassOrderIsoIntDual]

@[simp] theorem asymptoticClassOrderIsoIntDual_iterExp (n : ℕ) (A : AsymptoticClass) :
    asymptoticClassOrderIsoIntDual (AsymptoticClass.iterExp n A) =
      (asymptoticClassOrderIsoIntDual A : OrderDual ℤ) +
        (show OrderDual ℤ from (n : ℤ)) := by
  simp

@[simp] theorem asymptoticClassOrderIsoIntDual_iterLog (n : ℕ) (A : AsymptoticClass) :
    asymptoticClassOrderIsoIntDual (AsymptoticClass.iterLog n A) =
      (asymptoticClassOrderIsoIntDual A : OrderDual ℤ) -
        (show OrderDual ℤ from (n : ℤ)) := by
  simp

theorem asymptoticClass_dominates_iff_orderIsoIntDual_le (A B : AsymptoticClass) :
    AsymptoticClass.Dominates A B ↔
      asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B := by
  simpa [asymptoticClassOrderIsoIntDual] using
    (asymptoticClass_dominates_iff_valuation A B)

theorem asymptoticClass_eq_iff_equivInt_eq (A B : AsymptoticClass) :
    A = B ↔ asymptoticClassEquivInt A = asymptoticClassEquivInt B := by
  simpa [asymptoticClassEquivInt] using asymptoticClass_eq_iff_valuation_eq A B

theorem asymptoticClass_dominates_iff_equivInt_le (A B : AsymptoticClass) :
    AsymptoticClass.Dominates A B ↔ asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A := by
  simpa [asymptoticClassEquivInt] using asymptoticClass_dominates_iff_valuation A B

theorem asymptoticClass_dominates_of_equivInt_le {A B : AsymptoticClass}
    (h : asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A) :
    AsymptoticClass.Dominates A B :=
  (asymptoticClass_dominates_iff_equivInt_le A B).2 h

theorem asymptoticClass_equivInt_le_of_dominates {A B : AsymptoticClass}
    (h : AsymptoticClass.Dominates A B) :
    asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A :=
  (asymptoticClass_dominates_iff_equivInt_le A B).1 h

theorem asymptoticClass_dominates_of_orderIsoIntDual_le {A B : AsymptoticClass}
    (h : asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B) :
    AsymptoticClass.Dominates A B :=
  (asymptoticClass_dominates_iff_orderIsoIntDual_le A B).2 h

theorem asymptoticClass_orderIsoIntDual_le_of_dominates {A B : AsymptoticClass}
    (h : AsymptoticClass.Dominates A B) :
    asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B :=
  (asymptoticClass_dominates_iff_orderIsoIntDual_le A B).1 h

theorem asymptoticClass_dominates_iff_valuation_equivInt_orderIsoIntDual_le
    (A B : AsymptoticClass) :
    AsymptoticClass.Dominates A B ↔
      AsymptoticClass.valuation B ≤ AsymptoticClass.valuation A ∧
      asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
      asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact (asymptoticClass_dominates_iff_valuation A B).1 h
    · exact (asymptoticClass_dominates_iff_equivInt_le A B).1 h
    · exact (asymptoticClass_dominates_iff_orderIsoIntDual_le A B).1 h
  · intro h
    exact (asymptoticClass_dominates_iff_valuation A B).2 h.1

theorem asymptoticClass_dominates_valuation_equivInt_orderIsoIntDual_le_of_dominates
    {A B : AsymptoticClass} (h : AsymptoticClass.Dominates A B) :
    AsymptoticClass.valuation B ≤ AsymptoticClass.valuation A ∧
      asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
      asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B :=
  (asymptoticClass_dominates_iff_valuation_equivInt_orderIsoIntDual_le A B).1 h

theorem asymptoticClass_dominates_of_valuation_equivInt_orderIsoIntDual_le
    {A B : AsymptoticClass}
    (h : AsymptoticClass.valuation B ≤ AsymptoticClass.valuation A ∧
      asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
      asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B) :
    AsymptoticClass.Dominates A B :=
  (asymptoticClass_dominates_iff_valuation_equivInt_orderIsoIntDual_le A B).2 h

theorem asymptoticClass_valuation_le_of_dominates_valuation_equivInt_orderIsoIntDual_le
    {A B : AsymptoticClass}
    (h : AsymptoticClass.valuation B ≤ AsymptoticClass.valuation A ∧
      asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
      asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B) :
    AsymptoticClass.valuation B ≤ AsymptoticClass.valuation A :=
  h.1

theorem asymptoticClass_equivInt_le_of_dominates_valuation_equivInt_orderIsoIntDual_le
    {A B : AsymptoticClass}
    (h : AsymptoticClass.valuation B ≤ AsymptoticClass.valuation A ∧
      asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
      asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B) :
    asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A :=
  h.2.1

theorem asymptoticClass_orderIsoIntDual_le_of_dominates_valuation_equivInt_orderIsoIntDual_le
    {A B : AsymptoticClass}
    (h : AsymptoticClass.valuation B ≤ AsymptoticClass.valuation A ∧
      asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
      asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B) :
    asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B :=
  h.2.2

theorem asymptoticClass_dominates_valuation_equivInt_orderIsoIntDual_le_of_valuation_le
    {A B : AsymptoticClass}
    (h : AsymptoticClass.valuation B ≤ AsymptoticClass.valuation A) :
    AsymptoticClass.valuation B ≤ AsymptoticClass.valuation A ∧
      asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
      asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B :=
  asymptoticClass_dominates_valuation_equivInt_orderIsoIntDual_le_of_dominates
    ((asymptoticClass_dominates_iff_valuation A B).2 h)

theorem asymptoticClass_dominates_valuation_equivInt_orderIsoIntDual_le_of_equivInt_le
    {A B : AsymptoticClass}
    (h : asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A) :
    AsymptoticClass.valuation B ≤ AsymptoticClass.valuation A ∧
      asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
      asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B :=
  asymptoticClass_dominates_valuation_equivInt_orderIsoIntDual_le_of_dominates
    (asymptoticClass_dominates_of_equivInt_le h)

theorem asymptoticClass_dominates_valuation_equivInt_orderIsoIntDual_le_of_orderIsoIntDual_le
    {A B : AsymptoticClass}
    (h : asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B) :
    AsymptoticClass.valuation B ≤ AsymptoticClass.valuation A ∧
      asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
      asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B :=
  asymptoticClass_dominates_valuation_equivInt_orderIsoIntDual_le_of_dominates
    (asymptoticClass_dominates_of_orderIsoIntDual_le h)

theorem asymptoticClass_dominates_antisymm_iff_equivInt_antisymm
    (A B : AsymptoticClass) :
    (AsymptoticClass.Dominates A B ∧ AsymptoticClass.Dominates B A) ↔
      (asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
        asymptoticClassEquivInt A ≤ asymptoticClassEquivInt B) := by
  constructor
  · intro h
    exact ⟨
      (asymptoticClass_dominates_iff_equivInt_le A B).1 h.1,
      (asymptoticClass_dominates_iff_equivInt_le B A).1 h.2
    ⟩
  · intro h
    exact ⟨
      (asymptoticClass_dominates_iff_equivInt_le A B).2 h.1,
      (asymptoticClass_dominates_iff_equivInt_le B A).2 h.2
    ⟩

theorem asymptoticClass_dominates_antisymm_iff_orderIsoIntDual_antisymm
    (A B : AsymptoticClass) :
    (AsymptoticClass.Dominates A B ∧ AsymptoticClass.Dominates B A) ↔
      (asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B ∧
        asymptoticClassOrderIsoIntDual B ≤ asymptoticClassOrderIsoIntDual A) := by
  constructor
  · intro h
    exact ⟨
      (asymptoticClass_dominates_iff_orderIsoIntDual_le A B).1 h.1,
      (asymptoticClass_dominates_iff_orderIsoIntDual_le B A).1 h.2
    ⟩
  · intro h
    exact ⟨
      (asymptoticClass_dominates_iff_orderIsoIntDual_le A B).2 h.1,
      (asymptoticClass_dominates_iff_orderIsoIntDual_le B A).2 h.2
    ⟩

theorem asymptoticClass_eq_of_equivInt_antisymm {A B : AsymptoticClass}
    (hBA : asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A)
    (hAB : asymptoticClassEquivInt A ≤ asymptoticClassEquivInt B) :
    A = B := by
  apply (asymptoticClass_eq_iff_equivInt_eq A B).2
  exact le_antisymm hAB hBA

theorem asymptoticClass_eq_iff_equivInt_antisymm (A B : AsymptoticClass) :
    A = B ↔
      asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
      asymptoticClassEquivInt A ≤ asymptoticClassEquivInt B := by
  constructor
  · intro h
    subst h
    exact ⟨le_rfl, le_rfl⟩
  · intro h
    exact asymptoticClass_eq_of_equivInt_antisymm h.1 h.2

theorem asymptoticClass_eq_of_orderIsoIntDual_antisymm {A B : AsymptoticClass}
    (hAB : asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B)
    (hBA : asymptoticClassOrderIsoIntDual B ≤ asymptoticClassOrderIsoIntDual A) :
    A = B := by
  apply asymptoticClass_eq_of_valuation_eq
  exact congrArg (fun x : OrderDual ℤ => (show ℤ from x)) (le_antisymm hAB hBA)

theorem asymptoticClass_eq_iff_orderIsoIntDual_antisymm (A B : AsymptoticClass) :
    A = B ↔
      asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B ∧
      asymptoticClassOrderIsoIntDual B ≤ asymptoticClassOrderIsoIntDual A := by
  constructor
  · intro h
    subst h
    exact ⟨le_rfl, le_rfl⟩
  · intro h
    exact asymptoticClass_eq_of_orderIsoIntDual_antisymm h.1 h.2

theorem asymptoticClass_eq_iff_dominates_equivInt_orderIso_antisymm
    (A B : AsymptoticClass) :
    A = B ↔
      (AsymptoticClass.Dominates A B ∧ AsymptoticClass.Dominates B A) ∧
      (asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
        asymptoticClassEquivInt A ≤ asymptoticClassEquivInt B) ∧
      (asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B ∧
        asymptoticClassOrderIsoIntDual B ≤ asymptoticClassOrderIsoIntDual A) := by
  constructor
  · intro h
    subst h
    exact ⟨⟨asymptoticClass_dominates_refl _, asymptoticClass_dominates_refl _⟩, ⟨le_rfl, le_rfl⟩, ⟨le_rfl, le_rfl⟩⟩
  · intro h
    exact asymptoticClass_eq_of_dominates_antisymm h.1.1 h.1.2

theorem asymptoticClass_dominates_equivInt_orderIso_antisymm_of_eq
    {A B : AsymptoticClass} (h : A = B) :
    (AsymptoticClass.Dominates A B ∧ AsymptoticClass.Dominates B A) ∧
      (asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
        asymptoticClassEquivInt A ≤ asymptoticClassEquivInt B) ∧
      (asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B ∧
        asymptoticClassOrderIsoIntDual B ≤ asymptoticClassOrderIsoIntDual A) :=
  (asymptoticClass_eq_iff_dominates_equivInt_orderIso_antisymm A B).1 h

theorem asymptoticClass_eq_of_dominates_equivInt_orderIso_antisymm
    {A B : AsymptoticClass}
    (h : (AsymptoticClass.Dominates A B ∧ AsymptoticClass.Dominates B A) ∧
      (asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
        asymptoticClassEquivInt A ≤ asymptoticClassEquivInt B) ∧
      (asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B ∧
        asymptoticClassOrderIsoIntDual B ≤ asymptoticClassOrderIsoIntDual A)) :
    A = B :=
  (asymptoticClass_eq_iff_dominates_equivInt_orderIso_antisymm A B).2 h

theorem asymptoticClass_dominates_antisymm_of_dominates_equivInt_orderIso_antisymm
    {A B : AsymptoticClass}
    (h : (AsymptoticClass.Dominates A B ∧ AsymptoticClass.Dominates B A) ∧
      (asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
        asymptoticClassEquivInt A ≤ asymptoticClassEquivInt B) ∧
      (asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B ∧
        asymptoticClassOrderIsoIntDual B ≤ asymptoticClassOrderIsoIntDual A)) :
    AsymptoticClass.Dominates A B ∧ AsymptoticClass.Dominates B A :=
  h.1

theorem asymptoticClass_equivInt_antisymm_of_dominates_equivInt_orderIso_antisymm
    {A B : AsymptoticClass}
    (h : (AsymptoticClass.Dominates A B ∧ AsymptoticClass.Dominates B A) ∧
      (asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
        asymptoticClassEquivInt A ≤ asymptoticClassEquivInt B) ∧
      (asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B ∧
        asymptoticClassOrderIsoIntDual B ≤ asymptoticClassOrderIsoIntDual A)) :
    asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
      asymptoticClassEquivInt A ≤ asymptoticClassEquivInt B :=
  h.2.1

theorem asymptoticClass_orderIsoIntDual_antisymm_of_dominates_equivInt_orderIso_antisymm
    {A B : AsymptoticClass}
    (h : (AsymptoticClass.Dominates A B ∧ AsymptoticClass.Dominates B A) ∧
      (asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
        asymptoticClassEquivInt A ≤ asymptoticClassEquivInt B) ∧
      (asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B ∧
        asymptoticClassOrderIsoIntDual B ≤ asymptoticClassOrderIsoIntDual A)) :
    asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B ∧
      asymptoticClassOrderIsoIntDual B ≤ asymptoticClassOrderIsoIntDual A :=
  h.2.2

theorem asymptoticClass_dominates_equivInt_orderIso_antisymm_of_dominates_antisymm
    {A B : AsymptoticClass}
    (h : AsymptoticClass.Dominates A B ∧ AsymptoticClass.Dominates B A) :
    (AsymptoticClass.Dominates A B ∧ AsymptoticClass.Dominates B A) ∧
      (asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
        asymptoticClassEquivInt A ≤ asymptoticClassEquivInt B) ∧
      (asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B ∧
        asymptoticClassOrderIsoIntDual B ≤ asymptoticClassOrderIsoIntDual A) := by
  refine ⟨h, ?_, ?_⟩
  · exact (asymptoticClass_dominates_antisymm_iff_equivInt_antisymm A B).1 h
  · exact (asymptoticClass_dominates_antisymm_iff_orderIsoIntDual_antisymm A B).1 h

theorem asymptoticClass_dominates_equivInt_orderIso_antisymm_of_equivInt_antisymm
    {A B : AsymptoticClass}
    (h : asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
      asymptoticClassEquivInt A ≤ asymptoticClassEquivInt B) :
    (AsymptoticClass.Dominates A B ∧ AsymptoticClass.Dominates B A) ∧
      (asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
        asymptoticClassEquivInt A ≤ asymptoticClassEquivInt B) ∧
      (asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B ∧
        asymptoticClassOrderIsoIntDual B ≤ asymptoticClassOrderIsoIntDual A) := by
  exact asymptoticClass_dominates_equivInt_orderIso_antisymm_of_dominates_antisymm
    ((asymptoticClass_dominates_antisymm_iff_equivInt_antisymm A B).2 h)

theorem asymptoticClass_dominates_equivInt_orderIso_antisymm_of_orderIsoIntDual_antisymm
    {A B : AsymptoticClass}
    (h : asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B ∧
      asymptoticClassOrderIsoIntDual B ≤ asymptoticClassOrderIsoIntDual A) :
    (AsymptoticClass.Dominates A B ∧ AsymptoticClass.Dominates B A) ∧
      (asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
        asymptoticClassEquivInt A ≤ asymptoticClassEquivInt B) ∧
      (asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B ∧
        asymptoticClassOrderIsoIntDual B ≤ asymptoticClassOrderIsoIntDual A) := by
  exact asymptoticClass_dominates_equivInt_orderIso_antisymm_of_dominates_antisymm
    ((asymptoticClass_dominates_antisymm_iff_orderIsoIntDual_antisymm A B).2 h)

theorem asymptoticClass_eq_iff_orderIsoIntDual_eq (A B : AsymptoticClass) :
    A = B ↔ asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B := by
  constructor
  · intro h
    simp [h]
  · intro h
    apply (asymptoticClass_eq_iff_equivInt_eq A B).2
    exact congrArg (fun x : OrderDual ℤ => (show ℤ from x)) (by
      simpa [asymptoticClassOrderIsoIntDual_apply_eq_equivInt] using h)

theorem asymptoticClass_equivInt_eq_of_valuation_eq {A B : AsymptoticClass}
    (h : AsymptoticClass.valuation A = AsymptoticClass.valuation B) :
    asymptoticClassEquivInt A = asymptoticClassEquivInt B := by
  simpa [asymptoticClassEquivInt] using h

theorem asymptoticClass_valuation_eq_of_equivInt_eq {A B : AsymptoticClass}
    (h : asymptoticClassEquivInt A = asymptoticClassEquivInt B) :
    AsymptoticClass.valuation A = AsymptoticClass.valuation B := by
  simpa [asymptoticClassEquivInt] using h

theorem asymptoticClass_orderIsoIntDual_eq_of_valuation_eq {A B : AsymptoticClass}
    (h : AsymptoticClass.valuation A = AsymptoticClass.valuation B) :
    asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B := by
  exact congrArg (fun x : ℤ => (show OrderDual ℤ from x)) h

theorem asymptoticClass_valuation_eq_of_orderIsoIntDual_eq {A B : AsymptoticClass}
    (h : asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B) :
    AsymptoticClass.valuation A = AsymptoticClass.valuation B := by
  exact congrArg (fun x : OrderDual ℤ => (show ℤ from x)) h

theorem asymptoticClass_equivInt_eq_of_orderIsoIntDual_eq {A B : AsymptoticClass}
    (h : asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B) :
    asymptoticClassEquivInt A = asymptoticClassEquivInt B :=
  asymptoticClass_equivInt_eq_of_valuation_eq
    (asymptoticClass_valuation_eq_of_orderIsoIntDual_eq h)

theorem asymptoticClass_orderIsoIntDual_eq_of_equivInt_eq {A B : AsymptoticClass}
    (h : asymptoticClassEquivInt A = asymptoticClassEquivInt B) :
    asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B :=
  asymptoticClass_orderIsoIntDual_eq_of_valuation_eq
    (asymptoticClass_valuation_eq_of_equivInt_eq h)

theorem asymptoticClass_eq_iff_valuation_equivInt_orderIsoIntDual_eq
    (A B : AsymptoticClass) :
    A = B ↔
      AsymptoticClass.valuation A = AsymptoticClass.valuation B ∧
      asymptoticClassEquivInt A = asymptoticClassEquivInt B ∧
      asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B := by
  constructor
  · intro h
    subst h
    simp
  · intro h
    exact (asymptoticClass_eq_iff_valuation_eq A B).2 h.1

theorem asymptoticClass_valuation_equivInt_orderIsoIntDual_eq_of_eq
    {A B : AsymptoticClass} (h : A = B) :
    AsymptoticClass.valuation A = AsymptoticClass.valuation B ∧
      asymptoticClassEquivInt A = asymptoticClassEquivInt B ∧
      asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B :=
  (asymptoticClass_eq_iff_valuation_equivInt_orderIsoIntDual_eq A B).1 h

theorem asymptoticClass_eq_of_valuation_equivInt_orderIsoIntDual_eq
    {A B : AsymptoticClass}
    (h : AsymptoticClass.valuation A = AsymptoticClass.valuation B ∧
      asymptoticClassEquivInt A = asymptoticClassEquivInt B ∧
      asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B) :
    A = B :=
  (asymptoticClass_eq_iff_valuation_equivInt_orderIsoIntDual_eq A B).2 h

theorem asymptoticClass_valuation_eq_of_valuation_equivInt_orderIsoIntDual_eq
    {A B : AsymptoticClass}
    (h : AsymptoticClass.valuation A = AsymptoticClass.valuation B ∧
      asymptoticClassEquivInt A = asymptoticClassEquivInt B ∧
      asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B) :
    AsymptoticClass.valuation A = AsymptoticClass.valuation B :=
  h.1

theorem asymptoticClass_equivInt_eq_of_valuation_equivInt_orderIsoIntDual_eq
    {A B : AsymptoticClass}
    (h : AsymptoticClass.valuation A = AsymptoticClass.valuation B ∧
      asymptoticClassEquivInt A = asymptoticClassEquivInt B ∧
      asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B) :
    asymptoticClassEquivInt A = asymptoticClassEquivInt B :=
  h.2.1

theorem asymptoticClass_orderIsoIntDual_eq_of_valuation_equivInt_orderIsoIntDual_eq
    {A B : AsymptoticClass}
    (h : AsymptoticClass.valuation A = AsymptoticClass.valuation B ∧
      asymptoticClassEquivInt A = asymptoticClassEquivInt B ∧
      asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B) :
    asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B :=
  h.2.2

theorem asymptoticClass_valuation_equivInt_orderIsoIntDual_eq_of_valuation_eq
    {A B : AsymptoticClass}
    (h : AsymptoticClass.valuation A = AsymptoticClass.valuation B) :
    AsymptoticClass.valuation A = AsymptoticClass.valuation B ∧
      asymptoticClassEquivInt A = asymptoticClassEquivInt B ∧
      asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B := by
  exact ⟨h, asymptoticClass_equivInt_eq_of_valuation_eq h, asymptoticClass_orderIsoIntDual_eq_of_valuation_eq h⟩

theorem asymptoticClass_valuation_equivInt_orderIsoIntDual_eq_of_equivInt_eq
    {A B : AsymptoticClass}
    (h : asymptoticClassEquivInt A = asymptoticClassEquivInt B) :
    AsymptoticClass.valuation A = AsymptoticClass.valuation B ∧
      asymptoticClassEquivInt A = asymptoticClassEquivInt B ∧
      asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B := by
  exact ⟨asymptoticClass_valuation_eq_of_equivInt_eq h, h, asymptoticClass_orderIsoIntDual_eq_of_equivInt_eq h⟩

theorem asymptoticClass_valuation_equivInt_orderIsoIntDual_eq_of_orderIsoIntDual_eq
    {A B : AsymptoticClass}
    (h : asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B) :
    AsymptoticClass.valuation A = AsymptoticClass.valuation B ∧
      asymptoticClassEquivInt A = asymptoticClassEquivInt B ∧
      asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B := by
  exact ⟨asymptoticClass_valuation_eq_of_orderIsoIntDual_eq h, asymptoticClass_equivInt_eq_of_orderIsoIntDual_eq h, h⟩

theorem asymptoticClassEquivInt_injective : Function.Injective asymptoticClassEquivInt :=
  asymptoticClassEquivInt.injective

theorem asymptoticClassOrderIsoIntDual_injective :
    Function.Injective asymptoticClassOrderIsoIntDual :=
  asymptoticClassOrderIsoIntDual.injective

theorem asymptoticClassEquivInt_surjective : Function.Surjective asymptoticClassEquivInt :=
  asymptoticClassEquivInt.surjective

theorem asymptoticClassEquivInt_bijective : Function.Bijective asymptoticClassEquivInt :=
  asymptoticClassEquivInt.bijective

theorem asymptoticClassOrderIsoIntDual_surjective :
    Function.Surjective asymptoticClassOrderIsoIntDual :=
  asymptoticClassOrderIsoIntDual.surjective

theorem asymptoticClassOrderIsoIntDual_bijective :
    Function.Bijective asymptoticClassOrderIsoIntDual :=
  asymptoticClassOrderIsoIntDual.bijective

theorem asymptoticClassOrderIsoIntDual_eq_iff_equivInt_eq (A B : AsymptoticClass) :
    asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B ↔
      asymptoticClassEquivInt A = asymptoticClassEquivInt B := by
  constructor
  · intro h
    exact congrArg (fun x : OrderDual ℤ => (show ℤ from x))
      (by simpa [asymptoticClassOrderIsoIntDual_apply_eq_equivInt] using h)
  · intro h
    simpa [asymptoticClassOrderIsoIntDual_apply_eq_equivInt] using
      congrArg (fun x : ℤ => (show OrderDual ℤ from x)) h

theorem asymptoticClassEquivInt_eq_iff (A B : AsymptoticClass) :
    asymptoticClassEquivInt A = asymptoticClassEquivInt B ↔ A = B := by
  exact (asymptoticClass_eq_iff_equivInt_eq A B).symm

theorem asymptoticClassOrderIsoIntDual_eq_iff (A B : AsymptoticClass) :
    asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B ↔ A = B := by
  exact (asymptoticClass_eq_iff_orderIsoIntDual_eq A B).symm

theorem asymptoticClass_exists_eq_equivInt (e : ℤ) :
    ∃ A : AsymptoticClass, asymptoticClassEquivInt A = e := by
  exact ⟨asymptoticClassEquivInt.symm e, by simp⟩

theorem asymptoticClass_exists_eq_orderIsoIntDual (e : OrderDual ℤ) :
    ∃ A : AsymptoticClass, asymptoticClassOrderIsoIntDual A = e := by
  exact ⟨asymptoticClassOrderIsoIntDual.symm e, by simp⟩

theorem asymptoticClass_existsUnique_equivInt (e : ℤ) :
    ∃! A : AsymptoticClass, asymptoticClassEquivInt A = e := by
  refine ⟨asymptoticClassEquivInt.symm e, by simp, ?_⟩
  intro A hA
  exact asymptoticClassEquivInt.injective (hA.trans (by simp))

theorem asymptoticClass_existsUnique_orderIsoIntDual (e : OrderDual ℤ) :
    ∃! A : AsymptoticClass, asymptoticClassOrderIsoIntDual A = e := by
  refine ⟨asymptoticClassOrderIsoIntDual.symm e, by simp, ?_⟩
  intro A hA
  exact asymptoticClassOrderIsoIntDual.injective (hA.trans (by simp))

/--
Semantics package for transmonomials over a `HyperserialModel`.
`omegaPow` is left as an explicit parameter so we can evolve this
independently from the current surreal `exp/log` pin surface.
-/
structure Semantics (K : Type*) [CommRing K] (M : HyperserialModel K) where
  omegaPow : ℤ → K

/-- Interpret transmonomials in a model using a chosen `omegaPow` handler. -/
def eval {K : Type*} [CommRing K] {M : HyperserialModel K}
    (S : Semantics K M) : Transmonomial → K
  | .one => 1
  | .omegaPow e => S.omegaPow e
  | .exp m => M.exp (eval S m)
  | .log m => M.log (eval S m)

@[simp] theorem eval_one {K : Type*} [CommRing K] {M : HyperserialModel K}
    (S : Semantics K M) : eval S .one = (1 : K) := rfl

@[simp] theorem eval_omegaPow {K : Type*} [CommRing K] {M : HyperserialModel K}
    (S : Semantics K M) (e : ℤ) : eval S (.omegaPow e) = S.omegaPow e := rfl

@[simp] theorem eval_exp {K : Type*} [CommRing K] {M : HyperserialModel K}
    (S : Semantics K M) (m : Transmonomial) :
    eval S (.exp m) = M.exp (eval S m) := rfl

@[simp] theorem eval_log {K : Type*} [CommRing K] {M : HyperserialModel K}
    (S : Semantics K M) (m : Transmonomial) :
    eval S (.log m) = M.log (eval S m) := rfl

/-- Iterate model `exp` in value-space. -/
def evalIterExp {K : Type*} [CommRing K] (M : HyperserialModel K) : ℕ → K → K
  | 0, x => x
  | n + 1, x => M.exp (evalIterExp M n x)

/-- Iterate model `log` in value-space. -/
def evalIterLog {K : Type*} [CommRing K] (M : HyperserialModel K) : ℕ → K → K
  | 0, x => x
  | n + 1, x => M.log (evalIterLog M n x)

@[simp] theorem evalIterExp_zero {K : Type*} [CommRing K] (M : HyperserialModel K) (x : K) :
    evalIterExp M 0 x = x := rfl

@[simp] theorem evalIterExp_succ {K : Type*} [CommRing K] (M : HyperserialModel K) (n : ℕ) (x : K) :
    evalIterExp M (n + 1) x = M.exp (evalIterExp M n x) := rfl

@[simp] theorem evalIterLog_zero {K : Type*} [CommRing K] (M : HyperserialModel K) (x : K) :
    evalIterLog M 0 x = x := rfl

@[simp] theorem evalIterLog_succ {K : Type*} [CommRing K] (M : HyperserialModel K) (n : ℕ) (x : K) :
    evalIterLog M (n + 1) x = M.log (evalIterLog M n x) := rfl

theorem eval_iterExp {K : Type*} [CommRing K] {M : HyperserialModel K}
    (S : Semantics K M) (n : ℕ) (m : Transmonomial) :
    eval S (Transmonomial.iterExp n m) = evalIterExp M n (eval S m) := by
  induction n generalizing m with
  | zero =>
      simp [Transmonomial.iterExp, evalIterExp]
  | succ n ih =>
      simp [Transmonomial.iterExp, evalIterExp, ih]

theorem eval_iterLog {K : Type*} [CommRing K] {M : HyperserialModel K}
    (S : Semantics K M) (n : ℕ) (m : Transmonomial) :
    eval S (Transmonomial.iterLog n m) = evalIterLog M n (eval S m) := by
  induction n generalizing m with
  | zero =>
      simp [Transmonomial.iterLog, evalIterLog]
  | succ n ih =>
      simp [Transmonomial.iterLog, evalIterLog, ih]

section Laws

variable {K : Type*} [CommRing K] {M : HyperserialModel K} [HyperserialModelLaws K M]

theorem eval_exp_log (S : Semantics K M) (m : Transmonomial) :
    eval S (.exp (.log m)) = eval S m := by
  simp [eval, Hyperseries.exp_log (M := M)]

theorem eval_log_exp (S : Semantics K M) (m : Transmonomial) :
    eval S (.log (.exp m)) = eval S m := by
  simp [eval, Hyperseries.log_exp (M := M)]

omit [HyperserialModelLaws K M] in
theorem evalIterExp_eq_iterate (n : ℕ) (x : K) :
    evalIterExp M n x = (M.exp^[n]) x := by
  induction n generalizing x with
  | zero =>
      rfl
  | succ n ih =>
      simp [evalIterExp, Function.iterate_succ_apply', ih]

omit [HyperserialModelLaws K M] in
theorem evalIterLog_eq_iterate (n : ℕ) (x : K) :
    evalIterLog M n x = (M.log^[n]) x := by
  induction n generalizing x with
  | zero =>
      rfl
  | succ n ih =>
      simp [evalIterLog, Function.iterate_succ_apply', ih]

theorem evalIterExp_evalIterLog (n : ℕ) (x : K) :
    evalIterExp M n (evalIterLog M n x) = x := by
  have hLeft : Function.LeftInverse M.exp M.log := by
    intro y
    exact Hyperseries.exp_log (M := M) y
  have hIter := Function.LeftInverse.iterate hLeft n
  calc
    evalIterExp M n (evalIterLog M n x) = (M.exp^[n]) ((M.log^[n]) x) := by
      simp [evalIterExp_eq_iterate, evalIterLog_eq_iterate]
    _ = x := hIter x

theorem evalIterLog_evalIterExp (n : ℕ) (x : K) :
    evalIterLog M n (evalIterExp M n x) = x := by
  have hLeft : Function.LeftInverse M.log M.exp := by
    intro y
    exact Hyperseries.log_exp (M := M) y
  have hIter := Function.LeftInverse.iterate hLeft n
  calc
    evalIterLog M n (evalIterExp M n x) = (M.log^[n]) ((M.exp^[n]) x) := by
      simp [evalIterExp_eq_iterate, evalIterLog_eq_iterate]
    _ = x := hIter x

theorem eval_iterExp_iterLog (S : Semantics K M) (n : ℕ) (m : Transmonomial) :
    eval S (Transmonomial.iterExp n (Transmonomial.iterLog n m)) = eval S m := by
  calc
    eval S (Transmonomial.iterExp n (Transmonomial.iterLog n m))
        = evalIterExp M n (eval S (Transmonomial.iterLog n m)) := by
          simpa using eval_iterExp S n (Transmonomial.iterLog n m)
    _ = evalIterExp M n (evalIterLog M n (eval S m)) := by
          simp [eval_iterLog]
    _ = eval S m := by
          simpa using evalIterExp_evalIterLog (M := M) n (eval S m)

theorem eval_iterLog_iterExp (S : Semantics K M) (n : ℕ) (m : Transmonomial) :
    eval S (Transmonomial.iterLog n (Transmonomial.iterExp n m)) = eval S m := by
  calc
    eval S (Transmonomial.iterLog n (Transmonomial.iterExp n m))
        = evalIterLog M n (eval S (Transmonomial.iterExp n m)) := by
          simpa using eval_iterLog S n (Transmonomial.iterExp n m)
    _ = evalIterLog M n (evalIterExp M n (eval S m)) := by
          simp [eval_iterExp]
    _ = eval S m := by
          simpa using evalIterLog_evalIterExp (M := M) n (eval S m)

end Laws

/--
Staged compatibility property: adjacent tower constructors preserve valuation.
This captures exp/log cancellation behavior at the valuation layer.
-/
def valuationStableUnderExpLog (m : Transmonomial) : Prop :=
  valuation (.exp (.log m)) = valuation m ∧ valuation (.log (.exp m)) = valuation m

theorem valuationStableUnderExpLog_all (m : Transmonomial) :
    valuationStableUnderExpLog m := by
  constructor <;> simp [valuation]

end Transmonomial

noncomputable section

open Transmonomial

/-- Default staged semantics package for `Surreal` under the current model. -/
noncomputable def surrealTransmonomialSemantics : Transmonomial.Semantics Surreal surrealModel where
  omegaPow := fun e => (e : Surreal)

/-- Build transmonomial semantics from a packaged surreal exp/log semantics. -/
noncomputable def ofSurrealExpLog
    (S : SurrealExpLogSemantics) :
    Transmonomial.Semantics Surreal (SurrealExpLogSemantics.toModel S) where
  omegaPow := fun e => (e : Surreal)

@[simp] theorem surreal_eval_omegaPow (e : ℤ) :
    Transmonomial.eval surrealTransmonomialSemantics (.omegaPow e) = (e : Surreal) := rfl

@[simp] theorem eval_ofSurrealExpLog_omegaPow (S : SurrealExpLogSemantics) (e : ℤ) :
    Transmonomial.eval (ofSurrealExpLog S) (.omegaPow e) = (e : Surreal) := rfl

end

end Hyperseries
end HeytingLean
