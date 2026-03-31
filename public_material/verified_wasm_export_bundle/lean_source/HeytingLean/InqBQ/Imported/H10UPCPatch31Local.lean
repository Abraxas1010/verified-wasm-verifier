-- AUTO-GENERATED HIR v2 -> Lean translation (tool-run)
-- Translator: scripts/hir_v2_to_lean.py
-- Source: /tmp/h10upc_compl_closure_project_export_4142.json
-- Mode: strict
-- Namespace: TranslationKernelV2
-- GeneratedAt: 2026-03-26T18:32:13.380850+00:00
-- DO NOT EDIT MANUALLY: re-run translator to update.

import Mathlib.Logic.Encodable.Basic
import HeytingLean.InqBQ.H10UPCComputability

set_option linter.unusedVariables false

namespace TranslationKernelV2

universe u v w

def pointwise_relation {A : Sort u} {B : Sort v} (R : B -> B -> Prop) : (A -> B) -> (A -> B) -> Prop :=
  fun f g => ∀ x, R (f x) (g x)

def respectful {A : Sort u} {B : Sort v} (R : A -> A -> Prop) (S : B -> B -> Prop) : (A -> B) -> (A -> B) -> Prop :=
  fun f g => ∀ ⦃x y⦄, R x y -> S (f x) (g y)

def impl (P Q : Prop) : Prop := P → Q

def flip {A : Sort u} {B : Sort v} {C : Sort w} (f : A -> B -> C) (b : B) (a : A) : C := f a b

def all (A : Type u) (P : A -> Prop) : Prop := ∀ x, P x

inductive ex (A : Type u) (P : A -> Prop) : Prop where
  | intro : (x : A) -> P x -> ex A P

def ex.ex_intro (A : Type u) (P : A -> Prop) (x : A) (h : P x) : ex A P :=
  ex.intro x h

def option_map (A : Type u) (B : Type v) (f : A -> B) : Option A -> Option B
  | some x => some (f x)
  | none => none

theorem eq_proper_proxy (A : Type u) (x : A) : Eq x x := rfl

theorem subrelation_refl {A : Type u} (R : A -> A -> Prop) :
    (∀ ⦃x y : A⦄, R x y -> R x y) := by
  intro x y h
  exact h

theorem trans_co_eq_inv_impl_morphism {A : Type} {R : A -> A -> Prop}
    (H : ∀ {x y z : A}, R x y -> R y z -> R x z) :
    respectful R (respectful (Eq) (flip impl)) R R := by
  intro x y hxy z w hEq hyw
  subst hEq
  exact H hxy hyw

theorem subrelation_respectful {A : Type u} {B : Type v}
    {RA' RA : A -> A -> Prop} (subl : ∀ ⦃x y : A⦄, RA' x y -> RA x y)
    {RB RB' : B -> B -> Prop} (subr : ∀ ⦃x y : B⦄, RB x y -> RB' x y) :
    ∀ ⦃f g : A -> B⦄, respectful RA RB f g -> respectful RA' RB' f g := by
  intro f g hfg x y hxy
  exact subr (hfg (subl hxy))

theorem subrelation_proper {A : Type u} {R' : A -> A -> Prop} {m : A}
    (mor : R' m m) {R : A -> A -> Prop} (_unc : True)
    (sub : ∀ ⦃x y : A⦄, R' x y -> R x y) : R m m := by
  exact sub mor

def and_ind (A B P : Prop) (f : A -> B -> P) : And A B -> P
  | And.intro hA hB => f hA hB


def all_iff_morphism (A : Type) (P Q : A -> Prop) (h : ∀ x, P x ↔ Q x) :
    all A P ↔ all A Q := by
  constructor
  · intro hP x
    exact (h x).1 (hP x)
  · intro hQ x
    exact (h x).2 (hQ x)

def ex_iff_morphism (A : Type) (P Q : A -> Prop) (h : ∀ x, P x ↔ Q x) :
    ex A P ↔ ex A Q := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (h x).1 hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (h x).2 hx⟩

structure PER (A : Type) (R : A -> A -> Prop) : Prop where
  PER_Symmetric : ∀ {x : A} {y : A}, R x y -> R y x
  PER_Transitive : ∀ {x : A} {y : A} {z : A}, R x y -> R y z -> R x z

structure Equivalence (A : Type) (R : A -> A -> Prop) : Prop where
  Equivalence_Reflexive : ∀ x : A, R x x
  Equivalence_Symmetric : ∀ {x : A} {y : A}, R x y -> R y x
  Equivalence_Transitive : ∀ {x : A} {y : A} {z : A}, R x y -> R y z -> R x z

inductive positive : Type where
  | xI : positive -> positive
  | xO : positive -> positive
  | xH

inductive N : Type where
  | N0
  | Npos : positive -> N

inductive Z : Type where
  | Z0
  | Zpos : positive -> Z
  | Zneg : positive -> Z

inductive sig (A : Type u) (P : A -> Prop) : Type u where
  | exist : (x : A) -> P x -> sig A P

inductive sigT (A : Type u) (P : A -> Type v) : Type (max u v) where
  | existT : (x : A) -> P x -> sigT A P

inductive t_1 : Nat -> Type where
  | F1 : {n : Nat} -> t_1 (Nat.succ n)
  | FS : {n : Nat} -> t_1 n -> t_1 (Nat.succ n)

inductive VarMap_t (A : Type) : Type where
  | Empty
  | Elt : A -> VarMap_t A
  | Branch : VarMap_t A -> A -> VarMap_t A -> VarMap_t A

inductive PExpr (C : Type) : Type where
  | PEc : C -> PExpr C
  | PEX : positive -> PExpr C
  | PEadd : PExpr C -> PExpr C -> PExpr C
  | PEsub : PExpr C -> PExpr C -> PExpr C
  | PEmul : PExpr C -> PExpr C -> PExpr C
  | PEopp : PExpr C -> PExpr C
  | PEpow : PExpr C -> N -> PExpr C

inductive PolC (C : Type) : Type where
  | Pc : C -> PolC C
  | Pinj : positive -> PolC C -> PolC C
  | PX : PolC C -> positive -> PolC C -> PolC C

inductive Op2 : Type where
  | OpEq
  | OpNEq
  | OpLe
  | OpGe
  | OpLt
  | OpGt

inductive Formula (T : Type) : Type where
  | Build_Formula : PExpr T -> Op2 -> PExpr T -> Formula T

inductive ZArithProof : Type where
  | DoneProof
  | RatProof : ZWitness -> ZArithProof -> ZArithProof
  | CutProof : ZWitness -> ZArithProof -> ZArithProof
  | SplitProof : PolC Z -> ZArithProof -> ZArithProof -> ZArithProof
  | EnumProof : ZWitness -> ZWitness -> List ZArithProof -> ZArithProof
  | ExProof : positive -> ZArithProof -> ZArithProof

inductive t (A : Type) : Nat -> Type where
  | nil : t A Nat.zero
  | cons : A -> (n : Nat) -> t A n -> t A (Nat.succ n)

inductive direction : Type where
  | go_left
  | go_right

structure SBTM : Type 2 where
  num_states : Nat
  trans : t (Prod (Option (Prod (Prod (t_1 num_states) Bool) direction)) (Option (Prod (Prod (t_1 num_states) Bool) direction))) num_states

inductive dio_op : Type where
  | do_add
  | do_mul

inductive dio_formula : Type where
  | df_cst : Nat -> Nat -> dio_formula
  | df_eq : Nat -> Nat -> dio_formula
  | df_op : dio_op -> Nat -> Nat -> Nat -> dio_formula
  | df_bin : dio_op -> dio_formula -> dio_formula -> dio_formula
  | df_exst : dio_formula -> dio_formula

theorem Equivalence_PER {A : Type} {R : A -> A -> Prop} (E : Equivalence A R) : PER A R := by
  refine PER.mk ?_ ?_
  · intro x y hxy
    exact E.Equivalence_Symmetric hxy
  · intro x y z hxy hyz
    exact E.Equivalence_Transitive hxy hyz

def iff_equivalence : Equivalence Prop Iff := by
  refine Equivalence.mk ?_ ?_ ?_
  · intro P
    exact Iff.rfl
  · intro P Q h
    exact Iff.symm h
  · intro P Q R hPQ hQR
    exact Iff.trans hPQ hQR

theorem iff_flip_impl_subrelation : (∀ ⦃x y : Prop⦄, (x ↔ y) -> flip impl x y) := by
  intro x y h hy
  exact h.mpr hy

theorem per_partial_app_morphism {A : Type} {R : A -> A -> Prop}
    (H : PER A R) (x : A) : respectful R Iff (R x) (R x) := by
  intro y z hyz
  constructor
  · intro hxy
    exact H.PER_Transitive hxy hyz
  · intro hxz
    exact H.PER_Transitive hxz (H.PER_Symmetric hyz)

def de_op_sem : dio_op -> Nat -> Nat -> Nat
  | dio_op.do_add => Nat.add
  | dio_op.do_mul => Nat.mul

inductive dio_elem_expr : Type where
  | dee_nat : Nat -> dio_elem_expr
  | dee_var : Nat -> dio_elem_expr
  | dee_par : Nat -> dio_elem_expr
  | dee_comp : dio_op -> Nat -> Nat -> dio_elem_expr

def dee_eval (__ : Nat -> Nat) (___1 : Nat -> Nat) : dio_elem_expr -> Nat
  | dio_elem_expr.dee_nat n => n
  | dio_elem_expr.dee_var v => __ v
  | dio_elem_expr.dee_par i => ___1 i
  | dio_elem_expr.dee_comp o v w => de_op_sem o (__ v) (__ w)

def df_op_sem : dio_op -> Prop -> Prop -> Prop
  | dio_op.do_add => Or
  | dio_op.do_mul => And

def df_pred : dio_formula -> (Nat -> Nat) -> Prop
  | dio_formula.df_cst x n => fun ν => ν x = n
  | dio_formula.df_eq x y => fun ν => ν x = ν y
  | dio_formula.df_op o x y z => fun ν => ν x = de_op_sem o (ν y) (ν z)
  | dio_formula.df_bin o f g => fun ν => df_op_sem o (df_pred f ν) (df_pred g ν)
  | dio_formula.df_exst f => fun ν =>
      ex Nat (fun n => df_pred f (fun k => match k with | Nat.zero => n | Nat.succ k' => ν k'))

def enumerator (X : Type u) (f : Nat -> Option X) (P : X -> Prop) : Prop :=
  ∀ x, P x ↔ ∃ n, f n = some x

def enumerator__T' (X : Type u) (f : Nat -> Option X) : Prop :=
  ∀ x : X, ex Nat (fun n => f n = some x)

def enumerable (X : Type u) (P : X -> Prop) : Prop :=
  ex (Nat -> Option X) (fun f => enumerator X f P)

def decidable (X : Type u) (P : X -> Prop) : Prop :=
  ex (X -> Bool) (fun f => ∀ x : X, Iff (P x) (Eq (α := Bool) (f x) Bool.true))

def semi_decidable (X : Type u) (P : X -> Prop) : Prop :=
  ex (X -> Nat -> Bool) (fun f => ∀ x : X, Iff (P x) (ex Nat (fun n => Eq (α := Bool) (f x n) Bool.true)))

def nat_enum (n : Nat) : Option Nat := some n

def bool_enum : Nat -> Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

theorem enumerator__T_nat : enumerator__T' Nat nat_enum := by
  exact fun n => ex.ex_intro Nat (fun m => nat_enum m = some n) n rfl

theorem enumerator__T_bool : enumerator__T' Bool bool_enum := by
  intro b
  cases b with
  | false => exact ex.ex_intro Nat (fun n => bool_enum n = some false) 0 rfl
  | true => exact ex.ex_intro Nat (fun n => bool_enum n = some true) 1 rfl

def all_fins : (n : Nat) -> List (t_1 n)
  | 0 => []
  | n + 1 => t_1.F1 :: (all_fins n).map t_1.FS

def Fin_enum (k : Nat) (n : Nat) : Option (t_1 k) :=
  (all_fins k).get? n

def fin_encode : ∀ {k : Nat}, t_1 k -> Nat
  | _, t_1.F1 => 0
  | _, t_1.FS x => fin_encode x + 1

theorem fin_encode_spec : ∀ {k : Nat} (x : t_1 k), Fin_enum k (fin_encode x) = some x := by
  intro k x
  induction x with
  | F1 =>
      simp [fin_encode, Fin_enum, all_fins]
  | FS x ih =>
      simpa [fin_encode, Fin_enum, all_fins] using congrArg (Option.map t_1.FS) ih

theorem enumerator__T_Fin (k : Nat) : enumerator__T' (t_1 k) (Fin_enum k) := by
  intro x
  exact ex.ex_intro Nat (fun n => Fin_enum k n = some x) (fin_encode x) (fin_encode_spec x)

def direction_enum : Nat -> Option direction
  | 0 => some direction.go_left
  | 1 => some direction.go_right
  | _ => none

theorem enumerator__T_direction : enumerator__T' direction direction_enum := by
  intro d
  cases d with
  | go_left =>
      exact ex.ex_intro Nat (fun n => direction_enum n = some direction.go_left) 0 rfl
  | go_right =>
      exact ex.ex_intro Nat (fun n => direction_enum n = some direction.go_right) 1 rfl

def direction_enumeration : sig (Nat -> Option direction) (fun e => enumerator__T' direction e) :=
  sig.exist direction_enum enumerator__T_direction

def prod_enum (X : Type u) (Y : Type v) (f1 : Nat -> Option X) (f2 : Nat -> Option Y) (n : Nat) : Option (Prod X Y) :=
  let p := Nat.unpair n
  match f1 p.1, f2 p.2 with
  | some x, some y => some (x, y)
  | _, _ => none

theorem enumerator__T_prod {X : Type u} {Y : Type v} (f1 : Nat -> Option X) (f2 : Nat -> Option Y)
    (H1 : enumerator__T' X f1) (H2 : enumerator__T' Y f2) :
    enumerator__T' (Prod X Y) (prod_enum X Y f1 f2) := by
  intro xy
  rcases H1 xy.1 with ⟨n1, hn1⟩
  rcases H2 xy.2 with ⟨n2, hn2⟩
  refine ex.ex_intro Nat (fun n => prod_enum X Y f1 f2 n = some xy) (Nat.pair n1 n2) ?_
  simp [prod_enum, hn1, hn2, Nat.unpair_pair]

def option_enum (X : Type u) (f : Nat -> Option X) : Nat -> Option (Option X)
  | 0 => some none
  | n + 1 => some (f n)

theorem enumerator__T_option {X : Type u} (f : Nat -> Option X)
    (H : enumerator__T' X f) : enumerator__T' (Option X) (option_enum X f) := by
  intro ox
  cases ox with
  | none =>
      exact ex.ex_intro Nat (fun n => option_enum X f n = some none) 0 rfl
  | some x =>
      rcases H x with ⟨n, hn⟩
      refine ex.ex_intro Nat (fun m => option_enum X f m = some (some x)) (n + 1) ?_
      simpa [option_enum] using hn

def Vector_enum (X : Type) : (k : Nat) -> (Nat -> Option X) -> Nat -> Option (t X k)
  | 0, _f, _n => some t.nil
  | k + 1, f, n =>
      let p := Nat.unpair n
      match f p.1, Vector_enum X k f p.2 with
      | some x, some v => some (t.cons x k v)
      | _, _ => none

theorem enumerator__T_Vector {X : Type} {k : Nat} (f : Nat -> Option X)
    (Hf : enumerator__T' X f) : enumerator__T' (t X k) (Vector_enum X k f) := by
  induction k with
  | zero =>
      exact fun v => by
        cases v
        exact ex.ex_intro Nat (fun n => Vector_enum X 0 f n = some t.nil) 0 rfl
  | succ k ih =>
      intro v
      cases v with
      | cons x _ xs =>
          rcases Hf x with ⟨nx, hnx⟩
          rcases ih xs with ⟨m, hm⟩
          refine ex.ex_intro Nat (fun n => Vector_enum X (Nat.succ k) f n = some (t.cons x k xs)) (Nat.pair nx m) ?_
          simp [Vector_enum, hnx, hm, Nat.unpair_pair]

def sigT_enum (X : Type u) (P : X -> Type v)
    (f : Nat -> Option X) (fP : ∀ x, Nat -> Option (P x)) (n : Nat) :
    Option (sigT X P) :=
  let q := Nat.unpair n
  match f q.1 with
  | some x =>
      match fP x q.2 with
      | some y => some (sigT.existT x y)
      | none => none
  | none => none

theorem enumerator__T_sigT {X : Type u} {P : X -> Type v}
    (f : Nat -> Option X) (fP : ∀ x, Nat -> Option (P x))
    (Hf : enumerator__T' X f) (HfP : ∀ x, enumerator__T' (P x) (fP x)) :
    enumerator__T' (sigT X P) (sigT_enum X P f fP) := by
  intro xp
  cases xp with
  | existT x px =>
      rcases Hf x with ⟨nx, hnx⟩
      rcases HfP x px with ⟨nP, hnP⟩
      refine ex.ex_intro Nat
        (fun n => sigT_enum X P f fP n = some (sigT.existT x px))
        (Nat.pair nx nP) ?_
      simp [sigT_enum, hnx, hnP, Nat.unpair_pair]

theorem decidable_semi_decidable {X : Type} {p : X -> Prop}
    (H : decidable X p) : semi_decidable X p := by
  rcases H with ⟨d, hd⟩
  refine ⟨fun x _ => d x, ?_⟩
  intro x
  constructor
  · intro hp
    refine ex.ex_intro Nat (fun n => Eq (α := Bool) (d x) Bool.true) 0 ?_
    simpa using (hd x).1 hp
  · rintro ⟨n, hn⟩
    exact (hd x).2 hn

theorem semi_decidable_enumerable {X : Type} {p : X -> Prop}
    (HX : ((fun (X : Type) => ex (Nat -> Option X) (fun (f : Nat -> Option X) => enumerator__T' X f)) X))
    (Hp : semi_decidable X p) : enumerable X p := by
  rcases HX with ⟨e, He⟩
  rcases Hp with ⟨f, Hf⟩
  let g : Nat -> Option X := fun n =>
    let q := Nat.unpair n
    match e q.1 with
    | some x => if f x q.2 = Bool.true then some x else none
    | none => none
  refine ex.ex_intro (Nat -> Option X) (fun h => enumerator X h p) g ?_
  intro x
  constructor
  · intro hx
    rcases He x with ⟨m, hm⟩
    rcases (Hf x).1 hx with ⟨n, hn⟩
    exact Exists.intro (Nat.pair m n) (by
      simp [g, hm, hn, Nat.unpair_pair])
  · rintro ⟨n, hn⟩
    let q := Nat.unpair n
    cases hE : e q.1 with
    | none =>
        simp [g, q, hE] at hn
    | some y =>
        by_cases hfy : f y q.2 = Bool.true
        · simp [g, q, hE, hfy] at hn
          have hxy : y = x := by simpa using hn
          subst hxy
          exact (Hf y).2 (ex.ex_intro Nat (fun k => Eq (α := Bool) (f y k) Bool.true) q.2 hfy)
        · simp [g, q, hE, hfy] at hn

theorem dec_count_enum {X : Type} {p : X -> Prop}
    (Hdec : decidable X p)
    (HX : ((fun (X : Type) => ex (Nat -> Option X) (fun (f : Nat -> Option X) => enumerator__T' X f)) X)) :
    enumerable X p := by
  exact semi_decidable_enumerable HX (decidable_semi_decidable Hdec)

theorem enumerator_enumerable {X : Type} (f : Nat -> Option X)
    (H : enumerator__T' X f) :
    ((fun (X : Type) => ex (Nat -> Option X) (fun (g : Nat -> Option X) => enumerator__T' X g)) X) := by
  exact ex.ex_intro (Nat -> Option X) (fun g => enumerator__T' X g) f H

abbrev SBTMTrans (n : Nat) : Type :=
  t (Prod (Option (Prod (Prod (t_1 n) Bool) direction)) (Option (Prod (Prod (t_1 n) Bool) direction))) n

def SBTM_to_sigT (M : SBTM) : sigT Nat SBTMTrans :=
  sigT.existT M.num_states M.trans

def SBTM_of_sigT : sigT Nat SBTMTrans -> SBTM
  | sigT.existT n tr => SBTM.mk n tr

theorem SBTM_of_sigT_to_sigT (M : SBTM) : SBTM_of_sigT (SBTM_to_sigT M) = M := by
  cases M
  rfl

def SBTMInstrEnum (n : Nat) : Nat -> Option (Prod (Prod (t_1 n) Bool) direction) :=
  prod_enum (Prod (t_1 n) Bool) direction
    (prod_enum (t_1 n) Bool (Fin_enum n) bool_enum)
    direction_enum

theorem enumerator__T_SBTMInstr (n : Nat) :
    enumerator__T' (Prod (Prod (t_1 n) Bool) direction) (SBTMInstrEnum n) := by
  exact
    @enumerator__T_prod (Prod (t_1 n) Bool) direction
      (prod_enum (t_1 n) Bool (Fin_enum n) bool_enum)
      direction_enum
      (@enumerator__T_prod (t_1 n) Bool (Fin_enum n) bool_enum (enumerator__T_Fin n) enumerator__T_bool)
      enumerator__T_direction

def SBTMCellEnum (n : Nat) : Nat -> Option (Option (Prod (Prod (t_1 n) Bool) direction)) :=
  option_enum (Prod (Prod (t_1 n) Bool) direction) (SBTMInstrEnum n)

theorem enumerator__T_SBTMCell (n : Nat) :
    enumerator__T' (Option (Prod (Prod (t_1 n) Bool) direction)) (SBTMCellEnum n) := by
  exact @enumerator__T_option (Prod (Prod (t_1 n) Bool) direction) (SBTMInstrEnum n) (enumerator__T_SBTMInstr n)

def SBTMTransitionEnum (n : Nat) : Nat -> Option (SBTMTrans n) :=
  Vector_enum
    (Prod (Option (Prod (Prod (t_1 n) Bool) direction)) (Option (Prod (Prod (t_1 n) Bool) direction)))
    n
    (prod_enum
      (Option (Prod (Prod (t_1 n) Bool) direction))
      (Option (Prod (Prod (t_1 n) Bool) direction))
      (SBTMCellEnum n)
      (SBTMCellEnum n))

theorem enumerator__T_SBTMTransition (n : Nat) :
    enumerator__T' (SBTMTrans n) (SBTMTransitionEnum n) := by
  exact
    @enumerator__T_Vector
      (Prod (Option (Prod (Prod (t_1 n) Bool) direction)) (Option (Prod (Prod (t_1 n) Bool) direction)))
      n
      (prod_enum
        (Option (Prod (Prod (t_1 n) Bool) direction))
        (Option (Prod (Prod (t_1 n) Bool) direction))
        (SBTMCellEnum n)
        (SBTMCellEnum n))
      (@enumerator__T_prod
        (Option (Prod (Prod (t_1 n) Bool) direction))
        (Option (Prod (Prod (t_1 n) Bool) direction))
        (SBTMCellEnum n)
        (SBTMCellEnum n)
        (enumerator__T_SBTMCell n)
        (enumerator__T_SBTMCell n))

def SBTMSigEnum : Nat -> Option (sigT Nat SBTMTrans) :=
  sigT_enum Nat SBTMTrans nat_enum SBTMTransitionEnum

theorem enumerator__T_SBTMSig : enumerator__T' (sigT Nat SBTMTrans) SBTMSigEnum := by
  exact enumerator__T_sigT nat_enum SBTMTransitionEnum enumerator__T_nat enumerator__T_SBTMTransition

def SBTM_enum : Nat -> Option SBTM := fun n => Option.map SBTM_of_sigT (SBTMSigEnum n)

theorem enumerator__T_SBTM : enumerator__T' SBTM SBTM_enum := by
  intro M
  rcases enumerator__T_SBTMSig (SBTM_to_sigT M) with ⟨n, hn⟩
  exact ex.ex_intro Nat (fun k => SBTM_enum k = some M) n (by
    simpa [SBTM_enum, SBTM_of_sigT_to_sigT] using congrArg (Option.map SBTM_of_sigT) hn)

def SBTM_enumeration : sig (Nat -> Option SBTM) (fun e => enumerator__T' SBTM e) :=
  sig.exist SBTM_enum enumerator__T_SBTM

def dc_eval (__ : Nat -> Nat) (___1 : Nat -> Nat) (c : Prod Nat dio_elem_expr) : Prop :=
  __ c.1 = dee_eval __ ___1 c.2

inductive h10c : Type where
  | h10c_one : (∀ (x : Nat), h10c)
  | h10c_plus : (∀ (x : Nat), (∀ (x_1 : Nat), (∀ (x_2 : Nat), h10c)))
  | h10c_mult : (∀ (x : Nat), (∀ (x_1 : Nat), (∀ (x_2 : Nat), h10c)))

inductive h10sqc : Type where
  | h10sqc_one : (∀ (x : Nat), h10sqc)
  | h10sqc_plus : (∀ (x : Nat), (∀ (x_1 : Nat), (∀ (x_2 : Nat), h10sqc)))
  | h10sqc_sq : (∀ (x : Nat), (∀ (x_1 : Nat), h10sqc))

inductive bsm_instr (n : Nat) : Type where
  | bsm_pop : (∀ (x : (t_1 n)), (∀ (x_1 : Nat), (∀ (x_2 : Nat), (bsm_instr n))))
  | bsm_push : (∀ (x : (t_1 n)), (∀ (x_1 : Bool), (bsm_instr n)))

def out_code {X : Type} (i : Nat) (P : Prod Nat (List X)) : Prop :=
  i < P.1 ∨ P.1 + List.length P.2 <= i

def sss_step (instr : Type) (data : Type)
    (one_step : instr -> Prod Nat data -> Prod Nat data -> Prop)
    (P : Prod Nat (List instr)) (st1 st2 : Prod Nat data) : Prop :=
  ex Nat (fun k =>
    ex (List instr) (fun l =>
      ex instr (fun i =>
        ex (List instr) (fun r =>
          ex data (fun d =>
            P = (k, l ++ i :: r) ∧ st1 = (k + List.length l, d) ∧ one_step i st1 st2)))))

inductive sss_steps (instr : Type) (data : Type)
    (one_step : instr -> Prod Nat data -> Prod Nat data -> Prop)
    (P : Prod Nat (List instr)) : Nat -> Prod Nat data -> Prod Nat data -> Prop where
  | zero (st : Prod Nat data) : sss_steps instr data one_step P 0 st st
  | succ (n : Nat) (st1 st2 st3 : Prod Nat data) :
      sss_step instr data one_step P st1 st2 ->
      sss_steps instr data one_step P n st2 st3 ->
      sss_steps instr data one_step P (Nat.succ n) st1 st3

def sss_compute (instr : Type) (data : Type)
    (one_step : instr -> Prod Nat data -> Prod Nat data -> Prop)
    (P : Prod Nat (List instr)) (st1 st2 : Prod Nat data) : Prop :=
  ex Nat (fun k => sss_steps instr data one_step P k st1 st2)

def sss_output (instr : Type) (data : Type)
    (one_step : instr -> Prod Nat data -> Prod Nat data -> Prop)
    (P : Prod Nat (List instr)) (st st' : Prod Nat data) : Prop :=
  sss_compute instr data one_step P st st' ∧ out_code st'.1 P

def sss_terminates (instr : Type) (data : Type)
    (one_step : instr -> Prod Nat data -> Prod Nat data -> Prop)
    (P : Prod Nat (List instr)) (st : Prod Nat data) : Prop :=
  ex (Prod Nat data) (fun st' => sss_output instr data one_step P st st')

def vec_get {A : Type} : ∀ {n : Nat}, t A n -> t_1 n -> A
  | _, t.cons x _ _, t_1.F1 => x
  | _, t.cons _ _ xs, t_1.FS i => vec_get xs i

def vec_set {A : Type} : ∀ {n : Nat}, t A n -> t_1 n -> A -> t A n
  | _, t.cons _ k xs, t_1.F1, a => t.cons a k xs
  | _, t.cons x k xs, t_1.FS i, a => t.cons x k (vec_set xs i a)

abbrev bsm_state (n : Nat) : Type := Prod Nat (t (List Bool) n)

inductive bsm_sss (n : Nat) : bsm_instr n -> bsm_state n -> bsm_state n -> Prop where
  | pop_empty (i : Nat) (x : t_1 n) (p q : Nat) (v : t (List Bool) n) :
      vec_get v x = [] ->
      bsm_sss n (bsm_instr.bsm_pop x p q) (Prod.mk (α := Nat) (β := t (List Bool) n) i v)
        (Prod.mk (α := Nat) (β := t (List Bool) n) q v)
  | pop_false (i : Nat) (x : t_1 n) (p q : Nat) (v : t (List Bool) n) (ll : List Bool) :
      vec_get v x = Bool.false :: ll ->
      bsm_sss n (bsm_instr.bsm_pop x p q) (Prod.mk (α := Nat) (β := t (List Bool) n) i v)
        (Prod.mk (α := Nat) (β := t (List Bool) n) p (vec_set v x ll))
  | pop_true (i : Nat) (x : t_1 n) (p q : Nat) (v : t (List Bool) n) (ll : List Bool) :
      vec_get v x = Bool.true :: ll ->
      bsm_sss n (bsm_instr.bsm_pop x p q) (Prod.mk (α := Nat) (β := t (List Bool) n) i v)
        (Prod.mk (α := Nat) (β := t (List Bool) n) (Nat.succ i) (vec_set v x ll))
  | push (i : Nat) (x : t_1 n) (b : Bool) (v : t (List Bool) n) :
      bsm_sss n (bsm_instr.bsm_push x b) (Prod.mk (α := Nat) (β := t (List Bool) n) i v)
        (Prod.mk (α := Nat) (β := t (List Bool) n) (Nat.succ i) (vec_set v x (b :: vec_get v x)))

def BSM_PROBLEM : Type :=
  sigT Nat (fun n => sigT Nat (fun i => sigT (List (bsm_instr n)) (fun _ => t (List Bool) n)))

def eval (n : Nat) (P : Prod Nat (List (bsm_instr n)))
    (st st' : bsm_state n) : Prop :=
  sss_output (bsm_instr n) (t (List Bool) n) (bsm_sss n) P st st'

theorem eval_iff (n : Nat) (i : Nat) (prog : List (bsm_instr n))
    (c : Nat) (v : t (List Bool) n) (c' : Nat) (v' : t (List Bool) n) :
    eval n (Prod.mk (α := Nat) (β := List (bsm_instr n)) i prog)
      (Prod.mk (α := Nat) (β := t (List Bool) n) c v)
      (Prod.mk (α := Nat) (β := t (List Bool) n) c' v') ↔
    sss_output (bsm_instr n) (t (List Bool) n) (bsm_sss n)
      (Prod.mk (α := Nat) (β := List (bsm_instr n)) i prog)
      (Prod.mk (α := Nat) (β := t (List Bool) n) c v)
      (Prod.mk (α := Nat) (β := t (List Bool) n) c' v') := by
  rfl

def BSM_HALTING : BSM_PROBLEM -> Prop
  | sigT.existT n (sigT.existT i (sigT.existT prog v)) =>
      sss_terminates (bsm_instr n) (t (List Bool) n) (bsm_sss n)
        (Prod.mk (α := Nat) (β := List (bsm_instr n)) i prog)
        (Prod.mk (α := Nat) (β := t (List Bool) n) i v)

def Halt_BSM : BSM_PROBLEM -> Prop := BSM_HALTING

theorem Halt_BSM_iff (P : BSM_PROBLEM) : Halt_BSM P ↔ BSM_HALTING P := by
  rfl

def In : ∀ (A : Type), A -> List A -> Prop
  | A, a, [] => False
  | A, a, b :: l => Or (Eq (α := A) b a) (In A a l)

inductive Forall (A : Type) (P : A -> Prop) : List A -> Prop where
  | nil : Forall A P []
  | cons : ∀ {x : A} {l : List A}, P x -> Forall A P l -> Forall A P (x :: l)

theorem Forall_forall (A : Type) (P : A -> Prop) (l : List A) :
    Forall A P l ↔ ∀ x : A, In A x l -> P x := by
  induction l with
  | nil =>
      constructor
      · intro h x hx
        simpa [In] using hx
      · intro h
        exact Forall.nil
  | cons a l ih =>
      constructor
      · intro h x hx
        cases h with
        | cons ha ht =>
            have hx' : Eq (α := A) a x ∨ In A x l := by
              simpa [In] using hx
            cases hx' with
            | inl hax =>
                cases hax
                exact ha
            | inr hxl =>
                exact (ih.mp ht) x hxl
      · intro h
        refine Forall.cons ?_ ?_
        · exact h a (by simp [In])
        · exact ih.mpr (fun x hx => h x (by simpa [In] using Or.inr hx))

inductive mm_instr (X : Type) : Type where
  | mm_inc : X -> mm_instr X
  | mm_dec : X -> Nat -> mm_instr X

inductive mm_sss (n : Nat) : mm_instr (t_1 n) -> Prod Nat (t Nat n) -> Prod Nat (t Nat n) -> Prop where
  | inc (i : Nat) (x : t_1 n) (v : t Nat n) :
      mm_sss n (mm_instr.mm_inc x) (Prod.mk (α := Nat) (β := t Nat n) i v)
        (Prod.mk (α := Nat) (β := t Nat n) (Nat.succ i) (vec_set v x (Nat.succ (vec_get v x))))
  | dec_zero (i : Nat) (x : t_1 n) (k : Nat) (v : t Nat n) :
      vec_get v x = Nat.zero ->
      mm_sss n (mm_instr.mm_dec x k) (Prod.mk (α := Nat) (β := t Nat n) i v)
        (Prod.mk (α := Nat) (β := t Nat n) k v)
  | dec_succ (i : Nat) (x : t_1 n) (k u : Nat) (v : t Nat n) :
      vec_get v x = Nat.succ u ->
      mm_sss n (mm_instr.mm_dec x k) (Prod.mk (α := Nat) (β := t Nat n) i v)
        (Prod.mk (α := Nat) (β := t Nat n) (Nat.succ i) (vec_set v x u))

def mm_eval (n : Nat) (P : Prod Nat (List (mm_instr (t_1 n))))
    (st st' : Prod Nat (t Nat n)) : Prop :=
  sss_output (mm_instr (t_1 n)) (t Nat n) (mm_sss n) P st st'

def MM_PROBLEM : Type :=
  sigT Nat (fun n => sigT (List (mm_instr (t_1 n))) (fun _ => t Nat n))

def MM_HALTING : MM_PROBLEM -> Prop
  | sigT.existT n (sigT.existT prog v) =>
      sss_terminates (mm_instr (t_1 n)) (t Nat n) (mm_sss n)
        (Prod.mk (α := Nat) (β := List (mm_instr (t_1 n))) (Nat.succ Nat.zero) prog)
        (Prod.mk (α := Nat) (β := t Nat n) (Nat.succ Nat.zero) v)

def Halt_MM : MM_PROBLEM -> Prop := MM_HALTING

theorem Halt_MM_iff (P : MM_PROBLEM) : Halt_MM P ↔ MM_HALTING P := by
  rfl

def fractran_regular (l : List (Prod Nat Nat)) : Prop :=
  Forall (Prod Nat Nat) (fun c => c.2 ≠ Nat.zero) l

axiom fractran_terminates : List (Prod Nat Nat) -> Nat -> Prop

def FRACTRAN_PROBLEM : Type := Prod (List (Prod Nat Nat)) Nat

def FRACTRAN_HALTING : FRACTRAN_PROBLEM -> Prop
  | Prod.mk l x => fractran_terminates l x

def FRACTRAN_REG_PROBLEM : Type :=
  sigT (List (Prod Nat Nat)) (fun l => sig Nat (fun _ => fractran_regular l))

def FRACTRAN_REG_HALTING : FRACTRAN_REG_PROBLEM -> Prop
  | sigT.existT l s =>
      match s with
      | sig.exist x _ => fractran_terminates l x

def Halt_FRACTRAN : FRACTRAN_PROBLEM -> Prop := FRACTRAN_HALTING

theorem Halt_FRACTRAN_iff (P : FRACTRAN_PROBLEM) :
    Halt_FRACTRAN P ↔ FRACTRAN_HALTING P := by
  rfl

axiom bsm_state_enc :
  ∀ (n : Nat), t (List Bool) n -> t Nat (Nat.add (Nat.succ (Nat.succ Nat.zero)) n)

axiom bsm_mm_compiler_1 :
  ∀ (n i : Nat) (prog : List (bsm_instr n)),
    sig (List (mm_instr (t_1 (Nat.add (Nat.succ (Nat.succ Nat.zero)) n))))
      (fun q => ∀ v : t (List Bool) n,
        Halt_BSM (sigT.existT n (sigT.existT i (sigT.existT prog v))) ↔
        Halt_MM (sigT.existT (Nat.add (Nat.succ (Nat.succ Nat.zero)) n)
          (sigT.existT q (bsm_state_enc n v))))

axiom mm_fractran_n :
  ∀ (n : Nat) (prog : List (mm_instr (t_1 n))) (v : t Nat n),
    sigT (List (Prod Nat Nat))
      (fun l => sig Nat
        (fun x => And (fractran_regular l)
          (Halt_MM (sigT.existT n (sigT.existT prog v)) ↔ fractran_terminates l x)))

def dio_constraint : Type := (Prod Nat dio_elem_expr)

def h10c_sem : (∀ (c : h10c), (∀ (__ : (∀ (x : Nat), Nat)), Prop)) := (fun (c : h10c) => (fun (__ : (∀ (x : Nat), Nat)) => (match c with | h10c.h10c_one x_1 => (Eq (α := Nat) (__ x_1) (Nat.succ Nat.zero)) | h10c.h10c_plus x_2 y z => (Eq (α := Nat) (Nat.add (__ x_2) (__ y)) (__ z)) | h10c.h10c_mult x_3 y_1 z_1 => (Eq (α := Nat) (Nat.mul (__ x_3) (__ y_1)) (__ z_1)))))

def h10sqc_sem : (∀ (__ : (∀ (x : Nat), Nat)), (∀ (c : h10sqc), Prop)) := (fun (__ : (∀ (x : Nat), Nat)) => (fun (c : h10sqc) => (match c with | h10sqc.h10sqc_one x_1 => (Eq (α := Nat) (__ x_1) (Nat.succ Nat.zero)) | h10sqc.h10sqc_plus x_2 y z => (Eq (α := Nat) (Nat.add (__ x_2) (__ y)) (__ z)) | h10sqc.h10sqc_sq x_3 y_1 => (Eq (α := Nat) (Nat.mul (__ x_3) (__ x_3)) (__ y_1)))))

def not : (∀ (A : Prop), Prop) := (fun (A : Prop) => (∀ (x : A), False))

def reduction_3 (X : Type u) (Y : Type v) (f : X -> Y) (P : X -> Prop) (Q : Y -> Prop) : Prop :=
  ∀ x : X, P x ↔ Q (f x)

def reduces (X : Type u) (Y : Type v) (P : X -> Prop) (Q : Y -> Prop) : Prop :=
  ex (X -> Y) (fun f => reduction_3 X Y f P Q)

def BSM_MM_HALTING : reduces BSM_PROBLEM MM_PROBLEM Halt_BSM Halt_MM := by
  let f : ∀ x : BSM_PROBLEM, MM_PROBLEM := fun H =>
    match H with
    | sigT.existT n (sigT.existT i (sigT.existT prog v)) =>
        match bsm_mm_compiler_1 n i prog with
        | sig.exist q _ =>
            sigT.existT (Nat.add (Nat.succ (Nat.succ Nat.zero)) n)
              (sigT.existT q (bsm_state_enc n v))
  refine ex.ex_intro (∀ x : BSM_PROBLEM, MM_PROBLEM)
    (fun g => reduction_3 BSM_PROBLEM MM_PROBLEM g Halt_BSM Halt_MM) f ?_
  intro H
  cases H with
  | existT n s =>
      cases s with
      | existT i s0 =>
          cases s0 with
          | existT prog v =>
              dsimp [f]
              cases bsm_mm_compiler_1 n i prog with
              | exist q hq =>
                  simpa using hq v

def MM_FRACTRAN_REG_HALTING : reduces MM_PROBLEM FRACTRAN_REG_PROBLEM Halt_MM FRACTRAN_REG_HALTING := by
  let f : ∀ x : MM_PROBLEM, FRACTRAN_REG_PROBLEM := fun H =>
    match H with
    | sigT.existT n (sigT.existT prog v) =>
        match mm_fractran_n n prog v with
        | sigT.existT l s =>
            match s with
            | sig.exist x h =>
            match h with
            | And.intro hreg _ =>
                sigT.existT l
                  (sig.exist x hreg)
  refine ex.ex_intro (∀ x : MM_PROBLEM, FRACTRAN_REG_PROBLEM)
    (fun g => reduction_3 MM_PROBLEM FRACTRAN_REG_PROBLEM g Halt_MM FRACTRAN_REG_HALTING) f ?_
  intro H
  cases H with
  | existT n s =>
      cases s with
      | existT prog v =>
          dsimp [f]
          cases mm_fractran_n n prog v with
          | existT l s =>
              cases s with
              | exist x h =>
                  cases h with
                  | intro hreg hterm =>
                  dsimp
                  exact hterm

def FRACTRAN_REG_FRACTRAN_HALTING : reduces FRACTRAN_REG_PROBLEM FRACTRAN_PROBLEM FRACTRAN_REG_HALTING Halt_FRACTRAN := by
  let f : ∀ x : FRACTRAN_REG_PROBLEM, FRACTRAN_PROBLEM := fun H =>
    match H with
    | sigT.existT l s =>
        match s with
        | sig.exist x _ => Prod.mk l x
  refine ex.ex_intro (∀ x : FRACTRAN_REG_PROBLEM, FRACTRAN_PROBLEM)
    (fun g => reduction_3 FRACTRAN_REG_PROBLEM FRACTRAN_PROBLEM g FRACTRAN_REG_HALTING Halt_FRACTRAN) f ?_
  intro H
  cases H with
  | existT l s =>
      cases s with
      | exist x hreg =>
          rfl

def DIO_LOGIC_PROBLEM : Type := Prod dio_formula (Nat -> Nat)

def DIO_LOGIC_SAT : DIO_LOGIC_PROBLEM -> Prop
  | Prod.mk f ν => df_pred f ν

axiom fractran_halting_on_diophantine :
  ∀ (l : List (Prod Nat Nat)) (x : Nat),
    sig dio_formula
      (fun f => ∀ ν : Nat -> Nat, df_pred f ν ↔ Halt_FRACTRAN (Prod.mk l x))

def FRACTRAN_HALTING_DIO_LOGIC_SAT :
    reduces FRACTRAN_PROBLEM DIO_LOGIC_PROBLEM Halt_FRACTRAN DIO_LOGIC_SAT := by
  let f : ∀ x : FRACTRAN_PROBLEM, DIO_LOGIC_PROBLEM := fun H =>
    match H with
    | Prod.mk l x =>
        match fractran_halting_on_diophantine l x with
        | sig.exist φ _ => Prod.mk φ (fun _ => x)
  refine ex.ex_intro (∀ x : FRACTRAN_PROBLEM, DIO_LOGIC_PROBLEM)
    (fun g => reduction_3 FRACTRAN_PROBLEM DIO_LOGIC_PROBLEM g Halt_FRACTRAN DIO_LOGIC_SAT) f ?_
  intro H
  cases H with
  | mk l x =>
      dsimp [f, DIO_LOGIC_SAT]
      cases fractran_halting_on_diophantine l x with
      | exist φ hφ =>
          simpa using (hφ (fun _ => x)).symm

def DIO_ELEM_PROBLEM : Type := Prod (List dio_constraint) (Nat -> Nat)

def DIO_ELEM_SAT : DIO_ELEM_PROBLEM -> Prop
  | Prod.mk l ν => ex (Nat -> Nat) (fun φ => Forall dio_constraint (dc_eval φ ν) l)

axiom dio_formula_elem :
  ∀ (A : dio_formula),
    sig (List dio_constraint)
      (fun l => ∀ ν : Nat -> Nat,
        df_pred A ν ↔ ex (Nat -> Nat) (fun φ => Forall dio_constraint (dc_eval φ ν) l))

def DIO_LOGIC_ELEM_SAT :
    reduces DIO_LOGIC_PROBLEM DIO_ELEM_PROBLEM DIO_LOGIC_SAT DIO_ELEM_SAT := by
  let f : ∀ x : DIO_LOGIC_PROBLEM, DIO_ELEM_PROBLEM := fun H =>
    match H with
    | Prod.mk A ν =>
        match dio_formula_elem A with
        | sig.exist l _ => Prod.mk l ν
  refine ex.ex_intro (∀ x : DIO_LOGIC_PROBLEM, DIO_ELEM_PROBLEM)
    (fun g => reduction_3 DIO_LOGIC_PROBLEM DIO_ELEM_PROBLEM g DIO_LOGIC_SAT DIO_ELEM_SAT) f ?_
  intro H
  cases H with
  | mk A ν =>
      dsimp [f, DIO_LOGIC_SAT, DIO_ELEM_SAT]
      cases dio_formula_elem A with
      | exist l hl =>
          simpa using hl ν

def H10C_SAT : (∀ (cs : (List h10c)), Prop) := (fun (cs : (List h10c)) => (ex (∀ (x : Nat), Nat) (fun (__ : (∀ (x_1 : Nat), Nat)) => (∀ (c : h10c), (∀ (x_2 : (In h10c c cs)), (h10c_sem c __))))))

axiom dc_list_h10c : (Nat -> Nat) -> List dio_constraint -> List h10c

axiom dc_list_h10c_spec :
  ∀ (ν : Nat -> Nat) (l : List dio_constraint),
    ex (Nat -> Nat) (fun φ => Forall dio_constraint (dc_eval φ ν) l) ↔
    ex (Nat -> Nat) (fun ψ => Forall h10c (fun c => h10c_sem c ψ) (dc_list_h10c ν l))

theorem H10C_SAT_iff_exists_Forall (cs : List h10c) :
    H10C_SAT cs ↔ ex (Nat -> Nat) (fun ψ => Forall h10c (fun c => h10c_sem c ψ) cs) := by
  constructor
  · intro h
    cases h with
    | intro ψ hψ =>
        exact ex.ex_intro (Nat -> Nat) (fun g => Forall h10c (fun c => h10c_sem c g) cs) ψ ((Forall_forall h10c (fun c => h10c_sem c ψ) cs).mpr hψ)
  · intro h
    cases h with
    | intro ψ hψ =>
        exact ex.ex_intro (Nat -> Nat) (fun g => ∀ c : h10c, In h10c c cs -> h10c_sem c g) ψ ((Forall_forall h10c (fun c => h10c_sem c ψ) cs).mp hψ)

def DIO_ELEM_H10C_SAT : reduces DIO_ELEM_PROBLEM (List h10c) DIO_ELEM_SAT H10C_SAT := by
  let f : ∀ x : DIO_ELEM_PROBLEM, List h10c := fun H =>
    match H with
    | Prod.mk l ν => dc_list_h10c ν l
  refine ex.ex_intro (∀ x : DIO_ELEM_PROBLEM, List h10c)
    (fun g => reduction_3 DIO_ELEM_PROBLEM (List h10c) g DIO_ELEM_SAT H10C_SAT) f ?_
  intro H
  cases H with
  | mk l ν =>
      dsimp [f, DIO_ELEM_SAT]
      simpa [H10C_SAT_iff_exists_Forall] using dc_list_h10c_spec ν l

def H10SQC_SAT : (∀ (cs : (List h10sqc)), Prop) := (fun (cs : (List h10sqc)) => (ex (∀ (x : Nat), Nat) (fun (__ : (∀ (x_1 : Nat), Nat)) => (∀ (c : h10sqc), (∀ (x_2 : (In h10sqc c cs)), (h10sqc_sem __ c))))))

axiom h10c_to_h10sqcs : List h10c -> List h10sqc
axiom h10c_to_h10sqcs_transport :
  ∀ cs : List h10c, H10C_SAT cs -> H10SQC_SAT (h10c_to_h10sqcs cs)
axiom h10c_to_h10sqcs_inverse :
  ∀ cs : List h10c, H10SQC_SAT (h10c_to_h10sqcs cs) -> H10C_SAT cs

def reduction_2 : reduces (List h10c) (List h10sqc) H10C_SAT H10SQC_SAT := by
  let f : ∀ x : List h10c, List h10sqc := h10c_to_h10sqcs
  refine ex.ex_intro (∀ x : List h10c, List h10sqc)
    (fun g => reduction_3 (List h10c) (List h10sqc) g H10C_SAT H10SQC_SAT) f ?_
  intro cs
  exact Iff.intro (h10c_to_h10sqcs_transport cs) (h10c_to_h10sqcs_inverse cs)

def h10uc : Type := (Prod (Prod Nat Nat) Nat)

def h10uc_sem : (∀ (__ : (∀ (x : Nat), Nat)), (∀ (c : h10uc), Prop)) := (fun (__ : (∀ (x : Nat), Nat)) => (fun (c : h10uc) => (match c with | (p, z) => (match p with | (x_1, y) => (Eq (α := Nat) (Nat.add (Nat.add (Nat.succ Nat.zero) (__ x_1)) (Nat.mul (__ y) (__ y))) (__ z))))))

def H10UC_SAT : (∀ (cs : (List h10uc)), Prop) := (fun (cs : (List h10uc)) => (ex (∀ (x : Nat), Nat) (fun (__ : (∀ (x_1 : Nat), Nat)) => (∀ (c : h10uc), (∀ (x_2 : (In h10uc c cs)), (h10uc_sem __ c))))))

axiom h10sqc_to_h10ucs : List h10sqc -> List h10uc
axiom h10sqc_to_h10ucs_transport :
  ∀ cs : List h10sqc, H10SQC_SAT cs -> H10UC_SAT (h10sqc_to_h10ucs cs)
axiom h10sqc_to_h10ucs_inverse :
  ∀ cs : List h10sqc, H10UC_SAT (h10sqc_to_h10ucs cs) -> H10SQC_SAT cs

def reduction_1 : reduces (List h10sqc) (List h10uc) H10SQC_SAT H10UC_SAT := by
  let f : ∀ x : List h10sqc, List h10uc := h10sqc_to_h10ucs
  refine ex.ex_intro (∀ x : List h10sqc, List h10uc)
    (fun g => reduction_3 (List h10sqc) (List h10uc) g H10SQC_SAT H10UC_SAT) f ?_
  intro cs
  exact Iff.intro (h10sqc_to_h10ucs_transport cs) (h10sqc_to_h10ucs_inverse cs)

def reduces_transitive :
    ∀ (X : Type u) (P : X -> Prop) (Y : Type v) (Q : Y -> Prop) (Z : Type w) (R : Z -> Prop),
      reduces X Y P Q -> reduces Y Z Q R -> reduces X Z P R := by
  intro X P Y Q Z R H H0
  cases H with
  | intro f hf =>
      cases H0 with
      | intro g hg =>
          refine ex.ex_intro (∀ x : X, Z) (fun h => reduction_3 X Z h P R) (fun x => g (f x)) ?_
          intro x
          exact Iff.trans (hf x) (hg (f x))

def num_states : (∀ (s : SBTM), Nat) := (fun (s : SBTM) => (SBTM.casesOn (motive := (fun s_1 => Nat)) s (fun num_states trans => num_states)))

axiom config_enumeration : (∀ (M : SBTM), (sig (∀ (x : Nat), (Option (Prod (t_1 (num_states M)) (Prod (Prod (List Bool) Bool) (List Bool))))) (fun (e : (∀ (x_1 : Nat), (Option (Prod (t_1 (num_states M)) (Prod (Prod (List Bool) Bool) (List Bool)))))) => (enumerator__T' (Prod (t_1 (num_states M)) (Prod (Prod (List Bool) Bool) (List Bool))) e))))

axiom steps : (∀ (M : SBTM), (∀ (k : Nat), (∀ (x : (Prod (t_1 (num_states M)) (Prod (Prod (List Bool) Bool) (List Bool)))), (Option (Prod (t_1 (num_states M)) (Prod (Prod (List Bool) Bool) (List Bool)))))))

axiom SBTM_HALT : (∀ (x : (sigT SBTM (fun (M : SBTM) => (Prod (t_1 (num_states M)) (Prod (Prod (List Bool) Bool) (List Bool)))))), Prop)

axiom reduction_4 : (reduces (sigT SBTM (fun (M : SBTM) => (Prod (t_1 (num_states M)) (Prod (Prod (List Bool) Bool) (List Bool))))) BSM_PROBLEM SBTM_HALT BSM_HALTING)

def complement (X : Type u) (P : X -> Prop) : X -> Prop :=
  fun x => not (P x)

def reduces_complement :
    ∀ (X : Type u) (P : X -> Prop) (Y : Type v) (Q : Y -> Prop),
      reduces X Y P Q -> reduces X Y (complement X P) (complement Y Q) := by
  intro X P Y Q H
  cases H with
  | intro f hf =>
      refine ex.ex_intro (∀ x : X, Y) (fun g => reduction_3 X Y g (complement X P) (complement Y Q)) f ?_
      intro x
      constructor
      · intro hP hQ
        exact hP ((hf x).2 hQ)
      · intro hQ hP
        exact hQ ((hf x).1 hP)

def h10upc : Type := (Prod (Prod Nat Nat) (Prod Nat Nat))

def h10upc_sem : (∀ (__ : (∀ (x : Nat), Nat)), (∀ (c : h10upc), Prop)) :=
  fun ρ c => HeytingLean.InqBQ.h10upcSem ρ c

def H10UPC_SAT : (∀ (cs : (List h10upc)), Prop) := (fun (cs : (List h10upc)) => (ex (∀ (x : Nat), Nat) (fun (__ : (∀ (x_1 : Nat), Nat)) => (∀ (c : h10upc), (∀ (x_2 : (In h10upc c cs)), (h10upc_sem __ c))))))

axiom h10uc_to_h10upcs : List h10uc -> List h10upc
axiom h10uc_to_h10upcs_transport :
  ∀ cs : List h10uc, H10UC_SAT cs -> H10UPC_SAT (h10uc_to_h10upcs cs)
axiom h10uc_to_h10upcs_inverse :
  ∀ cs : List h10uc, H10UPC_SAT (h10uc_to_h10upcs cs) -> H10UC_SAT cs

def reduction : reduces (List h10uc) (List h10upc) H10UC_SAT H10UPC_SAT := by
  let f : ∀ x : List h10uc, List h10upc := h10uc_to_h10upcs
  refine ex.ex_intro (∀ x : List h10uc, List h10upc)
    (fun g => reduction_3 (List h10uc) (List h10upc) g H10UC_SAT H10UPC_SAT) f ?_
  intro cs
  exact Iff.intro (h10uc_to_h10upcs_transport cs) (h10uc_to_h10upcs_inverse cs)

def undecidable (X : Type u) (p : X -> Prop) : Prop :=
  decidable X p -> False

axiom complement_SBTM_HALT_undec : (undecidable (sigT SBTM (fun (M : SBTM) => (Prod (t_1 (num_states M)) (Prod (Prod (List Bool) Bool) (List Bool))))) (complement (sigT SBTM (fun (M_1 : SBTM) => (Prod (t_1 (num_states M_1)) (Prod (Prod (List Bool) Bool) (List Bool))))) SBTM_HALT))

def undecidability_from_reducibility :
    ∀ (X : Type u) (p : X -> Prop) (Y : Type v) (q : Y -> Prop),
      undecidable X p -> reduces X Y p q -> undecidable Y q := by
  intro X p Y q H H0 HdecY
  apply H
  cases H0 with
  | intro f hf =>
      cases HdecY with
      | intro d hd =>
          refine ex.ex_intro (X -> Bool) (fun g => ∀ x : X, p x ↔ Eq (α := Bool) (g x) Bool.true) (fun x => d (f x)) ?_
          intro x
          exact Iff.trans (hf x) (hd (f x))

def reduction_4_halt :
    reduces (sigT SBTM (fun (M : SBTM) => Prod (t_1 (num_states M)) (Prod (Prod (List Bool) Bool) (List Bool))))
      BSM_PROBLEM SBTM_HALT Halt_BSM := by
  cases reduction_4 with
  | intro f hf =>
      refine ex.ex_intro _ _ f ?_
      intro x
      exact Iff.trans (hf x) (Halt_BSM_iff (f x)).symm

def reduction_h10sqc_to_h10upc : reduces (List h10sqc) (List h10upc) H10SQC_SAT H10UPC_SAT :=
  reduces_transitive (List h10sqc) H10SQC_SAT (List h10uc) H10UC_SAT (List h10upc) H10UPC_SAT reduction_1 reduction

def reduction_h10c_to_h10upc : reduces (List h10c) (List h10upc) H10C_SAT H10UPC_SAT :=
  reduces_transitive (List h10c) H10C_SAT (List h10sqc) H10SQC_SAT (List h10upc) H10UPC_SAT reduction_2 reduction_h10sqc_to_h10upc

def reduction_dio_elem_to_h10upc : reduces DIO_ELEM_PROBLEM (List h10upc) DIO_ELEM_SAT H10UPC_SAT :=
  reduces_transitive DIO_ELEM_PROBLEM DIO_ELEM_SAT (List h10c) H10C_SAT (List h10upc) H10UPC_SAT DIO_ELEM_H10C_SAT reduction_h10c_to_h10upc

def reduction_dio_logic_to_h10upc : reduces DIO_LOGIC_PROBLEM (List h10upc) DIO_LOGIC_SAT H10UPC_SAT :=
  reduces_transitive DIO_LOGIC_PROBLEM DIO_LOGIC_SAT DIO_ELEM_PROBLEM DIO_ELEM_SAT (List h10upc) H10UPC_SAT DIO_LOGIC_ELEM_SAT reduction_dio_elem_to_h10upc

def reduction_fractran_to_h10upc : reduces FRACTRAN_PROBLEM (List h10upc) Halt_FRACTRAN H10UPC_SAT :=
  reduces_transitive FRACTRAN_PROBLEM Halt_FRACTRAN DIO_LOGIC_PROBLEM DIO_LOGIC_SAT (List h10upc) H10UPC_SAT FRACTRAN_HALTING_DIO_LOGIC_SAT reduction_dio_logic_to_h10upc

def reduction_fractran_reg_to_h10upc : reduces FRACTRAN_REG_PROBLEM (List h10upc) FRACTRAN_REG_HALTING H10UPC_SAT :=
  reduces_transitive FRACTRAN_REG_PROBLEM FRACTRAN_REG_HALTING FRACTRAN_PROBLEM Halt_FRACTRAN (List h10upc) H10UPC_SAT FRACTRAN_REG_FRACTRAN_HALTING reduction_fractran_to_h10upc

def reduction_mm_to_h10upc : reduces MM_PROBLEM (List h10upc) Halt_MM H10UPC_SAT :=
  reduces_transitive MM_PROBLEM Halt_MM FRACTRAN_REG_PROBLEM FRACTRAN_REG_HALTING (List h10upc) H10UPC_SAT MM_FRACTRAN_REG_HALTING reduction_fractran_reg_to_h10upc

def reduction_bsm_to_h10upc : reduces BSM_PROBLEM (List h10upc) Halt_BSM H10UPC_SAT :=
  reduces_transitive BSM_PROBLEM Halt_BSM MM_PROBLEM Halt_MM (List h10upc) H10UPC_SAT BSM_MM_HALTING reduction_mm_to_h10upc

def reduction_sbtm_to_h10upc :
    reduces (sigT SBTM (fun (M : SBTM) => Prod (t_1 (num_states M)) (Prod (Prod (List Bool) Bool) (List Bool))))
      (List h10upc) SBTM_HALT H10UPC_SAT :=
  reduces_transitive
    (sigT SBTM (fun (M : SBTM) => Prod (t_1 (num_states M)) (Prod (Prod (List Bool) Bool) (List Bool))))
    SBTM_HALT
    BSM_PROBLEM
    Halt_BSM
    (List h10upc)
    H10UPC_SAT
    reduction_4_halt
    reduction_bsm_to_h10upc

def H10UPC_SAT_compl_undec : undecidable (List h10upc) (complement (List h10upc) H10UPC_SAT) :=
  undecidability_from_reducibility
    (sigT SBTM (fun (M : SBTM) => Prod (t_1 (num_states M)) (Prod (Prod (List Bool) Bool) (List Bool))))
    (complement (sigT SBTM (fun (M : SBTM) => Prod (t_1 (num_states M)) (Prod (Prod (List Bool) Bool) (List Bool)))) SBTM_HALT)
    (List h10upc)
    (complement (List h10upc) H10UPC_SAT)
    complement_SBTM_HALT_undec
    (reduces_complement
      (sigT SBTM (fun (M : SBTM) => Prod (t_1 (num_states M)) (Prod (Prod (List Bool) Bool) (List Bool))))
      SBTM_HALT
      (List h10upc)
      H10UPC_SAT
      reduction_sbtm_to_h10upc)

end TranslationKernelV2
