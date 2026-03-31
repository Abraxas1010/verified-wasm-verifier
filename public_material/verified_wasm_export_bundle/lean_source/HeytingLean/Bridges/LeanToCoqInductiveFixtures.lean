namespace HeytingLean.Bridges.LeanToCoqInductiveFixtures

inductive MyBool : Type where
  | t : MyBool
  | f : MyBool

def neg : MyBool → MyBool
  | MyBool.t => MyBool.f
  | MyBool.f => MyBool.t

def test1 : neg MyBool.t = MyBool.f := rfl
def test2 : neg MyBool.f = MyBool.t := rfl

def optGet (o : Option Nat) : Nat :=
  Option.casesOn o Nat.zero (fun a => a)

def test3 : optGet (Option.some (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))) =
    (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))) := rfl
def test4 : optGet (Option.none) = Nat.zero := rfl

def sumSwap : Sum Nat Bool → Sum Bool Nat
  | Sum.inl n => Sum.inr n
  | Sum.inr b => Sum.inl b

def test5 : sumSwap (Sum.inl (Nat.succ (Nat.succ Nat.zero))) = Sum.inr (Nat.succ (Nat.succ Nat.zero)) := rfl
def test6 : sumSwap (Sum.inr Bool.true) = Sum.inl Bool.true := rfl

def prodFst (p : Prod Nat Bool) : Nat :=
  Prod.fst p

def test7 : prodFst (Prod.mk (Nat.succ (Nat.succ (Nat.succ Nat.zero))) Bool.false) =
    (Nat.succ (Nat.succ (Nat.succ Nat.zero))) := rfl

def listHeadOr0 (xs : List Nat) : Nat :=
  List.casesOn xs Nat.zero (fun a _ => a)

def test8 : listHeadOr0 (List.cons (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) List.nil) =
    (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) := rfl
def test9 : listHeadOr0 (List.nil) = Nat.zero := rfl

def listTailOrNil (xs : List Nat) : List Nat :=
  List.casesOn xs List.nil (fun _ t => t)

def test10 : listTailOrNil (List.cons (Nat.succ Nat.zero) (List.cons (Nat.succ (Nat.succ Nat.zero)) List.nil)) =
    (List.cons (Nat.succ (Nat.succ Nat.zero)) List.nil) := rfl
def test11 : listTailOrNil (List.nil) = List.nil := rfl

def prodSwap (p : Prod Nat Bool) : Prod Bool Nat :=
  Prod.mk p.snd p.fst

def test12 : prodSwap (Prod.mk (Nat.succ Nat.zero) Bool.true) = Prod.mk Bool.true (Nat.succ Nat.zero) := rfl

end HeytingLean.Bridges.LeanToCoqInductiveFixtures
