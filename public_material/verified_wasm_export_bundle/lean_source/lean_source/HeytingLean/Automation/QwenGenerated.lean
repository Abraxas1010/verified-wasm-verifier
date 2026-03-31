import HeytingLean.Numbers.SurrealCore


namespace HeytingLean
namespace Numbers
namespace SurrealCore
namespace PreGame

@[simp] theorem birthday_build (L R : List PreGame) :
  birthday (build L R) = Nat.succ (Nat.max (maxBirth L) (maxBirth R)) := rfl

@[simp] theorem maxBirth_nil : maxBirth [] = 0 := rfl

end PreGame
end SurrealCore
end Numbers
end HeytingLean
