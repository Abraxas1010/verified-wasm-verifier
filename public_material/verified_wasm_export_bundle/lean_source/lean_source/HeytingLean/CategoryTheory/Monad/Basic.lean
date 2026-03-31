import HeytingLean.CDL.RNucleusMonad

namespace HeytingLean
namespace CategoryTheory
namespace Monad

open HeytingLean.CDL

universe u

def id_is_r_nucleus_monad : RNucleusMonad Id := by
  infer_instance

def option_is_r_nucleus_monad : RNucleusMonad Option := by
  infer_instance

def strong_monad_lifts_to_r_nucleus (R : Type u → Type u) [StrongMonad R] :
    RNucleusMonad R := by
  infer_instance

def para_map_identity_2cell (T : Type u → Type u) [StrongMonad T] [LawfulMonad T]
    (X : Type u) :
    CDL.Para.Para2Hom (CDL.Para.map (T := T) (CDL.Para.ParaHom.id X))
      (CDL.Para.ParaHom.id (T X)) :=
  CDL.Para.map_id (T := T) X

def para_map_comp_2cell (T : Type u → Type u) [StrongMonad T] [LawfulMonad T]
    {X Y Z : Type u} (g : CDL.Para.ParaHom Y Z) (f : CDL.Para.ParaHom X Y) :
    CDL.Para.Para2Hom
      (CDL.Para.map (T := T) (CDL.Para.ParaHom.comp g f))
      (CDL.Para.ParaHom.comp (CDL.Para.map (T := T) g) (CDL.Para.map (T := T) f)) :=
  CDL.Para.map_comp (T := T) g f

end Monad
end CategoryTheory
end HeytingLean
