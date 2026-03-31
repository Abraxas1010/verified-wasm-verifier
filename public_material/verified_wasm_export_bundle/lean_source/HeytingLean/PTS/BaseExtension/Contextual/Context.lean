import HeytingLean.PTS.BaseExtension.Contextual.Kernel

namespace HeytingLean.PTS.BaseExtension.Contextual

/-!
# Base types for program-level base-extension semantics

Following Gheorghiu (arXiv:2603.13018v1, Definition 3.1), a base is a program
in the second-order logic-programming language. Base extension means adding
arbitrary clauses (not just atoms).

The previous atomic `structure Base` has been replaced by `abbrev Base := Program`.
Atomic bases are available as a convenience constructor `atomicBase`.
-/

abbrev Base := Program

def BaseExtends (B C : Base) : Prop :=
  ∀ ⦃g : Goal⦄, g ∈ B → g ∈ C

def encodeBase (B : Base) : Program := B

/-- Convenience constructor for purely atomic bases.
    Produces a program of atom goals, one per atom. -/
def atomicBase (atoms : List Atom) : Base :=
  atoms.map (fun a => Goal.atom (AtomVar.atom a))

/-- Legacy alias for backward compatibility. -/
def baseOfAtoms (atoms : List Atom) : Base :=
  atomicBase atoms

theorem baseExtends_refl (B : Base) : BaseExtends B B := by
  intro g hg
  exact hg

theorem baseExtends_trans {A B C : Base}
    (hAB : BaseExtends A B) (hBC : BaseExtends B C) :
    BaseExtends A C := by
  intro g hg
  exact hBC (hAB hg)

theorem baseExtends_cons (B : Base) (g : Goal) : BaseExtends B (g :: B) := by
  intro g' hg'
  exact List.mem_cons_of_mem g hg'

end Contextual
end HeytingLean.PTS.BaseExtension
