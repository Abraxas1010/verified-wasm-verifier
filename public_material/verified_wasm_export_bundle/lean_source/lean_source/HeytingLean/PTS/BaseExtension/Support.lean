import HeytingLean.PTS.BaseExtension.IPL
import HeytingLean.PTS.BaseExtension.Operational

namespace HeytingLean.PTS.BaseExtension

/--
A Sandqvist-style base for propositional support semantics. At this scaffold
stage, bases are sets of atomic facts; extensions add more supported atoms.
-/
abbrev Base := List Atom

def BaseExtends (B C : Base) : Prop :=
  ∀ ⦃a : Atom⦄, a ∈ B → a ∈ C

def encodeBase (B : Base) : Program :=
  B.map fun a => Definite.atom (.atom a)

def Supports (B : Base) : IPL → Prop
  | .atom a => a ∈ B
  | .bot => False
  | .conj φ ψ => Supports B φ ∧ Supports B ψ
  | .disj φ ψ =>
      ∀ ⦃C : Base⦄ (p : Atom),
        BaseExtends B C →
        (Supports C φ → p ∈ C) →
        (Supports C ψ → p ∈ C) →
        p ∈ C
  | .imp φ ψ =>
      ∀ ⦃C : Base⦄, BaseExtends B C → Supports C φ → Supports C ψ

lemma baseExtends_refl (B : Base) : BaseExtends B B := by
  intro a ha
  exact ha

lemma encodeBase_mem {B : Base} {a : Atom} :
    Definite.atom (.atom a) ∈ encodeBase B ↔ a ∈ B := by
  unfold encodeBase
  simp

@[simp] lemma programAtoms_encodeBase (B : Base) :
    programAtoms (encodeBase B) = B := by
  induction B with
  | nil =>
      simp [encodeBase, programAtoms]
  | cons hd tl ih =>
      simpa [encodeBase, programAtoms, definiteAtoms, atomVarAtoms] using
        congrArg (List.cons hd) ih

lemma supports_atom_imp_atom_iff (B : Base) (p q : Atom) :
    Supports B (.imp (.atom p) (.atom q)) ↔ p = q ∨ q ∈ B := by
  constructor
  · intro h
    by_cases hpq : p = q
    · exact Or.inl hpq
    · have hq : Supports (p :: B) (.atom q) := by
        have hp : Supports (p :: B) (.atom p) := by
          simp [Supports]
        exact h (by
          intro a ha
          exact List.mem_cons_of_mem _ ha) hp
      rcases List.mem_cons.mp hq with hqEq | hqMem
      · exact False.elim (hpq hqEq.symm)
      · exact Or.inr hqMem
  · rintro (rfl | hq) C hBC hp
    · exact hp
    · exact hBC hq

lemma supports_monotone {B C : Base} (hBC : BaseExtends B C) :
    ∀ {φ : IPL}, Supports B φ → Supports C φ := by
  intro φ
  induction φ generalizing B C with
  | atom a =>
      intro h
      exact hBC h
  | bot =>
      intro h
      exact False.elim h
  | conj φ ψ ihφ ihψ =>
      intro h
      exact ⟨ihφ hBC h.1, ihψ hBC h.2⟩
  | disj φ ψ ihφ ihψ =>
      intro h D p hCD hφ hψ
      exact h p (by
        intro a ha
        exact hCD (hBC ha)) hφ hψ
  | imp φ ψ ihφ ihψ =>
      intro h D hCD hφ
      have hBD : BaseExtends B D := by
        intro a ha
        exact hCD (hBC ha)
      exact h hBD hφ

example : Supports [⟨0⟩] (.disj (.atom ⟨0⟩) (.atom ⟨1⟩)) := by
  intro C p hC hLeft _hRight
  exact hLeft (by simpa [Supports] using hC (show (⟨0⟩ : Atom) ∈ [⟨0⟩] by simp))

end HeytingLean.PTS.BaseExtension
