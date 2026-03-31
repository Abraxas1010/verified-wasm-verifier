import HeytingLean.PTS.BaseExtension.Completeness

namespace HeytingLean.PTS.BaseExtension

abbrev ProgramBase := Program

abbrev ProgramBaseExtends := extends_

/--
Program-based support semantics. This is the generalization point where bases are
arbitrary programs rather than atomic fact lists.

The atom case is operational by design. `⊥` remains semantically unsupported here,
which means the unrestricted theorem

`∀ B φ, ProgramSupports B φ ↔ SearchSupports B (encode φ)`

is false once the executable kernel admits the compiled absurd clause `Definite.absurd`.
-/
def ProgramSupports (B : ProgramBase) : IPL → Prop
  | .atom a => Proves B (.atom (.atom a))
  | .bot => False
  | .conj φ ψ => ProgramSupports B φ ∧ ProgramSupports B ψ
  | .disj φ ψ => ProgramSupports B φ ∨ ProgramSupports B ψ
  | .imp φ ψ =>
      ∀ ⦃C : ProgramBase⦄, ProgramBaseExtends B C →
        ProgramSupports C φ → ProgramSupports C ψ

theorem programAtom_support_iff_search (B : ProgramBase) (a : Atom) :
    ProgramSupports B (.atom a) ↔ SearchSupports B (encode (.atom a)) := by
  constructor
  · intro h
    simpa [ProgramSupports, encode] using (search_complete h)
  · rintro ⟨fuel, hfuel⟩
    simpa [ProgramSupports, encode] using (search_sound hfuel)

theorem searchSupports_absurd_program_bot :
    SearchSupports [Definite.absurd] (encode .bot) := by
  exact ⟨3, by native_decide⟩

theorem not_programSupports_absurd_program_bot :
    ¬ ProgramSupports [Definite.absurd] .bot := by
  simp [ProgramSupports]

theorem no_global_programSupports_bridge :
    ¬ (∀ B : ProgramBase, ∀ φ : IPL, ProgramSupports B φ ↔ SearchSupports B (encode φ)) := by
  intro h
  have hBot : ProgramSupports [Definite.absurd] .bot :=
    (h [Definite.absurd] .bot).2 searchSupports_absurd_program_bot
  exact not_programSupports_absurd_program_bot hBot

end HeytingLean.PTS.BaseExtension
