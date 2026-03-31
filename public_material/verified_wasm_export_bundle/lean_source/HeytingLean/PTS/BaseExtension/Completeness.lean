import HeytingLean.PTS.BaseExtension.Soundness

namespace HeytingLean.PTS.BaseExtension

theorem atom_search_implies_support (B : Base) (a : Atom) :
    SearchSupports (encodeBase B) (encode (.atom a)) → Supports B (.atom a) := by
  rintro ⟨fuel, hfuel⟩
  cases fuel with
  | zero =>
      simp [search] at hfuel
  | succ fuel =>
      rw [search_encodeBase_atom_eq_factSearch fuel B a] at hfuel
      have hfact : factSearch (encodeBase B) (.atom a) = true := hfuel
      exact (factSearch_encodeBase_atom_iff).1 hfact

theorem bot_search_implies_support (B : Base) :
    SearchSupports (encodeBase B) (encode .bot) → Supports B .bot := by
  rintro ⟨fuel, hfuel⟩
  rw [search_encodeBase_bot_false fuel B] at hfuel
  cases hfuel

theorem atomImp_search_implies_support (B : Base) (p q : Atom) :
    SearchSupports (encodeBase B) (encode (.imp (.atom p) (.atom q))) →
      Supports B (.imp (.atom p) (.atom q)) := by
  rintro ⟨fuel, hfuel⟩
  cases fuel with
  | zero =>
      simp [search] at hfuel
  | succ fuel =>
      have hcons : SearchSupports (encodeBase (p :: B)) (encode (.atom q)) := by
        refine ⟨fuel, ?_⟩
        rw [← search_imp_atom_atom_eq_search_cons fuel B p q]
        exact hfuel
      exact (supports_atom_imp_atom_iff B p q).2 <|
        by
          have hq : Supports (p :: B) (.atom q) := atom_search_implies_support (p :: B) q hcons
          rcases List.mem_cons.mp hq with rfl | hqMem
          · exact Or.inl rfl
          · exact Or.inr hqMem

theorem search_complete {P : Program} {g : Goal} :
    Proves P g → ∃ fuel, search fuel P g = true := by
  intro h
  induction h with
  | absurd hAbs =>
      exact ⟨1, (SearchDerives.absurd (fuel := 0) hAbs).toBool⟩
  | fact hFact =>
      exact ⟨1, (SearchDerives.fact (fuel := 0) hFact).toBool⟩
  | backchain hImp _ ih =>
      rcases ih with ⟨fuel, hFuel⟩
      exact ⟨fuel + 1, (SearchDerives.backchain hImp (search_derives_of_true hFuel)).toBool⟩
  | andI =>
      rename_i P g₁ g₂ _ _ ih₁ ih₂
      rcases ih₁ with ⟨fuel₁, h₁'⟩
      rcases ih₂ with ⟨fuel₂, h₂'⟩
      let fuel := max fuel₁ fuel₂
      have hd₁' := (search_derives_of_true h₁').monotone (fuel - fuel₁)
      have hd₁ : SearchDerives fuel P g₁ := by
        simpa [fuel, Nat.add_sub_of_le (Nat.le_max_left fuel₁ fuel₂)] using hd₁'
      have hd₂' := (search_derives_of_true h₂').monotone (fuel - fuel₂)
      have hd₂ : SearchDerives fuel P g₂ := by
        simpa [fuel, Nat.add_sub_of_le (Nat.le_max_right fuel₁ fuel₂)] using hd₂'
      exact ⟨fuel + 1, (SearchDerives.andI hd₁ hd₂).toBool⟩
  | orL _ ih =>
      rcases ih with ⟨fuel, hFuel⟩
      exact ⟨fuel + 1, (SearchDerives.orL (search_derives_of_true hFuel)).toBool⟩
  | orR _ ih =>
      rcases ih with ⟨fuel, hFuel⟩
      exact ⟨fuel + 1, (SearchDerives.orR (search_derives_of_true hFuel)).toBool⟩
  | augment _ ih =>
      rcases ih with ⟨fuel, hFuel⟩
      exact ⟨fuel + 1, (SearchDerives.augment (search_derives_of_true hFuel)).toBool⟩
  | generic _ ih =>
      rcases ih with ⟨fuel, hFuel⟩
      exact ⟨fuel + 1, (SearchDerives.generic (search_derives_of_true hFuel)).toBool⟩
  | instance_ hAll _ ih =>
      rcases ih with ⟨fuel, hFuel⟩
      exact ⟨fuel + 1, (SearchDerives.instance_ hAll (search_derives_of_true hFuel)).toBool⟩

end HeytingLean.PTS.BaseExtension
