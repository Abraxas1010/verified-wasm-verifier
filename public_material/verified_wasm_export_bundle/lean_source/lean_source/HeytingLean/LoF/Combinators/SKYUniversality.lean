import HeytingLean.Computation.YWitness.ProductiveSequence

namespace HeytingLean.LoF.Combinators.SKYUniversality

open HeytingLean.LoF

/-- An explicit self-referential target language for the SKY lane: a base term together with any
finite number of `Y`-unfolding wrappers.
-/
inductive SelfProgram where
  | base (seed : Comb)
  | unfold (program : SelfProgram)
  deriving Repr, DecidableEq

/-- Encode the explicit self-program syntax into the repo's SKY term language. -/
def encode : SelfProgram → Comb
  | .base seed => seed
  | .unfold program => Comb.app .Y (encode program)

/-- Decode a SKY term back into the explicit self-program fragment by peeling leading `Y` shells.
This is the honest completeness target for this phase: the self-referential SKY fragment, not
global Turing completeness.
-/
def decode : Comb → SelfProgram
  | .app .Y term => .unfold (decode term)
  | term => .base term

/-- The canonical program with `n` explicit `Y`-unfolds over a seed. -/
def repeatedUnfold (seed : Comb) : Nat → SelfProgram
  | 0 => .base seed
  | n + 1 => .unfold (repeatedUnfold seed n)

theorem encode_decode (term : Comb) :
    encode (decode term) = term := by
  induction term with
  | K =>
      rfl
  | S =>
      rfl
  | Y =>
      rfl
  | app f a ihf iha =>
      cases f with
      | K =>
          rfl
      | S =>
          rfl
      | Y =>
          simpa [encode, decode] using congrArg (Comb.app .Y) iha
      | app f₁ f₂ =>
          rfl

/-- Encoded self-programs roundtrip exactly on the SKY side. -/
theorem decode_encode (program : SelfProgram) :
    encode (decode (encode program)) = encode program := by
  exact encode_decode (encode program)

theorem encode_repeatedUnfold (seed : Comb) (n : Nat) :
    encode (repeatedUnfold seed n) =
      HeytingLean.Computation.YWitness.yProductiveSequence seed n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [repeatedUnfold, encode, HeytingLean.Computation.YWitness.yProductiveSequence, ih]

/-- Soundness for the explicit universality target: the encoded self-program unfolds by the SKY
`Y` rule exactly as intended.
-/
theorem encode_unfold_step (program : SelfProgram) :
    Comb.Step (encode (.unfold program))
      (Comb.app (encode program) (encode (.unfold program))) := by
  simpa [encode] using Comb.Step.Y_rule (encode program)

/-- Every target self-program is represented by a SKY term, and that term is stable under the
decode-then-encode roundtrip.
-/
theorem universal_for_selfPrograms (program : SelfProgram) :
    ∃ term : Comb, encode (decode term) = term ∧ encode program = term := by
  exact ⟨encode program, decode_encode program, rfl⟩

/-- Soundness/completeness viewed from the SKY side: every SKY term lies in the image of the
explicit self-program fragment under `encode`.
-/
theorem encoded_fragment_complete (term : Comb) :
    ∃ program : SelfProgram, encode program = term := by
  exact ⟨decode term, encode_decode term⟩

end HeytingLean.LoF.Combinators.SKYUniversality
