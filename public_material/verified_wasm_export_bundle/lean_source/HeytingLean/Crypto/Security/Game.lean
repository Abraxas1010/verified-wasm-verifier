namespace HeytingLean
namespace Crypto
namespace Security

/-- Minimal shared game surface for native crypto security statements. -/
structure Game where
  State : Type
  Transcript : Type
  Challenge : Type
  Output : Type
  init : State
  transcript : State → Transcript
  challenge : State → Challenge
  output : State → Output

end Security
end Crypto
end HeytingLean
