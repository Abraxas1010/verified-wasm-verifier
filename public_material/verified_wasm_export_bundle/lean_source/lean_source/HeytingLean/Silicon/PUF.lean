import HeytingLean.Silicon.Signature

namespace HeytingLean
namespace Silicon

noncomputable section

open scoped BigOperators

open HeytingLean.Probability.InfoTheory

universe u

/-- A minimal PUF interface: each device maps each challenge to a distribution of responses. -/
abbrev PUF (Dev Chal Resp : Type u) [Fintype Chal] [Fintype Resp] :=
  Dev → Chal → FinDist Resp

namespace PUF

variable {Dev Chal Resp : Type u} [Fintype Chal] [Fintype Resp]

/-- Two devices are distinguishable at a challenge if their response distributions differ. -/
def DistinguishableAt (F : PUF Dev Chal Resp) (d₁ d₂ : Dev) (c : Chal) : Prop :=
  F d₁ c ≠ F d₂ c

theorem exists_singleton_response_prob_ne [DecidableEq Resp]
    (F : PUF Dev Chal Resp) (d₁ d₂ : Dev) (c : Chal)
    (h : DistinguishableAt (Dev := Dev) (Chal := Chal) (Resp := Resp) F d₁ d₂ c) :
    ∃ r : Resp,
      FinDist.probEvent (F d₁ c) (fun x : Resp => x = r) ≠
        FinDist.probEvent (F d₂ c) (fun x : Resp => x = r) := by
  classical
  simpa [DistinguishableAt] using
    (Signature.exists_singleton_prob_ne (α := Resp) (P := F d₁ c) (Q := F d₂ c) h)

end PUF

end

end Silicon
end HeytingLean
