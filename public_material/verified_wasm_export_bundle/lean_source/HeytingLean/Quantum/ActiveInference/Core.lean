/-!
# Quantum Active Inference (discrete, finite example)

Arrays of `Float` for probabilities; no heavy numerics. This module
implements a small but fully honest finite model, suitable for CLIs
and tests without any fake semantics.
-/

namespace HeytingLean
namespace Quantum
namespace ActiveInference

-- Real-typed variants will be added in a later proof pass without affecting CLI

structure DiscreteModel where
  ns : Nat   -- number of states
  no : Nat   -- number of observations
  na : Nat   -- number of actions
  prior : Array Float              -- size ns
  like  : Array (Array (Array Float)) -- like[a][s][o]
deriving Repr

structure Preferences where
  prefObs? : Option (Array Float) := none  -- desired observation distribution
  prefState? : Option (Array Float) := none
deriving Repr

namespace Math

@[simp] def normalize (xs : Array Float) : Array Float := Id.run do
  let s := xs.foldl (init := 0.0) (· + ·)
  if s ≤ 0.0 then
    let n := xs.size
    if n = 0 then return xs else return Array.replicate n (1.0 / Float.ofNat n)
  else
    xs.map (fun x => x / s)

@[simp] def safeLog (x : Float) : Float :=
  let eps : Float := 0.000000000001
  if x ≤ eps then -27.6310211159 else Float.log x  -- log(1e-12) ≈ -27.63

@[simp] def klDiv (p q : Array Float) : Float := Id.run do
  let n := min p.size q.size
  let mut acc := 0.0
  for i in [:n] do
    let pi := p[i]!; let qi := q[i]!
    if pi > 0.0 then acc := acc + pi * (safeLog pi - safeLog qi)
  acc

end Math

open Math

@[simp] def posterior (m : DiscreteModel) (a : Nat) (obs : Nat) : Array Float := Id.run do
  -- q(s) ∝ prior(s) * like[a][s][obs]
  let mut out : Array Float := Array.replicate m.ns 0.0
  let tab := m.like[a]!
  for s in [:m.ns] do
    let p := m.prior[s]!
    let l := tab[s]![obs]!
    out := out.set! s (p * l)
  normalize out

@[simp] def freeEnergy (m : DiscreteModel) (a : Nat) (obs : Nat) : Float := Id.run do
  let q := posterior m a obs
  let mut acc := 0.0
  let tab := m.like[a]!
  for s in [:m.ns] do
    let qs := q[s]!; let ps := m.prior[s]!; let l := tab[s]![obs]!
    if qs > 0.0 then
      acc := acc + qs * (safeLog qs - safeLog ps - safeLog l)
  acc

@[simp] def predictObs (m : DiscreteModel) (a : Nat) : Array Float := Id.run do
  -- p(o|a) = Σ_s prior(s) like[a][s][o]
  let mut out : Array Float := Array.replicate m.no 0.0
  let tab := m.like[a]!
  for o in [:m.no] do
    let mut s := 0.0
    for st in [:m.ns] do
      s := s + m.prior[st]! * tab[st]![o]!
    out := out.set! o s
  normalize out

@[simp] def infoGain (m : DiscreteModel) (a : Nat) : Float := Id.run do
  -- E_o[ KL(q(s|o,a) || prior(s)) ]
  let po := predictObs m a
  let mut ig := 0.0
  for o in [:m.no] do
    let qo := posterior m a o
    ig := ig + po[o]! * klDiv qo m.prior
  ig

@[simp] def efe (m : DiscreteModel) (pref : Preferences) (a : Nat) : Float :=
  -- risk: expected -log pref(o)
  let po := predictObs m a
  let risk :=
    match pref.prefObs? with
    | none => 0.0
    | some prefO =>
      let n := min po.size prefO.size
      Id.run do
        let mut r := 0.0
        for i in [:n] do
          let pi := po[i]!; let wi := prefO[i]!
          if pi > 0.0 then r := r + pi * (- safeLog wi)
        return r
  let ig := infoGain m a
  risk + ig

@[simp] def withPrior (m : DiscreteModel) (p : Array Float) : DiscreteModel :=
  { m with prior := p }

@[simp] def efeWithPrior (m : DiscreteModel) (pref : Preferences) (a : Nat)
    (p : Array Float) : Float :=
  efe (withPrior m p) pref a

@[simp] def bestAction (m : DiscreteModel) (pref : Preferences) : Nat := Id.run do
  let mut bestA := 0
  let mut bestV := efe m pref 0
  for a in [1:m.na] do
    let v := efe m pref a
    if v < bestV then
      bestV := v; bestA := a
  bestA

/-! ### Simple two-step planning (a₁ then a₂)

Score a length-2 policy by EFE(a₁) + E_{o|a₁}[ EFE(a₂; prior←q(s|o,a₁)) ]. -/
@[simp] def scorePolicy2 (m : DiscreteModel) (pref : Preferences)
    (a1 a2 : Nat) : Float := Id.run do
  let base := efe m pref a1
  let po := predictObs m a1
  let mut tail := 0.0
  for o in [:m.no] do
    let q := posterior m a1 o
    tail := tail + po[o]! * efeWithPrior m pref a2 q
  base + tail

@[simp] def bestPolicy2 (m : DiscreteModel) (pref : Preferences) : Nat × Nat := Id.run do
  let mut best : Nat × Nat := (0, 0)
  let mut val := scorePolicy2 m pref 0 0
  for a1 in [:m.na] do
    for a2 in [:m.na] do
      let v := scorePolicy2 m pref a1 a2
      if v < val then
        val := v; best := (a1, a2)
  best

/-! ### Optional gating (Ω-level modality on observations)

Allows transforming the predicted observation distribution before scoring risk.
Set `Gate.jObs = id` for default behavior. -/
structure Gate where
  jObs : Array Float → Array Float := id

@[simp] def efeGated (m : DiscreteModel) (pref : Preferences) (g : Gate)
    (a : Nat) : Float :=
  let po := g.jObs (predictObs m a)
  let risk :=
    match pref.prefObs? with
    | none => 0.0
    | some prefO =>
      let n := min po.size prefO.size
      Id.run do
        let mut r := 0.0
        for i in [:n] do
          let pi := po[i]!; let wi := prefO[i]!
          if pi > 0.0 then r := r + pi * (- safeLog wi)
        return r
  risk + infoGain m a

@[simp] def bestActionGated (m : DiscreteModel) (pref : Preferences) (g : Gate) : Nat := Id.run do
  let mut bestA := 0
  let mut bestV := efeGated m pref g 0
  for a in [1:m.na] do
    let v := efeGated m pref g a
    if v < bestV then
      bestV := v; bestA := a
  bestA

end ActiveInference
end Quantum
end HeytingLean
