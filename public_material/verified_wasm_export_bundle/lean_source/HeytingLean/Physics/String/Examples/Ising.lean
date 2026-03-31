import HeytingLean.Physics.String.ComplexF

/-
Ising model (c=1/2) modular S and T (3×3) on a 3-vector of complex coefficients.
S is real; T phases are exp(2π i (h - c/24)) for h ∈ {0, 1/2, 1/16}.
This is a compile-friendly numeric demo, not a proof of modular identities.
-/

namespace HeytingLean
namespace Physics
namespace String
namespace Examples
namespace Ising

open HeytingLean.Physics.String

abbrev Vec3 := Array CFloat

private def sqrt2Over2 : Float := 0.7071067811865476

@[simp] def S : Array (Array Float) :=
  #[(#[(1.0/2.0), (1.0/2.0), sqrt2Over2]),
    (#[(1.0/2.0), (1.0/2.0), -sqrt2Over2]),
    (#[(sqrt2Over2), (-sqrt2Over2), 0.0])]

@[simp] def Tphases : Array Float :=
  -- θ_a = 2π (h_a - c/24) with c=1/2, h ∈ {0, 1/2, 1/16}
  let twoPi := 6.2831853071795864769
  let c24 := 1.0 / 48.0
  let θ0 := twoPi * (0.0 - c24)
  let θe := twoPi * (0.5 - c24)
  let θs := twoPi * (1.0/16.0 - c24)
  #[θ0, θe, θs]

@[simp] def applyS (v : Vec3) : Vec3 := Id.run do
  let M := S
  let mut out : Vec3 := #[]
  for i in [:3] do
    let row := M[i]!
    let mut acc : CFloat := {re := 0.0, im := 0.0}
    for j in [:3] do
      let a := row[j]!
      let x := v[j]!
      acc := CFloat.add acc (CFloat.scale a x)
    out := out.push acc
  out

@[simp] def applyT (v : Vec3) : Vec3 := Id.run do
  let θs := Tphases
  let mut out : Vec3 := #[]
  for i in [:3] do
    let θ := θs[i]!
    let phase := CFloat.unitPhase θ
    let x := v[i]!
    out := out.push (CFloat.mul phase x)
  out

end Ising
end Examples
end String
end Physics
end HeytingLean

