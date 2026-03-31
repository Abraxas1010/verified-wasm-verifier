/-
  Verified Particle Lenia - Basic Definitions

  This file establishes the foundational types and fixed-point arithmetic
  for Particle Lenia simulation. We use fixed-point representation to
  enable verified compilation through HeytingLean's LambdaIR pipeline.

  Reference: https://google-research.github.io/self-organising-systems/particle-lenia/
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.MinMax

namespace HeytingLean
namespace ParticleLenia

/-! ## Fixed-Point Arithmetic

We represent real numbers as integers scaled by `SCALE`.
For example, with SCALE = 1000:
  - 1.5 is represented as 1500
  - 0.001 is represented as 1
  - -2.7 is represented as -2700

This allows verified compilation through the Nat fragment system.
-/

/-- Scale factor for fixed-point representation (3 decimal places) -/
def SCALE : Int := 1000

/-- Fixed-point number: an integer with implicit scale -/
structure FixedPoint where
  raw : Int
  deriving Repr, DecidableEq, Inhabited

namespace FixedPoint

/-- Zero in fixed-point -/
def zero : FixedPoint := ⟨0⟩

/-- One in fixed-point -/
def one : FixedPoint := ⟨SCALE⟩

/-- Create from integer -/
def fromInt (n : Int) : FixedPoint := ⟨n * SCALE⟩

/-- Addition of fixed-point numbers -/
def add (a b : FixedPoint) : FixedPoint := ⟨a.raw + b.raw⟩

/-- Subtraction of fixed-point numbers -/
def sub (a b : FixedPoint) : FixedPoint := ⟨a.raw - b.raw⟩

/-- Multiplication (requires division by SCALE to maintain precision) -/
def mul (a b : FixedPoint) : FixedPoint := ⟨(a.raw * b.raw) / SCALE⟩

/-- Division (requires multiplication by SCALE first) -/
def div (a b : FixedPoint) : FixedPoint :=
  if b.raw = 0 then ⟨0⟩ else ⟨(a.raw * SCALE) / b.raw⟩

/-- Negation -/
def neg (a : FixedPoint) : FixedPoint := ⟨-a.raw⟩

/-- Comparison -/
def le (a b : FixedPoint) : Bool := a.raw ≤ b.raw

/-- Maximum of two fixed-point numbers -/
def max (a b : FixedPoint) : FixedPoint := ⟨if a.raw ≥ b.raw then a.raw else b.raw⟩

/-- Minimum of two fixed-point numbers -/
def min (a b : FixedPoint) : FixedPoint := ⟨if a.raw ≤ b.raw then a.raw else b.raw⟩

/-- Absolute value -/
def abs (a : FixedPoint) : FixedPoint := ⟨Int.natAbs a.raw⟩

/-- Square (a * a) -/
def sq (a : FixedPoint) : FixedPoint := mul a a

instance : Add FixedPoint := ⟨add⟩
instance : Sub FixedPoint := ⟨sub⟩
instance : Mul FixedPoint := ⟨mul⟩
instance : Div FixedPoint := ⟨div⟩
instance : Neg FixedPoint := ⟨neg⟩
instance : LE FixedPoint := ⟨fun a b => a.raw ≤ b.raw⟩
instance : LT FixedPoint := ⟨fun a b => a.raw < b.raw⟩
instance : Max FixedPoint := ⟨max⟩
instance : Min FixedPoint := ⟨min⟩

end FixedPoint

/-! ## 2D Vector Type -/

/-- A 2D vector in fixed-point representation -/
structure Vec2 where
  x : FixedPoint
  y : FixedPoint
  deriving Repr, DecidableEq, Inhabited

namespace Vec2

def zero : Vec2 := ⟨FixedPoint.zero, FixedPoint.zero⟩

def add (a b : Vec2) : Vec2 := ⟨a.x + b.x, a.y + b.y⟩

def sub (a b : Vec2) : Vec2 := ⟨a.x - b.x, a.y - b.y⟩

def scale (s : FixedPoint) (v : Vec2) : Vec2 := ⟨s * v.x, s * v.y⟩

def neg (v : Vec2) : Vec2 := ⟨-v.x, -v.y⟩

/-- Squared Euclidean distance (avoids sqrt) -/
def distSq (a b : Vec2) : FixedPoint :=
  let dx := a.x - b.x
  let dy := a.y - b.y
  dx.sq + dy.sq

instance : Add Vec2 := ⟨add⟩
instance : Sub Vec2 := ⟨sub⟩
instance : Neg Vec2 := ⟨neg⟩

end Vec2

/-! ## Particle Lenia Parameters -/

/-- Parameters for Particle Lenia simulation -/
structure LeniaParams where
  /-- Kernel mean (μ_K) - typical value: 4.0 -/
  mu_k : FixedPoint
  /-- Kernel std dev (σ_K) - typical value: 1.0 -/
  sigma_k : FixedPoint
  /-- Growth mean (μ_G) - typical value: 0.6 -/
  mu_g : FixedPoint
  /-- Growth std dev (σ_G) - typical value: 0.15 -/
  sigma_g : FixedPoint
  /-- Repulsion coefficient (c_rep) - typical value: 1.0 -/
  c_rep : FixedPoint
  /-- Time step (dt) - typical value: 0.1 -/
  dt : FixedPoint
  deriving Repr

/-- Default parameters from Particle Lenia paper -/
def LeniaParams.default : LeniaParams where
  mu_k := ⟨4000⟩      -- 4.0
  sigma_k := ⟨1000⟩   -- 1.0
  mu_g := ⟨600⟩       -- 0.6
  sigma_g := ⟨150⟩    -- 0.15
  c_rep := ⟨1000⟩     -- 1.0
  dt := ⟨100⟩         -- 0.1

/-! ## Particle System -/

/-- A single particle with position -/
structure Particle where
  pos : Vec2
  deriving Repr, DecidableEq, Inhabited

/-- A configuration of particles -/
abbrev ParticleSystem (n : Nat) := Fin n → Particle

end ParticleLenia
end HeytingLean
