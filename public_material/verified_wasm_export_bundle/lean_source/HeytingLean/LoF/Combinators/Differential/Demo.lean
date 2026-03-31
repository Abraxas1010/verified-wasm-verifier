import HeytingLean.LoF.Combinators.Differential.GradientDescent

/-!
# Differential combinators: demo data (compile-time)

This module is a library-side companion to the `differential_sky_demo` executable.
It provides small example datasets/configs for the compute backend.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Differential
namespace Demo

def toyParams : List Comb :=
  [.K, .S]

def toyX : Compute.FSum :=
  Compute.single .Y

def toyY : Compute.FSum :=
  Compute.add (Compute.smul 2 (Compute.single (.app .K .Y))) (Compute.single (.app .S .Y))

def toyExamples : List Compute.IOExample :=
  [{ input := toyX, expected := toyY }]

def toyConfig : Compute.GDConfig :=
  { learningRate := (1 : Rat) / 5
    iterations := 12
    params := toyParams }

end Demo
end Differential
end Combinators
end LoF
end HeytingLean
