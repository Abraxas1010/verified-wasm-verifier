import HeytingLean.AsymptoticSafety.BetaFunctions

namespace HeytingLean
namespace AsymptoticSafety
namespace Extraction

structure FloatTruncationScheme where
  newtonStar : Float
  cosmologicalStar : Float
  topExponent : Float
  portalExponent : Float

structure CouplingPointF where
  G_Newton : Float
  cosmological : Float
  topYukawa : Float
  bottomYukawa : Float
  higgsQuartic : Float
  gaugeU1 : Float
  gaugeSU2 : Float
  gaugeSU3 : Float
  portalCoupling : Float

def benchmarkFloat : FloatTruncationScheme where
  newtonStar := 0.71
  cosmologicalStar := 0.19
  topExponent := -1.03
  portalExponent := -1.02

def gravitationalFixedPointF (ts : FloatTruncationScheme) : CouplingPointF where
  G_Newton := ts.newtonStar
  cosmological := ts.cosmologicalStar
  topYukawa := 0.0
  bottomYukawa := 0.0
  higgsQuartic := 0.0
  gaugeU1 := 0.0
  gaugeSU2 := 0.0
  gaugeSU3 := 0.0
  portalCoupling := 0.0

def addF (a b : CouplingPointF) : CouplingPointF where
  G_Newton := a.G_Newton + b.G_Newton
  cosmological := a.cosmological + b.cosmological
  topYukawa := a.topYukawa + b.topYukawa
  bottomYukawa := a.bottomYukawa + b.bottomYukawa
  higgsQuartic := a.higgsQuartic + b.higgsQuartic
  gaugeU1 := a.gaugeU1 + b.gaugeU1
  gaugeSU2 := a.gaugeSU2 + b.gaugeSU2
  gaugeSU3 := a.gaugeSU3 + b.gaugeSU3
  portalCoupling := a.portalCoupling + b.portalCoupling

def smulF (c : Float) (a : CouplingPointF) : CouplingPointF where
  G_Newton := c * a.G_Newton
  cosmological := c * a.cosmological
  topYukawa := c * a.topYukawa
  bottomYukawa := c * a.bottomYukawa
  higgsQuartic := c * a.higgsQuartic
  gaugeU1 := c * a.gaugeU1
  gaugeSU2 := c * a.gaugeSU2
  gaugeSU3 := c * a.gaugeSU3
  portalCoupling := c * a.portalCoupling

def linearizedBetaF (ts : FloatTruncationScheme) (g : CouplingPointF) : CouplingPointF :=
  let fp := gravitationalFixedPointF ts
  {
    G_Newton := (2.0) * (g.G_Newton - fp.G_Newton)
    cosmological := (1.0) * (g.cosmological - fp.cosmological)
    topYukawa := ts.topExponent * (g.topYukawa - fp.topYukawa)
    bottomYukawa := ts.topExponent * (g.bottomYukawa - fp.bottomYukawa)
    higgsQuartic := (-1.01) * (g.higgsQuartic - fp.higgsQuartic)
    gaugeU1 := (-1.0) * (g.gaugeU1 - fp.gaugeU1)
    gaugeSU2 := (-1.0) * (g.gaugeSU2 - fp.gaugeSU2)
    gaugeSU3 := (-1.0) * (g.gaugeSU3 - fp.gaugeSU3)
    portalCoupling := ts.portalExponent * (g.portalCoupling - fp.portalCoupling)
  }

def eulerStepF (dt : Float) (ts : FloatTruncationScheme) (g : CouplingPointF) : CouplingPointF :=
  addF g (smulF dt (linearizedBetaF ts g))

def rk4StepF (dt : Float) (ts : FloatTruncationScheme) (g : CouplingPointF) : CouplingPointF :=
  let k1 := linearizedBetaF ts g
  let k2 := linearizedBetaF ts (addF g (smulF (dt / 2.0) k1))
  let k3 := linearizedBetaF ts (addF g (smulF (dt / 2.0) k2))
  let k4 := linearizedBetaF ts (addF g (smulF dt k3))
  let weighted := addF k1 (addF (smulF 2.0 k2) (addF (smulF 2.0 k3) k4))
  addF g (smulF (dt / 6.0) weighted)

def demoStart : CouplingPointF where
  G_Newton := 0.90
  cosmological := 0.25
  topYukawa := 0.50
  bottomYukawa := 0.10
  higgsQuartic := 0.05
  gaugeU1 := 0.08
  gaugeSU2 := 0.15
  gaugeSU3 := 0.40
  portalCoupling := 0.07

def demoRK4 : CouplingPointF :=
  rk4StepF 0.10 benchmarkFloat demoStart

end Extraction
end AsymptoticSafety
end HeytingLean
