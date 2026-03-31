import HeytingLean.Genesis.EigenformSoup.Bridge
import HeytingLean.Genesis.EigenformSoup.Extraction
import HeytingLean.Topology.Knot.BracketMathlibReidemeisterR3

/-!
# Genesis.EigenformSoup.PhaseGates

WS9 gate contracts:
- boundary gate,
- external R3 closure gate,
- extraction compile gate.
-/

namespace HeytingLean.Genesis.EigenformSoup

/-- Evidence object certifying theorem-level R3 closure availability. -/
structure R3ClosureEvidence : Type where
  bridgeInvariant :
    ∀ {g gL gR : HeytingLean.Topology.Knot.PDGraph} {x u w : Nat}
      (_hLeft : HeytingLean.Topology.Knot.Reidemeister.r3BraidLeft g x u w = .ok gL)
      (_hRight : HeytingLean.Topology.Knot.Reidemeister.r3BraidRight g x u w = .ok gR)
      (_hBridge : HeytingLean.Topology.Knot.Kauffman.R3SkeinBridgeWitness g gL gR x u w),
      HeytingLean.Topology.Knot.Kauffman.bracketGraphML gL =
        HeytingLean.Topology.Knot.Kauffman.bracketGraphML gR

/-- Canonical R3 closure certificate from the bridged endpoint theorem. -/
noncomputable def theoremR3ClosureEvidence : R3ClosureEvidence :=
  { bridgeInvariant := by
      intro g gL gR x u w hLeft hRight hBridge
      exact HeytingLean.Topology.Knot.Kauffman.bracketGraphML_r3_invariant_of_bridge_witness
        (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
        hLeft hRight hBridge }

/-- External gate inputs required before promoting LES integration claims. -/
structure ExternalGates where
  boundaryNoReverseImport : Prop
  r3Evidence : Option R3ClosureEvidence := none

namespace ExternalGates

/-- R3 closure is verified exactly when a concrete evidence object is supplied. -/
def r3ClosureVerified (ext : ExternalGates) : Prop :=
  ∃ ev, ext.r3Evidence = some ev

theorem r3ClosureVerified_of_some
    (ext : ExternalGates)
    {ev : R3ClosureEvidence}
    (h : ext.r3Evidence = some ev) :
    ext.r3ClosureVerified :=
  ⟨ev, h⟩

theorem not_r3ClosureVerified_of_none
    (ext : ExternalGates)
    (h : ext.r3Evidence = none) :
    ¬ ext.r3ClosureVerified := by
  intro hVerified
  rcases hVerified with ⟨ev, hev⟩
  rw [h] at hev
  cases hev

end ExternalGates

/-- Internal extraction gate for milestone-1 (compile proof-of-build). -/
def extractionCompileGate (nuc : SoupNucleus) (cfg : SoupConfig) : Prop :=
  (compileSoupCAB nuc cfg).allStagesCorrect = true

/-- Internal extraction semantic-parity gate for milestone-1 payload preservation. -/
def extractionSemanticParityGate (nuc : SoupNucleus) (cfg : SoupConfig) : Prop :=
  CHasStabilizedCount
    (compileSoupCAB nuc cfg).cCode
    ((runSoup nuc cfg).stabilized.length)

/-- Combined WS9 promotion gate. -/
def ws9PromotionReady (nuc : SoupNucleus) (cfg : SoupConfig) (ext : ExternalGates) : Prop :=
  ext.boundaryNoReverseImport ∧
    ext.r3ClosureVerified ∧
    extractionCompileGate nuc cfg ∧
    extractionSemanticParityGate nuc cfg

/-- Extraction gate is discharged by the compile theorem in WS8 scaffold. -/
theorem extractionCompileGate_holds (nuc : SoupNucleus) (cfg : SoupConfig) :
    extractionCompileGate nuc cfg := by
  exact compileSoupCAB_allStagesCorrect nuc cfg

/-- Extraction semantic-parity gate is discharged by the WS8 payload theorem. -/
theorem extractionSemanticParityGate_holds (nuc : SoupNucleus) (cfg : SoupConfig) :
    extractionSemanticParityGate nuc cfg := by
  exact compileSoupCAB_cCode_has_stabilizedCount nuc cfg

/-- If external gates are provided, WS9 promotion-ready follows directly. -/
theorem ws9PromotionReady_of_external
    (nuc : SoupNucleus)
    (cfg : SoupConfig)
    (ext : ExternalGates)
    (hBoundary : ext.boundaryNoReverseImport)
    (hR3 : ext.r3ClosureVerified) :
    ws9PromotionReady nuc cfg ext := by
  exact
    ⟨hBoundary, hR3, extractionCompileGate_holds nuc cfg,
      extractionSemanticParityGate_holds nuc cfg⟩

/-- Fail-closed theorem: without R3 evidence, WS9 promotion is blocked. -/
theorem ws9Promotion_not_ready_without_r3
    (nuc : SoupNucleus)
    (cfg : SoupConfig)
    (ext : ExternalGates)
    (hNone : ext.r3Evidence = none) :
    ¬ ws9PromotionReady nuc cfg ext := by
  intro hReady
  exact (ExternalGates.not_r3ClosureVerified_of_none ext hNone) hReady.2.1

end HeytingLean.Genesis.EigenformSoup
