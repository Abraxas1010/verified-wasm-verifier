import HeytingLean.Embeddings.CoreLenses
import HeytingLean.Embeddings.Presets
import HeytingLean.Embeddings.LensUnification

namespace HeytingLean.Tests.Embeddings.LensExpansionSanity

open HeytingLean.Embeddings

/-! ## New variant existence -/
#check CoreLensTag.fiberBundle
#check CoreLensTag.gauge
#check CoreLensTag.riemannian
#check CoreLensTag.symplectic
#check CoreLensTag.persistence
#check CoreLensTag.mapper
#check CoreLensTag.morse
#check CoreLensTag.coalgebra
#check CoreLensTag.stream
#check CoreLensTag.automaton
#check CoreLensTag.wasserstein
#check CoreLensTag.ot
#check CoreLensTag.fourier
#check CoreLensTag.wavelet
#check CoreLensTag.laplacian
#check CoreLensTag.operad
#check CoreLensTag.profunctor
#check CoreLensTag.kTheory
#check CoreLensTag.simplicial
#check CoreLensTag.topos
#check CoreLensTag.derivedCat
#check CoreLensTag.kolmogorov
#check CoreLensTag.fisher
#check CoreLensTag.gameTheory
#check CoreLensTag.auction
#check CoreLensTag.renormGroup
#check CoreLensTag.conformal
#check CoreLensTag.petriNet
#check CoreLensTag.symbDyn

/-! ## Metadata correctness -/
example : CoreLensTag.nameOf .fiberBundle = "Fiber Bundle" := rfl
example : CoreLensTag.idOf .gauge = "core.gauge" := rfl
example : CoreLensTag.nameOf .persistence = "Persistent Homology" := rfl
example : CoreLensTag.idOf .fourier = "core.fourier" := rfl
example : CoreLensTag.nameOf .operad = "Operad" := rfl
example : CoreLensTag.idOf .topos = "core.topos" := rfl
example : CoreLensTag.nameOf .kolmogorov = "Kolmogorov Complexity" := rfl
example : CoreLensTag.idOf .gameTheory = "core.gameTheory" := rfl
example : CoreLensTag.nameOf .conformal = "Conformal Field" := rfl
example : CoreLensTag.idOf .petriNet = "core.petriNet" := rfl

/-! ## Category assignments -/
example : CoreLensTag.categoryOf .fiberBundle = .diffGeometry := rfl
example : CoreLensTag.categoryOf .persistence = .tda := rfl
example : CoreLensTag.categoryOf .coalgebra = .coalgebraic := rfl
example : CoreLensTag.categoryOf .wasserstein = .optTransport := rfl
example : CoreLensTag.categoryOf .fourier = .signal := rfl
example : CoreLensTag.categoryOf .operad = .algebraic := rfl
example : CoreLensTag.categoryOf .simplicial = .topological := rfl
example : CoreLensTag.categoryOf .kolmogorov = .information := rfl
example : CoreLensTag.categoryOf .gameTheory = .economic := rfl
example : CoreLensTag.categoryOf .renormGroup = .physical := rfl
example : CoreLensTag.categoryOf .petriNet = .process := rfl

/-! ## Count consistency -/
example : CoreLensTag.count = 100 := rfl
example : CoreLensTag.all.length = 100 := by native_decide

/-! ## New lenses in `all` list -/
example : CoreLensTag.fiberBundle ∈ CoreLensTag.all := by native_decide
example : CoreLensTag.persistence ∈ CoreLensTag.all := by native_decide
example : CoreLensTag.coalgebra ∈ CoreLensTag.all := by native_decide
example : CoreLensTag.wasserstein ∈ CoreLensTag.all := by native_decide
example : CoreLensTag.fourier ∈ CoreLensTag.all := by native_decide
example : CoreLensTag.operad ∈ CoreLensTag.all := by native_decide
example : CoreLensTag.topos ∈ CoreLensTag.all := by native_decide
example : CoreLensTag.kolmogorov ∈ CoreLensTag.all := by native_decide
example : CoreLensTag.gameTheory ∈ CoreLensTag.all := by native_decide
example : CoreLensTag.conformal ∈ CoreLensTag.all := by native_decide
example : CoreLensTag.petriNet ∈ CoreLensTag.all := by native_decide

/-! ## Generic transport works with new lenses -/
def trivialExpanded :
    GenericCrossLensTransport.GenericTransport CoreLensTag
      (fun _ => Nat) Nat where
  toPlato _ x := x
  fromPlato _ p := p
  rt1 _ _ := rfl
  rt2 _ _ := rfl

example (x : Nat) :
    trivialExpanded.forward CoreLensTag.fourier CoreLensTag.wavelet x = x := rfl
example (x : Nat) :
    trivialExpanded.forward CoreLensTag.persistence CoreLensTag.coalgebra x = x := rfl
example (x : Nat) :
    trivialExpanded.forward CoreLensTag.topos CoreLensTag.operad x = x := rfl

/-! ## Preset smoke checks -/
#check LensPreset.diffGeometry
#check LensPreset.tda
#check LensPreset.transport
#check LensPreset.signalProcessing
#check LensPreset.automataTheory
#check LensPreset.games

example : (LensPreset.diffGeometry).contains .fiberBundle = true := by native_decide
example : (LensPreset.tda).contains .persistence = true := by native_decide
example : (LensPreset.transport).contains .wasserstein = true := by native_decide
example : (LensPreset.signalProcessing).contains .fourier = true := by native_decide
example : (LensPreset.automataTheory).contains .automaton = true := by native_decide
example : (LensPreset.games).contains .gameTheory = true := by native_decide

/-! ## Dynamic selection -/
example : (selectLensesFor "tda").contains .persistence = true := by native_decide
example : (selectLensesFor "geometry").contains .fiberBundle = true := by native_decide
example : (selectLensesFor "signal").contains .fourier = true := by native_decide
example : (selectLensesFor "games").contains .gameTheory = true := by native_decide

/-! ## Backwards compatibility: old lenses unchanged -/
example : CoreLensTag.nameOf .omega = "Omega (Eigenform)" := rfl
example : CoreLensTag.idOf .tropical = "core.tropical" := rfl
example : CoreLensTag.categoryOf .zkProof = .crypto := rfl

end HeytingLean.Tests.Embeddings.LensExpansionSanity
