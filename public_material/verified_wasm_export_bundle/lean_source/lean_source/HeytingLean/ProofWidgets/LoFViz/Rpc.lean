import Lean
import ProofWidgets
import HeytingLean.ProofWidgets.LoFViz.State
import HeytingLean.ProofWidgets.LoFViz.Kernel
import HeytingLean.ProofWidgets.LoFViz.Render.Router
import HeytingLean.ProofWidgets.LoFViz.Render.Types
import HeytingLean.ProofWidgets.LoFViz.Proof.Core
import HeytingLean.ProofWidgets.LoFViz.Proof.Graph

open Std
open Lean
open Lean Server

namespace HeytingLean
namespace ProofWidgets
namespace LoFViz

/-- Request payload for fetching a proof graph. -/
structure GraphRequest where
  constant : String
  fuel? : Option Nat := none
  deriving Inhabited, Repr, ToJson, FromJson, Server.RpcEncodable

/-- Response payload containing a proof graph encoded as JSON. -/
structure GraphResponse where
  constant : String
  graph : Json
  deriving Inhabited, Repr, ToJson, FromJson, Server.RpcEncodable

/-- In-memory cache for scene state. This persists for the lifetime of the Lean server. -/
initialize sceneCache : IO.Ref (Std.HashMap String State) ← IO.mkRef {}

/-- Load a specific scene, falling back to the initial state. -/
def loadState (sceneId : String) : RequestM State := do
  let cache : Std.HashMap String State ← sceneCache.get
  if h : sceneId ∈ cache then
    pure <| cache.get sceneId h
  else
    pure <| initialState sceneId

/-- Persist the updated scene state in the cache. -/
def saveState (st : State) : RequestM Unit := do
  sceneCache.modify fun m => m.insert st.sceneId st

/-- RPC entry point consumed by the widget. -/
@[server_rpc_method]
def apply (evt : Event) : RequestM (RequestTask Render.ApplyResponse) :=
  RequestM.asTask do
    let s ← loadState evt.sceneId
    let s' := Stepper.applyEvent s evt
    let kernel := KernelData.fromState s'
    let rendered := Render.route s' kernel
    let _ ← saveState s'
    pure
      { render :=
          { sceneId := s'.sceneId
            stage := toString s'.dialStage
            lens := toString s'.lens
            svg := rendered.svg
            hud := rendered.hud }
        proof := rendered.certificates }

@[server_rpc_method]
def graphOfConstant (req : GraphRequest) : RequestM (RequestTask GraphResponse) := do
  let doc ← RequestM.readDoc
  let task := doc.cmdSnaps.waitAll
  RequestM.mapTaskCostly task fun (snaps, _) => do
    let some snap := snaps.reverse.head?
      | throw <| RequestError.internalError "No elaboration snapshots available."
    let some name := Proof.nameFromString? req.constant
      | throw <| RequestError.invalidParams s!"Unknown constant name '{req.constant}'."
    RequestM.runCoreM snap do
      let bundle ← bundleOfConstantCore name (req.fuel?.getD defaultFuel)
      return { constant := req.constant, graph := bundle.graph.toJson }

end LoFViz
end ProofWidgets
end HeytingLean
