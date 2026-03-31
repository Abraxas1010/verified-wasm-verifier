import ProofWidgets

namespace HeytingLean
namespace ProofWidgets
namespace LoFViz

/-- Props accepted by the LoF visualization widget. -/
structure WidgetProps where
  sceneId : String := "demo"
  clientVersion : String := "0.1.0"
  deriving _root_.Lean.Server.RpcEncodable

/-- JavaScript-backed widget component powered by the React client. -/
@[widget_module]
def LoFVisualAppWidget : _root_.ProofWidgets.Component WidgetProps where
  javascript := include_str "LoFVisualApp.js"

end LoFViz
end ProofWidgets
end HeytingLean

