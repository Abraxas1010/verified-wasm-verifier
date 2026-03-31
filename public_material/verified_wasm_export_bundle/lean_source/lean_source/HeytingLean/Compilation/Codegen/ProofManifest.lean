import HeytingLean.Compilation.LambdaIR.Layout
import Mathlib.Data.List.Basic

/-!
# Proof manifest serialization (scaffold)

The unified code generator emits a small JSON-ish manifest listing layout-operation
certificates (operation name + proof hash).
-/

namespace HeytingLean
namespace Compilation
namespace Codegen

open HeytingLean.Compilation.LambdaIR

private def commaSepLines (xs : List String) : String :=
  String.intercalate ",\n    " xs

def certificateJson (c : LayoutCertificate) : String :=
  "{\"op\": \"" ++ c.operation ++ "\", \"hash\": \"" ++ c.proofHash ++ "\"}"

def proofManifestJson (moduleName : String) (certs : List LayoutCertificate) : String :=
  let entries :=
    match certs with
    | [] => ""
    | _ => commaSepLines (certs.map certificateJson)
  "{\n" ++
    "  \"module\": \"" ++ moduleName ++ "\",\n" ++
    "  \"certificates\": [\n" ++
    "    " ++ entries ++ "\n" ++
    "  ]\n" ++
    "}\n"

end Codegen
end Compilation
end HeytingLean
