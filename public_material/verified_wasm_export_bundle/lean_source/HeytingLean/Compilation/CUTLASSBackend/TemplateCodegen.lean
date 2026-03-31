import HeytingLean.Compilation.CUTLASSBackend.KernelPatterns
import HeytingLean.Compilation.LambdaIR.Layout
import Mathlib.Data.List.Basic

/-!
# CUTLASS C++ template code generation (scaffold)

Generates CUTLASS/CuTe-flavored C++ header text containing `cute::Layout` aliases.

This is *text-only* generation; it does not compile or link any CUDA code.
-/

namespace HeytingLean
namespace Compilation
namespace CUTLASSBackend

open HeytingLean.Compilation.LambdaIR

private def commaSep (xs : List String) : String :=
  String.intercalate ", " xs

private def intLit (n : Nat) : String := s!"Int<{n}>"

private def shapeTy (dims : List Nat) : String :=
  s!"Shape<{commaSep (dims.map intLit)}>"

private def strideTy (dims : List Nat) : String :=
  s!"Stride<{commaSep (dims.map intLit)}>"

private def layoutTy (shape stride : List Nat) : String :=
  s!"Layout<{shapeTy shape}, {strideTy stride}>"

private def certComment (c : LayoutCertificate) : String :=
  s!"// cert: op={c.operation}, hash={c.proofHash}"

private def layoutAlias (name : String) (layout : LayoutAnnotation) : List String :=
  if layout.isStatic then
    [s!"// Layout {name} (static)",
     s!"using {name} = {layoutTy layout.shape layout.stride};",
     ""]
  else
    [s!"// Layout {name} (runtime) — not representable as a CuTe compile-time alias",
     ""]

/-- Generate a `.hpp` header containing named CuTe layout aliases. -/
def genCUTLASSHeader (moduleName : String)
    (layouts : List (String × LayoutAnnotation))
    (certs : List LayoutCertificate) : String :=
  let certsBlock :=
    match certs with
    | [] => []
    | _ => ("// Certificates" :: certs.map certComment) ++ [""]
  let layoutLines := layouts.flatMap (fun (nm, l) => layoutAlias nm l)
  String.intercalate "\n"
    ([headerPreamble moduleName,
      pragmaOnce,
      "",
      includes,
      namespaceOpen moduleName] ++
      certsBlock ++
      layoutLines ++
      [namespaceClose])

end CUTLASSBackend
end Compilation
end HeytingLean
