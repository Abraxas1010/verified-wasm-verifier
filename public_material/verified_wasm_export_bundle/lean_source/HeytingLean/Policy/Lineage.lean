import Lean
import Lean.Data.Json
import HeytingLean.Boundary.Digests

namespace HeytingLean
namespace Policy
namespace Lineage

open Boundary.Digests

def lineageOk (parentHash : String) (child : StmtInputs) : Bool :=
  child.parentReceiptHash == parentHash

end Lineage
end Policy
end HeytingLean

