import Lean
import Lean.Data.Json
import HeytingLean.Certified.Library
import HeytingLean.Util.SHA

namespace HeytingLean
namespace Certified

open Lean
open HeytingLean.Util

namespace Transport

theorem rt1_artifact_header (p : CertifiedProgram) :
    p.artifact.header = p.header := rfl

theorem rt2_cHash_matches (p : CertifiedProgram) :
    p.header.cHash = SHA256.sha256Hex p.cCode.toUTF8 := by
  simpa [CertifiedProgram.header] using p.cHashOk

end Transport

end Certified
end HeytingLean

