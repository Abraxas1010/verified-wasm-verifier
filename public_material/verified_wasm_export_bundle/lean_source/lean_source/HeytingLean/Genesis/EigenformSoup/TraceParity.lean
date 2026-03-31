import HeytingLean.Genesis.EigenformSoup.Extraction

/-!
# Genesis.EigenformSoup.TraceParity

Theorem-facing parity layer for LES trace payloads.

We track both proxy and native lanes at the semantic level using the same
trace-checksum payload contract, then expose lane-specific parity theorems.
-/

namespace HeytingLean.Genesis.EigenformSoup

/-- Proxy-lane semantic checksum target. -/
noncomputable def proxyTraceChecksum (nuc : SoupNucleus) (cfg : SoupConfig) : Nat :=
  (mkSoupTraceArtifact nuc cfg).traceChecksum

/-- Native-lane semantic checksum target. -/
noncomputable def nativeTraceChecksum (nuc : SoupNucleus) (cfg : SoupConfig) : Nat :=
  (mkSoupTraceArtifact nuc cfg).traceChecksum

/-- Both lanes target the same semantic trace checksum. -/
@[simp] theorem proxy_native_traceChecksum_eq (nuc : SoupNucleus) (cfg : SoupConfig) :
    proxyTraceChecksum nuc cfg = nativeTraceChecksum nuc cfg := rfl

/-- Proxy lane C payload parity: emitted C code matches proxy semantic checksum. -/
theorem proxy_trace_c_payload_parity (nuc : SoupNucleus) (cfg : SoupConfig) :
    (compileSoupTraceCAB nuc cfg).cCode =
      renderTraceChecksumC (proxyTraceChecksum nuc cfg) := by
  simpa [proxyTraceChecksum] using compileSoupTraceCAB_cCode_has_traceChecksum nuc cfg

/-- Native lane C payload parity: emitted C code matches native semantic checksum. -/
theorem native_trace_c_payload_parity (nuc : SoupNucleus) (cfg : SoupConfig) :
    (compileSoupTraceCAB nuc cfg).cCode =
      renderTraceChecksumC (nativeTraceChecksum nuc cfg) := by
  simpa [nativeTraceChecksum] using compileSoupTraceCAB_cCode_has_traceChecksum nuc cfg

end HeytingLean.Genesis.EigenformSoup
