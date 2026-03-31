from __future__ import annotations

VERIFIER_VERSION = "0.1.0"
GENERATION_SCHEMA_VERSION = "leancp-wasm-generation-certificate-v1"
VERIFY_SCHEMA_VERSION = "leancp-wasm-verification-report-v1"
LEAN_TOOLCHAIN = "leanprover/lean4:v4.24.0"
SUPPORTED_MODES = ["generate", "verify"]


def compatibility_contract() -> dict[str, object]:
    return {
        "verifier_version": VERIFIER_VERSION,
        "supported_generation_schema_versions": [GENERATION_SCHEMA_VERSION],
        "supported_verification_schema_versions": [VERIFY_SCHEMA_VERSION],
        "lean_toolchain": LEAN_TOOLCHAIN,
        "target_language": "wasm",
        "modes": SUPPORTED_MODES,
        "bundle_layout_version": "leancp-wasm-service-bundle-v1",
        "sorry_policy": {
            "full": "no_sorry_or_admit_required",
            "scoped": "sorry_or_admit_advisory_only",
        },
        "accept_means": [
            "Lean build exits with code 0",
            "no unresolved sorry/admit in full-project runs (scoped mode reports advisories)",
            "generated WAT output hash matches certificate",
            "lean source hash matches certificate",
            "Lean toolchain matches certificate",
        ],
        "accept_does_not_mean": [
            "the specification is mathematically correct",
            "the generated WAT is portable without additional assumptions",
            "the code is production hardened",
            "timing, performance, or side-channel guarantees",
        ],
    }
