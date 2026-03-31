from __future__ import annotations

from typing import Any, Literal

from pydantic import BaseModel


class GenerationCertificate(BaseModel):
    schema_version: Literal["leancp-wasm-generation-certificate-v1"]
    generated_at: str
    lean_toolchain: str
    leancp_library_sha256: str
    lean_source_sha256: str
    lean_build_exit_code: int
    sorry_count: int
    admit_count: int
    target_language: Literal["wasm"]
    wasm_output_sha256: str
    wasm_output_deterministic: bool
    generation_log_sha256: str


class VerificationReport(BaseModel):
    accept: bool
    checked_at: str
    failed_checks: list[str]
    lean_source_sha256: str | None = None
    wasm_output_sha256: str | None = None
    certificate_sha256: str | None = None
    lean_toolchain_match: bool | None = None
    kernel_verdict: str | None = None


class LeanSourceHashBundle(BaseModel):
    manifest_hash: str
    artifact_hashes: dict[str, str] = {}


class GenerationRequest(BaseModel):
    source: str
    output: str
    schema_version: Literal["leancp-wasm-generate-request-v1"] = "leancp-wasm-generate-request-v1"
    options: dict[str, Any] = {}
