# verified-wasm-verifier

Public verification tool for LeanCP-generated WebAssembly (WAT) artifacts.

## What This Does

Verifies that a WAT file was generated from a specific Lean 4 source via
the LeanCP pipeline, using SHA-256 hash chain verification. No Lean
installation required.

## Quick Start

```bash
pip install verified-wasm-verifier
leancp-wasm-verify \
  --wat-file output.wat \
  --lean-source lean_source/ \
  --certificate generation.json \
  --json
```

## Shipped Bundle

The `public_material/verified_wasm_export_bundle/` directory contains a
pre-generated WAT output with its certificate chain, ready for verification.

## Trust Model

The Lean 4 kernel is the sole trusted computing base. This tool verifies the
certificate chain — it does not re-run the prover. For full independent
verification, use [verified-wasm-from-proof](https://github.com/Abraxas1010/verified-wasm-from-proof)
with `--full` mode.

## License

See LICENSE.md
