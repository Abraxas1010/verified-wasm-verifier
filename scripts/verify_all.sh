#!/usr/bin/env bash
# verify_all.sh — verify shipped bundle + negative cases for public Wasm verifier
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BUNDLE="${ROOT}/public_material/verified_wasm_export_bundle"

echo "[1/4] Version check..."
python3 -m cli.leancp_verify --version
echo "  PASS"

echo "[2/4] Shipped bundle verification..."
python3 -m cli.leancp_verify \
  --wat-file "${BUNDLE}/output.wat" \
  --lean-source "${BUNDLE}/lean_source" \
  --certificate "${BUNDLE}/generation.json" \
  --json
echo "  PASS"

echo "[3/4] SHA-256 hash consistency..."
WAT_HASH=$(python3 -c "import hashlib; print(hashlib.sha256(open('${BUNDLE}/output.wat','rb').read()).hexdigest())")
CERT_HASH=$(python3 -c "import json; print(json.load(open('${BUNDLE}/generation.json'))['wasm_output_sha256'])")
if [ "$WAT_HASH" = "$CERT_HASH" ]; then
  echo "  WAT hash: $WAT_HASH"
  echo "  PASS"
else
  echo "  FAIL: WAT hash $WAT_HASH != cert hash $CERT_HASH" >&2
  exit 1
fi

echo "[4/4] Negative cases..."
"${ROOT}/scripts/verify_negative_cases.sh"

echo ""
echo "[verify_all] ALL CHECKS PASSED"
