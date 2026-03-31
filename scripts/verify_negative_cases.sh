#!/usr/bin/env bash
# verify_negative_cases.sh — Wasm verifier: tests that SHOULD fail
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BUNDLE="${ROOT}/public_material/verified_wasm_export_bundle"
WAT_FILE="${BUNDLE}/output.wat"
LEAN_SRC="${BUNDLE}/lean_source"
CERT="${BUNDLE}/generation.json"

PASS=0
FAIL=0

expect_reject() {
  local desc="$1"; shift
  local output
  output="$(python3 -m cli.leancp_verify "$@" --json 2>/dev/null || true)"
  if [ -z "$output" ]; then
    echo "  [NEG-PASS] $desc (CLI error)"
    PASS=$((PASS + 1))
    return
  fi
  local accepted
  accepted="$(echo "$output" | python3 -c "import json,sys; r=json.load(sys.stdin); print(r.get('accept', False))" 2>/dev/null || echo "error")"
  if [ "$accepted" = "False" ] || [ "$accepted" = "error" ]; then
    echo "  [NEG-PASS] $desc"
    PASS=$((PASS + 1))
  else
    echo "  [NEG-FAIL] $desc — expected reject but got accept" >&2
    FAIL=$((FAIL + 1))
  fi
}

echo "Negative cases (should all be rejected):"

expect_reject "missing WAT file" \
  --wat-file "/nonexistent/output.wat" \
  --lean-source "$LEAN_SRC" \
  --certificate "$CERT"

expect_reject "missing lean source" \
  --wat-file "$WAT_FILE" \
  --lean-source "/nonexistent/lean_source" \
  --certificate "$CERT"

expect_reject "missing certificate" \
  --wat-file "$WAT_FILE" \
  --lean-source "$LEAN_SRC" \
  --certificate "/nonexistent/cert.json"

TAMPERED=$(mktemp)
echo ";; tampered" > "$TAMPERED"
expect_reject "tampered WAT file" \
  --wat-file "$TAMPERED" \
  --lean-source "$LEAN_SRC" \
  --certificate "$CERT"
rm -f "$TAMPERED"

TAMPERED_CERT=$(mktemp)
echo '{"invalid": true}' > "$TAMPERED_CERT"
expect_reject "invalid certificate JSON" \
  --wat-file "$WAT_FILE" \
  --lean-source "$LEAN_SRC" \
  --certificate "$TAMPERED_CERT"
rm -f "$TAMPERED_CERT"

TAMPERED_SRC=$(mktemp -d)
echo "-- tampered" > "$TAMPERED_SRC/fake.lean"
expect_reject "tampered lean source" \
  --wat-file "$WAT_FILE" \
  --lean-source "$TAMPERED_SRC" \
  --certificate "$CERT"
rm -rf "$TAMPERED_SRC"

EMPTY_CERT=$(mktemp)
echo "" > "$EMPTY_CERT"
expect_reject "empty certificate" \
  --wat-file "$WAT_FILE" \
  --lean-source "$LEAN_SRC" \
  --certificate "$EMPTY_CERT"
rm -f "$EMPTY_CERT"

echo ""
echo "Negative cases: $PASS passed, $FAIL failed (out of 7)"
[ "$FAIL" -eq 0 ] || exit 1
