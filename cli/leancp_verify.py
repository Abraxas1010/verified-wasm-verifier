from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from verifier.verify import verify_generation
from verifier.version import VERIFIER_VERSION, compatibility_contract


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="leancp-wasm-verify",
        description="Verify generated WAT artifacts against a generation certificate.",
    )
    parser.add_argument("--wat-file", required=False, help="Path to emitted WAT source.")
    parser.add_argument("--lean-source", required=False, help="Path to Lean source directory.")
    parser.add_argument("--certificate", required=False, help="Path to generation certificate JSON.")
    parser.add_argument("--json", action="store_true", help="Emit structured JSON output.")
    parser.add_argument("--version", action="store_true", help="Print version and exit.")
    parser.add_argument("--print-compatibility", action="store_true", help="Print compatibility contract.")
    args = parser.parse_args(argv)

    if args.version:
        print(VERIFIER_VERSION)
        return 0

    if args.print_compatibility:
        print(json.dumps(compatibility_contract(), indent=2, sort_keys=True))
        return 0

    if not args.wat_file or not args.lean_source or not args.certificate:
        parser.error("--wat-file, --lean-source, and --certificate are required for verification.")

    report = verify_generation(
        wat_file=Path(args.wat_file).resolve(),
        lean_source=Path(args.lean_source).resolve(),
        certificate=Path(args.certificate).resolve(),
    )
    if args.json:
        print(json.dumps(report.model_dump(), indent=2, sort_keys=True))
    else:
        for key, val in report.model_dump().items():
            print(f"{key}: {val}")
    return 0 if report.accept else 1


if __name__ == "__main__":
    raise SystemExit(main())
