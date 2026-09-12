#!/usr/bin/env python3
"""Execute the actual revision returned by one successful investigation."""
from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys

import investigate


def revision_case(receipt_path: Path) -> dict:
    receipt_path = receipt_path.resolve()
    receipt_bytes = receipt_path.read_bytes()
    receipt = json.loads(receipt_bytes)
    case_path = receipt_path.parent / "case.json"
    investigate.require(receipt.get("status") == "evaluated" and receipt.get("exit_code") == 0
        and receipt.get("sources_and_tools_unchanged") is True,
        "Following a revision requires a successful stable execution.")
    case_bytes = case_path.read_bytes()
    investigate.require(investigate.digest(case_bytes) == receipt.get("case_sha256"),
                        "The preceding case bytes changed.")
    original = json.loads(case_bytes)
    investigate.validate_case(original)
    investigate.require(original["kind"] != "inference", "Inference reports do not propose facet revisions.")
    investigate.validate_result(receipt["result"], original["kind"])
    investigate.require(receipt["result"]["input_formed"], "A rejected input cannot propose a revision.")
    proposal = receipt["result"]["revision"]
    case = copy.deepcopy(original)
    case["selected"] = proposal["selection"]
    case.setdefault("evidence", []).extend([
        {"path": str(receipt_path), "sha256": investigate.digest(receipt_bytes)},
        {"path": str(case_path), "sha256": investigate.digest(case_bytes)},
        {"path": str(Path(__file__).resolve()), "sha256": investigate.file_hash(Path(__file__))},
    ])
    case["revision_source"] = {"receipt": str(receipt_path), "withdrawn": proposal["withdrawn"],
        "repairs": proposal["repairs"], "remaining_comparisons": proposal["residual"]}
    investigate.validate_case(case)
    return case


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipt", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        case = revision_case(args.receipt)
        output = args.output.resolve()
        investigate.require(output != args.receipt.resolve().parent,
                            "The follow-up must retain the preceding run directory.")
        output.mkdir(parents=True, exist_ok=True)
        case_path = output / "proposed-case.json"
        investigate.require(not case_path.exists(), "The proposed case path already exists.")
        case_path.write_text(json.dumps(case, indent=2) + "\n")
        return subprocess.run([sys.executable, str(Path(investigate.__file__).resolve()),
            "--output", str(output), "run", str(case_path)], check=False).returncode
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
