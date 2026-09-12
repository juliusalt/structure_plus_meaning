#!/usr/bin/env python3
"""Build the complete session and collect its structural source checks together."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import uuid

import build

ROOT = Path(__file__).resolve().parents[1]


def source_checks() -> dict:
    names = set(re.findall(r"^    ([A-Za-z_][A-Za-z_0-9]*)\s*$", (ROOT / "ROOT").read_text(), re.M))
    files = {path.stem: path for path in (ROOT / "theories").glob("*.thy")}
    escapes = []
    for path in sorted(files.values()):
        for number, line in enumerate(path.read_text().splitlines(), 1):
            if re.search(r"\b(sorry|oops|axiomatization)\b", line):
                escapes.append({"file": str(path.relative_to(ROOT)), "line": number, "text": line.strip()})
    return {"theory_count": len(files), "missing_theory_files": sorted(names - files.keys()),
            "unlisted_theories": sorted(files.keys() - names), "proof_escape_matches": escapes}


def run_check(args) -> int:
    invocation = str(uuid.uuid4())
    output = ROOT / "validation"
    report_path = output / "check.json"
    report = {"invocation": invocation, "status": "running", "started_utc": build.utc_now(),
              "exit_code": 1, "build_receipt": "validation/build.json",
              "diagnostics_file": "validation/check-errors.log"}
    build.atomic_json(report_path, report)
    errors = ""
    (output / "check-errors.log").write_text(errors)
    try:
        # Use this invocation's returned evidence, never a receipt from an earlier process.
        receipt = build.run_build(args, invocation)
        report.update(build_status=receipt["status"], build_evidence=receipt)
        errors = receipt.get("error", "") + receipt.get("session_diagnostics", "")
        report.update(source_checks())
        unchanged = receipt.get("sources") == build.source_hashes() and receipt.get("tools") == build.tool_hashes()
        report["sources_and_tools_unchanged"] = unchanged
        if receipt["invocation"] != invocation or not unchanged:
            raise RuntimeError("Build evidence does not match this invocation and its current sources.")
        code = receipt["exit_code"]
        if receipt["status"] != "accepted" and code == 0:
            code = 1
        if any(report[key] for key in ("missing_theory_files", "unlisted_theories", "proof_escape_matches")):
            code = code or 1
        report.update(status="accepted" if code == 0 else receipt["status"] if receipt["status"] == "interrupted" else "failed",
                      exit_code=code)
    except build.RunInterrupted as error:
        report.update(status="interrupted", exit_code=128 + error.signum, error=str(error))
    except KeyboardInterrupt:
        report.update(status="interrupted", exit_code=130, error="Interrupted.")
    except Exception as error:
        report.update(status="failed", exit_code=1, error=str(error))
    finally:
        report["finished_utc"] = build.utc_now()
        if report.get("error"):
            errors += "\n" + report["error"]
        (output / "check-errors.log").write_text(errors)
        build.atomic_json(report_path, report)
    print(json.dumps({k: v for k, v in report.items() if k != "build_evidence"}, indent=2))
    if errors:
        print(errors)
    return report["exit_code"]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    build.add_arguments(parser, combined=True)
    args = parser.parse_args()
    if args.threads < 1 or args.timeout < 1:
        parser.error("threads and timeout must be positive")
    with build.interruption_signals(), build.validation_lock():
        return run_check(args)


if __name__ == "__main__":
    raise SystemExit(main())
