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


def theory_declarations(root: Path) -> dict:
    """Each theory ROOT declares, with the line that declares it."""
    text = (root / "ROOT").read_text()
    return {match[1]: text.count("\n", 0, match.start()) + 1
            for match in re.finditer(r"^    ([A-Za-z_][A-Za-z_0-9]*)\s*$", text, re.M)}


def source_checks(root: Path = ROOT) -> dict:
    """The structural source checks, with a refusal line naming every item that fails one.

    A session reads the refusals to decide, so each one names what was found and where it is:
    an undeclared theory by its path, a declared theory whose file is absent by name and by the
    ROOT line that declares it, an escaped proof by file, line and the escaping text.
    """
    declarations = theory_declarations(root)
    files = {path.stem: path for path in (root / "theories").glob("*.thy")}
    escapes = []
    for path in sorted(files.values()):
        for number, line in enumerate(path.read_text().splitlines(), 1):
            if re.search(r"\b(sorry|oops|axiomatization)\b", line):
                escapes.append({"file": str(path.relative_to(root)), "line": number, "text": line.strip()})
    missing = sorted(declarations.keys() - files.keys())
    unlisted = sorted(files.keys() - declarations.keys())
    refusals = [f"ROOT line {declarations[name]} declares {name}, but theories/{name}.thy is absent"
                for name in missing]
    refusals += [f"theories/{name}.thy is not declared in ROOT" for name in unlisted]
    refusals += [f"{escape['file']}:{escape['line']} escapes its proof: {escape['text']}" for escape in escapes]
    return {"theory_count": len(files), "missing_theory_files": missing, "unlisted_theories": unlisted,
            "proof_escape_matches": escapes, "refusals": refusals}


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
        if report["refusals"]:
            errors += "\n".join(("", "Source checks refused:", *report["refusals"]))
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
