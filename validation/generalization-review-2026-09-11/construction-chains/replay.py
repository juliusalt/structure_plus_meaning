#!/usr/bin/env python3
"""Replay a retained case family against its matching proof-source checkout."""
from pathlib import Path
import argparse
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=["before", "after"], required=True)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--poly", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    base = Path(__file__).resolve().parent / args.stage
    if not (base / "proof.json").is_file():
        parser.error("The requested retained stage is not present.")
    sys.path.insert(0, str(base))
    import check_reasoning as review
    import check_construction_chains as experiment
    review.ROOT = args.project.resolve()
    sys.argv = [str(base / "check_construction_chains.py"),
                "--proof", str(base / "proof.json"), "--engine", str(base / "native_reasoning.ML"),
                "--poly", str(args.poly.resolve()), "--output", str(args.output.resolve())]
    return experiment.main()


if __name__ == "__main__":
    raise SystemExit(main())
