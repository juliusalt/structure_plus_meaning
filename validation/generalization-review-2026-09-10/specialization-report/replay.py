#!/usr/bin/env python3
"""Replay the retained module with its original independent checker."""
import argparse
from pathlib import Path
import check_reasoning

base = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--project", type=Path, default=base.parents[2])
parser.add_argument("--poly", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
check_reasoning.ROOT = args.project.resolve()
args.proof = base / "proof.json"
args.engine = base / "native_reasoning.ML"
raise SystemExit(check_reasoning.run(args))
