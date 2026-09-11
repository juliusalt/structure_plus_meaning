#!/usr/bin/env python3
"""Retain complete exported libraries in the reasoning review's JSON syntax.

The shared serializer rejects target artifacts outside its supported complete
representation. Source-program soundness comes from the named theory contracts;
this exporter checks finite schema formation and complete premise enumeration.
"""
from __future__ import annotations

import argparse
from pathlib import Path

import check_reasoning as review


def no_cases():
    return []


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proof", type=Path, required=True)
    parser.add_argument("--poly", type=Path, required=True)
    parser.add_argument("--engine", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--library", action="append", required=True)
    args = parser.parse_args()
    return review.run(args, cases_factory=no_cases, cases_source=Path(__file__), library_exports=args.library)


if __name__ == "__main__":
    raise SystemExit(main())
