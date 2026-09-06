"""Command-line access to the canonical exact-record profile."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from .codec import CodecError, decode_record, encode_record, reference_to_value
from .artifact import reference_for


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="rra-kernel")
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("validate", "ref", "canonicalize", "verify-assembly"):
        p = sub.add_parser(name)
        p.add_argument("record", type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        raw = args.record.read_bytes()
        if args.command == "verify-assembly":
            from .assembly import verify_witness
            from .assembly_codec import decode_witness
            if not verify_witness(decode_witness(raw)):
                raise CodecError("assembly witness does not satisfy K2")
            print("valid")
            return 0
        if args.command == "canonicalize":
            record = decode_record(raw, require_canonical=False)
            sys.stdout.buffer.write(encode_record(record) + b"\n")
            return 0
        record = decode_record(raw, require_canonical=True)
        if args.command == "validate":
            print("valid")
        elif args.command == "ref":
            print(json.dumps(reference_to_value(reference_for(record)), sort_keys=True, separators=(",", ":")))
        return 0
    except (OSError, CodecError, ValueError) as exc:
        print(f"invalid: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
