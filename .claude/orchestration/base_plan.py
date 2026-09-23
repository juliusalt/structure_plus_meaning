#!/usr/bin/env python3
"""Facts for testing a reasoned base design, never a numerical content selector.

`data` records source relations, plan sections, current task scopes and projection sizes. The withdrawn weighted
model is deliberately absent. `plan` explains where the responsibility-based rule now lives. No session is launched.
"""
import argparse
import json
import os
from pathlib import Path
import time

import select_base_load as select
import v2


def gather():
    thys = {p.stem: str(p) for p in sorted((Path(select.PROJECT) / 'theories').glob('*.thy'))}
    refs, imports = select.references(thys)
    by_rel = {os.path.relpath(p, select.PROJECT): n for n, p in thys.items()}
    return dict(at=time.time(), boundary='Discovery relations and size estimates; no semantic verdict or value score.',
                refs=refs, imports=imports, plan=select.plan_parts(select.defined_names(), by_rel),
                bases={who: dict(selection=select.relation_choice(who), projection=select.projection(who)) for who in v2.BASES})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('data', 'plan'))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.command == 'plan':
        print('The weighted plan is withdrawn. The reasoned rule is in plan-bases-two-purposes.md; '
              'select_base_load.py --projection WHO applies its source relations and reports the result.')
        return 0
    output = args.output or Path(v2.STATE) / 'analysis/base-plan-data.json'
    data = gather()
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(data, indent=2) + '\n')
    print(output)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
