#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Stage unchanged proof sources for fresh builds without rewriting evidence."""
from pathlib import Path
import argparse
import shutil

ROOT = Path(__file__).resolve().parents[1]
CURRENT = ROOT / 'verification' / 'current'
DEST = CURRENT / 'formal'

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--clean', action='store_true', help='Remove only generated current checks.')
args = parser.parse_args()
if args.clean:
    if CURRENT.exists():
        shutil.rmtree(CURRENT)
    print('Removed generated verification/current outputs; recorded evidence retained.')
else:
    # copytree merges sources into an existing stage, retaining dependencies
    # and reusable generated artifacts. It never takes historical output logs.
    shutil.copytree(ROOT / 'lean', DEST, dirs_exist_ok=True,
                    ignore=shutil.ignore_patterns('verification', '.lake', '__pycache__', '*.pyc'))
    (DEST / 'verification').mkdir(parents=True, exist_ok=True)
    print('Staged unchanged Lean sources under verification/current/formal.')
    print('Fresh logs remain in that directory; lean/verification is preserved.')
