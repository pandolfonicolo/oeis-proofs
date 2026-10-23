"""Audit the selected source graph and actual final Lean axiom reports."""
from pathlib import Path
import argparse
import hashlib
import json
import re

parser = argparse.ArgumentParser()
parser.add_argument('--axioms-log', type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / 'joint-source-manifest.json').read_text())

def identifiers(source):
    """Ignore nested Lean comments and strings, preserving code identifiers."""
    i, depth = 0, 0
    while i < len(source):
        if depth:
            if source.startswith('/-', i): depth += 1; i += 2
            elif source.startswith('-/', i): depth -= 1; i += 2
            else: i += 1
        elif source.startswith('/-', i): depth = 1; i += 2
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end + 1
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == '\\': i += 2
                elif source[i] == '"': i += 1; break
                else: i += 1
        else:
            match = re.match(r'[A-Za-z_][A-Za-z_0-9\']*', source[i:])
            if match:
                yield match.group()
                i += len(match.group())
            else: i += 1

for item in manifest:
    path = root / item['source']
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != item['sha256']:
        raise SystemExit(f'Source changed since manifest: {item["source"]}')
    forbidden = set(identifiers(path.read_text())) & {'sorry', 'admit', 'axiom'}
    if forbidden:
        raise SystemExit(f'Admission/declaration in {item["source"]}: {sorted(forbidden)}')
print(f'Source graph: {len(manifest)} modules, no admissions or added axioms.')

if args.axioms_log:
    log = args.axioms_log.read_text()
    reports = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log))
    expected = re.findall(r'^#print axioms (\S+)',
                          (root / 'A354766/FinalAxioms.lean').read_text(), re.M)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name in expected:
        if name not in reports:
            raise SystemExit(f'Missing actual axiom report: {name}')
        axioms = {s.strip() for s in reports[name].split(',') if s.strip()}
        if not axioms <= allowed:
            raise SystemExit(f'Unexpected axioms in {name}: {sorted(axioms - allowed)}')
    print(f'Final conclusions: {len(expected)} actual reports, only standard kernel axioms.')
