#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Audit source bindings and recorded evidence; this does not invoke Lean.

The separate exact-count program performs the fresh bounded enumeration in
`make verify`. Kernel recompilation belongs to the distinct `make formal`.
"""
from pathlib import Path
import argparse
import csv
import hashlib
import json
from math import isqrt
import re

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean'
PIN = 'a3a10db0e9d66acbebf76c5e6a135066525ac900'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
FINAL_NAMES = (
    'A354766Neighbors.actual_odd_prime_recurrences',
    'A354766Neighbors.primitive_three_squares_euler_product',
    'A354766.cooper_hirschhorn_specialization',
    'A354766.primitive_quad_count_bridge',
    'A354766.multiplicative_conclusion',
    'A354766.P_prime_pow_mod_six_one',
    'A354766.P_prime_pow_mod_six_five',
    'A354766.P_three_pow',
    'A354766.T_prime_pow_mod_six_one',
    'A354766.T_prime_pow_mod_three',
    'A354766.equality_characterization',
    'A354766.equalitySet_density_zero',
    'A354766.A278085Primary_eq_P',
    'A354766.A278085Primary_multiplicative',
)
RECORDED_CLOUD_HASHES = {
    'exact_counts.py': '9899c969c7e46ebceab46462e73a193ba13440bdc3198c2629ec30e803c8284f',
    'counts.csv': '0003257db8d07d8981b88db36c6df734a9558234af0d21bf8c0b55bcf2c547f3',
    'symmetric_checks.csv': 'd20279cbe809fcbf71c35c48f655a3484646651f3b66e7d8d5132b1d82830694',
}


def require(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_identifiers(source):
    """Skip nested Lean comments and string literals before admission checks."""
    i, depth = 0, 0
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                depth += 1
                i += 2
            elif source.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif source.startswith('/-', i):
            depth = 1
            i += 2
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end + 1
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            match = re.match(r"[A-Za-z_][A-Za-z_0-9']*", source[i:])
            if match:
                yield match.group()
                i += len(match.group())
            else:
                i += 1
    require(depth == 0, 'Unterminated Lean block comment')


def imports_of(text):
    return [name for line in re.findall(r'^import\s+([^\n]+)', text, re.M)
            for name in line.split()]


def audit_sources():
    require((LEAN / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.27.0',
            'Lean toolchain is not pinned to v4.27.0')
    dependencies = json.loads((LEAN / 'lake-manifest.json').read_text())['packages']
    require(len(dependencies) == 9, 'Expected nine pinned dependency repositories')
    require(all(re.fullmatch(r'[0-9a-f]{40}', item['rev']) for item in dependencies),
            'An external dependency revision is not an exact commit')
    require(next(item['rev'] for item in dependencies if item['name'] == 'mathlib') == PIN,
            'Wrong Mathlib revision')

    manifest = json.loads((LEAN / 'joint-source-manifest.json').read_text())
    require(len(manifest) == 43, 'Expected the complete 43-module proof graph')
    by_name = {item['module']: item for item in manifest}
    require(len(by_name) == 43, 'Repeated module names in source manifest')
    order, active, visited = [], set(), set()

    def visit(name):
        if name in visited:
            return
        require(name not in active, 'Cycle in local proof imports: ' + name)
        require(name in by_name, 'Unmanifested local proof import: ' + name)
        item = by_name[name]
        source = Path(*name.split('.')).with_suffix('.lean')
        require(source.as_posix() == item['source'], 'Module/source path mismatch: ' + name)
        path = LEAN / source
        require(path.is_file(), 'Missing proof module: ' + name)
        require(digest(path) == item['sha256'], 'Proof source hash mismatch: ' + name)
        forbidden = set(code_identifiers(path.read_text())) & {
            'sorry', 'admit', 'axiom', 'sorryAx', 'skipKernelTC',
        }
        require(not forbidden, 'Forbidden admission/kernel bypass in ' + name + ': ' + repr(forbidden))
        active.add(name)
        for dependency in imports_of(path.read_text()):
            if dependency == 'A354766' or dependency.startswith('A354766.'):
                visit(dependency)
        active.remove(name)
        visited.add(name)
        order.append(name)

    visit('A354766')
    visit('A354766.FinalAxioms')
    require(order == [item['module'] for item in manifest],
            'Source manifest is not the complete deterministic topological import graph')

    # Reconstruct the deterministic joined source in memory only. Recorded
    # evidence and the published generated source are never rewritten.
    external = []
    for name in order:
        for dependency in imports_of((LEAN / by_name[name]['source']).read_text()):
            if dependency not in visited and dependency not in external:
                external.append(dependency)
    joined = '\n'.join('import ' + name for name in external) + '\n\n'
    for name in order:
        item = by_name[name]
        joined += '\n/- BEGIN SOURCE MODULE ' + name + ' -/\n'
        require(len(joined.splitlines()) == item['line_offset'],
                'Joined-source line map differs for ' + name)
        body = re.sub(r'^import([^\n]*)', r'-- imported above:\1',
                      (LEAN / item['source']).read_text(), flags=re.M)
        joined += body + '\n/- END SOURCE MODULE ' + name + ' -/\n'
    require(joined == (LEAN / 'A354766JointCheck.lean').read_text(),
            'Generated joint source no longer matches unchanged local proof bodies')
    print('PASS static source audit: pinned dependencies; 43 source hashes; complete import graph; no admissions.')
    return by_name


def audit_reports(text, context):
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    reports = {}
    for name, raw_axioms in matches:
        axioms = {part.strip() for part in raw_axioms.split(',') if part.strip()}
        require(axioms <= ALLOWED_AXIOMS, context + ': unexpected axioms for ' + name)
        if name in reports:
            require(reports[name] == axioms, context + ': contradictory duplicate axiom report')
        reports[name] = axioms
    require(set(FINAL_NAMES) <= set(reports), context + ': missing a final conclusion report')


def audit_recorded_formal(by_name):
    expected = re.findall(r'^#print axioms (\S+)',
                          (LEAN / 'A354766/FinalAxioms.lean').read_text(), re.M)
    require(tuple(expected) == FINAL_NAMES, 'Final audit contract must list the exact 14 conclusions')
    evidence = LEAN / 'verification'
    standalone = json.loads((evidence / 'standalone-results.json').read_text())
    require(re.search(r'version 4\.27\.0(?:\D|$)', standalone['lean']), 'Wrong recorded Lean compiler')
    require(standalone['mathlib'] == PIN, 'Wrong recorded Mathlib commit')
    modules = standalone['modules']
    require(len(modules) == 43 and {item['module'] for item in modules} == set(by_name),
            'Standalone records do not cover the complete graph')
    for item in modules:
        name = item['module']
        require(item['exit_code'] == 0, 'Recorded compilation failed: ' + name)
        require(item['source_sha256'] == by_name[name]['sha256'],
                'Recorded compiler source binding differs: ' + name)
        require(re.fullmatch(r'[0-9a-f]{64}', item.get('artifact_sha256', '')),
                'Missing recorded compiled-artifact hash: ' + name)
    log = (evidence / 'standalone.log').read_text()
    require('All selected modules passed.' in log, 'Recorded standalone build lacks success marker')
    require(not re.search(r'(^|\n)[^\n]*\berror:', log), 'An error occurs in the recorded standalone log')
    audit_reports(log, 'Standalone release record')

    joined = json.loads((evidence / 'CompleteConclusions.CHECKED.json').read_text())
    require(joined['errors'] == 0 and joined['busy'] is False, 'Recorded joined check did not finish cleanly')
    require(joined['sorryAx'] is False and joined['compiler_trust_axioms'] is False,
            'Recorded joined check has an admission/compiler-trust dependency')
    require(set(joined['axioms']) <= ALLOWED_AXIOMS, 'Unexpected joined-check axiom summary')
    require(digest(evidence / 'CompleteConclusions.CHECKED.joined.lean.txt') == joined['joined_sha256'],
            'Recorded checked joint-source hash differs')
    audit_reports('\n'.join(joined['final_axiom_audits']), 'Joined release record')
    print('PASS recorded formal evidence: 43 successful source-bound module records and 14 final standard-axiom reports.')
    print('NOTE this is an audit of recorded compilation evidence, not a new Lean compilation.')


def factorization(n):
    factors = []
    trial = 2
    while trial * trial <= n:
        exponent = 0
        while n % trial == 0:
            n //= trial
            exponent += 1
        if exponent:
            factors.append((trial, exponent))
        trial += 1
    if n > 1:
        factors.append((n, 1))
    return factors


def p_formula(n):
    result = 1
    for prime, exponent in factorization(n):
        if prime == 2:
            if exponent >= 2:
                return 0
        else:
            character = 0 if prime == 3 else 1 if prime % 3 == 1 else -1
            result *= prime ** (exponent - 1) * (prime - character)
    return result


def audit_recorded_counts():
    cloud = ROOT / 'verification/cloud'
    recorded_log = (cloud / 'CLOUD-EXACT-COUNTS-3.txt').read_text()
    for filename, expected_hash in RECORDED_CLOUD_HASHES.items():
        require(digest(cloud / filename) == expected_hash, 'Independent cloud transfer hash differs: ' + filename)
        require(expected_hash in recorded_log, 'Cloud record lacks the bound transfer hash: ' + filename)
    with (cloud / 'counts.csv').open(newline='') as stream:
        rows = list(csv.DictReader(stream))
    require(len(rows) == 300, 'Recorded independent enumeration must contain n=1..300')
    primitive = {n: p_formula(n) for n in range(1, 301)}
    checked_three_squares = 0
    for n, raw in enumerate(rows, 1):
        require(int(raw['n']) == n, 'Recorded count rows are missing, repeated, or unordered')
        total = sum(primitive[d] for d in range(1, n + 1) if n % d == 0)
        for key in ('standard_total_raw', 'primary_total_raw'):
            require(int(raw[key]) == 4 * total, f'Recorded total/formula mismatch at n={n}: {key}')
        for key in ('standard_primitive_raw', 'primary_primitive_raw'):
            require(int(raw[key]) == 4 * primitive[n], f'Recorded primitive/formula mismatch at n={n}: {key}')
        for key in ('A354766_T', 'formula_T'):
            require(int(raw[key]) == total, f'Recorded normalized total mismatch at n={n}')
        for key in ('A278085_P', 'formula_P'):
            require(int(raw[key]) == primitive[n], f'Recorded normalized primitive mismatch at n={n}')
        if n % 2 and n <= 75:
            require(int(raw['r3prim_3n2']) == 8 * primitive[n] and
                    int(raw['formula_r3prim_3n2']) == 8 * primitive[n],
                    f'Recorded direct three-square mismatch at n={n}')
            checked_three_squares += 1
        else:
            require(raw['r3prim_3n2'] == raw['formula_r3prim_3n2'] == '',
                    'Unexpected direct three-square coverage in recorded CSV')
    require(checked_three_squares == 38, 'Wrong recorded direct three-square coverage')
    with (cloud / 'symmetric_checks.csv').open(newline='') as stream:
        symmetric = list(csv.DictReader(stream))
    require(len(symmetric) == 12, 'Recorded symmetric-bound checks must cover n=1..12')
    for n, raw in enumerate(symmetric, 1):
        require(int(raw['n']) == n and int(raw['radius']) == isqrt(3 * n * n),
                'Incorrect symmetric-bound level or radius')
        for suffix in ('total', 'primitive'):
            require(int(raw['nonnegative_' + suffix]) == int(raw['symmetric_' + suffix]) ==
                    int(rows[n-1]['primary_' + suffix + '_raw']),
                    'Symmetric/nonnegative primary count discrepancy')
        require(int(raw['nonnegative_min_coordinate']) == int(raw['symmetric_min_coordinate']) == 0,
                'Unexpected negative primary coordinate in recorded check')
    print('PASS recorded numerical audit: all 300 rows, 38 direct three-square levels, and 12 symmetric-bound levels.')
    print('NOTE finite recorded counts are consistency evidence, not a proof of the general statements.')


def publication_files():
    tex_intermediates = {'.aux', '.fdb_latexmk', '.fls', '.log', '.out', '.toc'}
    for path in sorted(ROOT.rglob('*')):
        if not path.is_file():
            continue
        rel = path.relative_to(ROOT)
        if rel.as_posix() == 'checksums.sha256':
            continue
        if any(part in {'.git', '.lake', '__pycache__'} for part in rel.parts):
            continue
        if rel.parts[:2] == ('verification', 'current'):
            continue
        if path.name == '.DS_Store' or path.suffix == '.pyc':
            continue
        if rel.parts[0] == 'manuscript' and (path.suffix in tex_intermediates or path.name.endswith('.synctex.gz')):
            continue
        yield path, rel.as_posix()


def write_checksums():
    entries = [digest(path) + '  ' + rel for path, rel in publication_files()]
    (ROOT / 'checksums.sha256').write_text('\n'.join(entries) + '\n')
    print('Wrote publication checksums for ' + str(len(entries)) + ' files.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-checksums', action='store_true',
                        help='Explicitly regenerate the publication SHA-256 list; never run implicitly.')
    args = parser.parse_args()
    if args.write_checksums:
        write_checksums()
    else:
        audit_recorded_formal(audit_sources())
        audit_recorded_counts()
        print('PASS package release-evidence audit. Use make formal for fresh kernel verification.')
