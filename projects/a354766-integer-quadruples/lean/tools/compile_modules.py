"""Compile the pinned local modules and record reproducible kernel checks.

Run after `lake exe cache get`. A354766_LEAN may select an explicit Lean
binary; otherwise the usual elan `lean` shim reads this project's toolchain.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN = os.environ.get('A354766_LEAN') or shutil.which('lean')
if not LEAN:
    raise SystemExit('Lean is unavailable; install the pinned toolchain first.')
version = subprocess.check_output([LEAN, '--version'], cwd=ROOT, text=True).strip()
if not re.search(r'version 4\.27\.0(?:\D|$)', version):
    raise SystemExit(f'Wrong Lean version: {version}')
mathlib = ROOT / '.lake/packages/mathlib'
pin = 'a3a10db0e9d66acbebf76c5e6a135066525ac900'
actual_pin = subprocess.check_output(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True).strip()
if actual_pin != pin:
    raise SystemExit(f'Wrong Mathlib commit: {actual_pin}')

OUT = ROOT / '.lake/build/lib/lean'
OUT.mkdir(parents=True, exist_ok=True)
verification = ROOT / 'verification'
verification.mkdir(exist_ok=True)
env = dict(os.environ)
packages = [p for p in (ROOT / '.lake/packages').iterdir() if p.is_dir()]
env['LEAN_PATH'] = ':'.join(map(str, [OUT] + [p / '.lake/build/lib/lean' for p in packages]))
env['LEAN_SRC_PATH'] = ':'.join(map(str, [ROOT] + packages))
checked, results = set(), []

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def record():
    data = {'lean': version, 'mathlib': pin, 'modules': results}
    (verification / 'standalone-results.json').write_text(json.dumps(data, indent=2) + '\n')

def check(module):
    if module in checked:
        return
    source = ROOT / Path(*module.split('.')).with_suffix('.lean')
    if not source.exists():
        return
    dependencies = []
    for line in re.findall(r'^import\s+([^\n]+)', source.read_text(), re.M):
        for dependency in line.split():
            check(dependency)
            if (ROOT / Path(*dependency.split('.')).with_suffix('.lean')).exists():
                dependencies.append(OUT / Path(*dependency.split('.')).with_suffix('.olean'))
    target = OUT / Path(*module.split('.')).with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    checked.add(module)
    item = {'module': module, 'source_sha256': digest(source)}
    if module != 'A354766.FinalAxioms' and target.exists() and target.stat().st_mtime >= max(
            [source.stat().st_mtime] + [p.stat().st_mtime for p in dependencies]):
        print('REUSE', module, flush=True)
        item.update(exit_code=0, reused=True, artifact_sha256=digest(target))
        results.append(item)
        record()
        return
    print('CHECK', module, flush=True)
    pending = target.with_suffix('.checking.olean')
    pending.unlink(missing_ok=True)
    start = time.monotonic()
    result = subprocess.run([LEAN, '-j', '2', '-o', str(pending), str(source)], cwd=ROOT, env=env)
    item.update(exit_code=result.returncode, seconds=round(time.monotonic() - start, 3))
    if result.returncode == 0:
        pending.replace(target)
        item['artifact_sha256'] = digest(target)
    else:
        pending.unlink(missing_ok=True)
    results.append(item)
    record()
    print('RESULT', module, item['exit_code'], item['seconds'], flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)

print(version, '\nMathlib', pin, flush=True)
for module in sys.argv[1:] or ['A354766', 'A354766.FinalAxioms']:
    check(module)
print('All selected modules passed.', flush=True)
