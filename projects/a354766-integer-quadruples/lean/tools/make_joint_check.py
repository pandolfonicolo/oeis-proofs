"""Generate a deterministic check of the complete local dependency graph.

Only import lines are replaced; every proof body remains unchanged.
Normal standalone builds still validate the module boundaries separately.
"""
from pathlib import Path
import re
import json
import hashlib

root = Path(__file__).resolve().parents[1]
modules, visiting, visited = [], set(), set()

def imports_of(text):
    return [m for line in re.findall(r'^import\s+([^\n]+)', text, re.M)
            for m in line.split()]

def visit(module):
    if module in visited:
        return
    if module in visiting:
        raise RuntimeError(f'Local import cycle at {module}')
    source = root / Path(*module.split('.')).with_suffix('.lean')
    if not source.exists():
        return
    visiting.add(module)
    for dependency in imports_of(source.read_text()):
        if dependency == 'A354766' or dependency.startswith('A354766.'):
            visit(dependency)
    visiting.remove(module)
    visited.add(module)
    modules.append((module, source))

visit('A354766')
visit('A354766.FinalAxioms')
external_imports = []
for _, source in modules:
    for module in imports_of(source.read_text()):
        if module not in visited and module not in external_imports:
            external_imports.append(module)

result = '\n'.join('import ' + m for m in external_imports) + '\n\n'
manifest = []
for module, source in modules:
    result += f'\n/- BEGIN SOURCE MODULE {module} -/\n'
    start = len(result.splitlines())
    body = re.sub(r'^import([^\n]*)', r'-- imported above:\1', source.read_text(), flags=re.M)
    result += body + f'\n/- END SOURCE MODULE {module} -/\n'
    manifest.append({'module': module, 'source': str(source.relative_to(root)),
                     'sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                     'line_offset': start})

(root / 'A354766JointCheck.lean').write_text(result)
(root / 'joint-source-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(f'Generated {len(modules)} modules and {len(result.splitlines())} lines; proof bodies unchanged.')
