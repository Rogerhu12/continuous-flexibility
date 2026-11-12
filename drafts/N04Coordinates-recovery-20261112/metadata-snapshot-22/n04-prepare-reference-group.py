"""Bind the reviewed fixed-reference sources without activating them."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
DRAFTS = ROOT / 'n04-drafts'

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def blob(path):
    raw = Path(path).read_bytes()
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()

def imports(text):
    return re.findall(r'^import\s+(\S+)', text, re.M)

def names(text):
    return re.findall(r'^(?:@\[[^\n]+\]\s*)?(?:(?:noncomputable|protected)\s+)?'
        r'(?:theorem|def|structure|abbrev|class|inductive|opaque)\s+([^\s(:{]+)', text, re.M)

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO, text=True).strip()

assert not git('status', '--porcelain')
cp = json.loads((ROOT / 'n04-active-checkpoint.json').read_text())
assert git('rev-parse', 'HEAD') == cp['head']
assert git('rev-parse', 'HEAD^{tree}') == cp['tree']
prior_path = ROOT / 'n04-next-actual-family-group-reconstructed-held.json'
prior_sha = 'bd2804ba63b06e66d551b46bd47b887deb7147972c11e1c6f927bdfd9668fd8c'
assert digest(prior_path) == prior_sha
prior = json.loads(prior_path.read_text())
inventory_path = ROOT / 'n04-reference-next-group-review-inventory.json'
inventory = json.loads(inventory_path.read_text())
selected, files = {}, []
reviews = {}
for f in inventory['files']:
    path = Path(f['source'])
    raw = path.read_text()
    assert digest(path) == f['sha256']
    assert len(raw.splitlines()) == f['lines']
    assert not re.search(r'\b(?:sorry|axiom|unsafe|native_decide)\b', raw)
    assert not (REPO / 'src' / (f['module'].replace('.', '/') + '.lean')).exists()
    assert f['owners'] and f['reviews']
    # Prefer the specific per-file owner when an additional group owner exists.
    owner = next((x for x in f['owners'] if
        Path(x['path']).stem.startswith(f['module'].split('.')[-1])), f['owners'][0])
    assert digest(owner['path']) == owner['sha256']
    full = []
    for r in f['reviews']:
        assert digest(r['path']) == r['sha256']
        data = json.loads(Path(r['path']).read_text())
        verdict = data.get('result', data.get('status', data.get('verdict', '')))
        assert 'passed' in verdict.lower(), (r['path'], verdict)
        reviews[r['path']] = {'path': r['path'], 'sha256': r['sha256']}
        if 'full' in verdict.lower() or 'syntax-supersession' in verdict.lower():
            full.append(r)
    assert full, f['module']
    chosen = next((x for x in full if 'RangeProvider' not in x['path']), full[0])
    selected[f['module']] = path
    files.append({'module': f['module'], 'source': str(path),
        'file': 'src/' + f['module'].replace('.', '/') + '.lean',
        'sha256': f['sha256'], 'blob': blob(path), 'lines': f['lines'],
        'imports': imports(raw), 'public_names': names(raw),
        'reviewed_manifest': {'path': owner['path'], 'sha256': owner['sha256']},
        'independent_review': {'path': chosen['path'], 'sha256': chosen['sha256']},
        'supplemental_reviews': [{'path': r['path'], 'sha256': r['sha256']}
            for r in f['reviews'] if r['path'] != chosen['path']]})
assert len(files) == 41 and sum(f['lines'] for f in files) == 4902
installed = {str(p.relative_to(REPO / 'src')).removesuffix('.lean').replace('/', '.'): p
    for p in (REPO / 'src/ContinuousFlexibility').rglob('*.lean')}
providers = dict(installed)
for f in prior['files']:
    assert digest(f['source']) == f['sha256'] and blob(f['source']) == f['blob']
    if f['module'] not in providers:
        providers[f['module']] = Path(f['source'])
public = [name for f in files for name in f['public_names']]
assert len(public) == len(set(public)), 'internal public-name collision'
old = {name for p in providers.values() for name in names(p.read_text())}
assert not (set(public) & old), sorted(set(public) & old)
providers.update(selected)
seen, visiting, order = set(), set(), []

def walk(mod):
    if not mod.startswith('ContinuousFlexibility.') or mod in seen:
        return
    assert mod in providers, ('missing provider', mod)
    assert mod not in visiting, ('dependency cycle', mod)
    visiting.add(mod)
    for dep in imports(providers[mod].read_text()):
        walk(dep)
    visiting.remove(mod)
    seen.add(mod)
    if mod in selected:
        order.append(mod)

for mod in selected:
    walk(mod)
provider_blobs = {m: blob(providers[m]) for m in sorted(seen) if m not in selected}
record = {'kind': 'reviewed_fixed_reference_group_immutable_proposal',
    'status': 'HELD_NOT_ACTIVATED_OR_COMPILED', 'head': cp['head'], 'tree': cp['tree'],
    'main': git('rev-parse', 'origin/main'),
    'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'files': files, 'source_lines': 4902, 'public_name_count': len(public),
    'topological_order': order, 'project_closure_count': len(seen),
    'provider_blobs': provider_blobs,
    'prerequisite_group': {'path': str(prior_path), 'sha256': prior_sha},
    'inventory': {'path': str(inventory_path), 'sha256': digest(inventory_path)},
    'independent_reviews': list(reviews.values()),
    'scope': ['Same fixed positive reference gauge and actual whole-atlas geometry, operator, reference radiality and forward root/cut transmission.',
        'Qualitative same-atlas reference principal fields, actual supported auxiliary construction, and fixed radial-gauge finite principal jets.',
        'The explicit Bool radial jets, distinct-range gauge, restricted-neighborhood cut/operator and syntax-correct cut-first-jets sources are selected by their exact full reviews.',
        'The four current-main compatibility resolutions and prior proof-script repairs are tracked by exact independent provider reviews; no old immutable manifest is rewritten.',
        'No final material, CurrentJets, N04Properties or parent completion claim.'],
    'activation_gate': 'Prior 19-module actual-family group must be installed and exact current head must pass full CI before staging.'}
target = ROOT / 'n04-next-reference-group-held.json'
assert not target.exists()
target.write_text(json.dumps(record, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'proposal': str(target), 'sha256': digest(target), 'files': len(files),
    'lines': 4902, 'public_names': len(public), 'closure': len(seen),
    'providers': len(provider_blobs), 'independent_reviews': len(reviews)}))
