"""Verify the retained 41-source reference family; activate only after exact full CI."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import re
import subprocess

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
PROPOSAL = ROOT / 'n04-next-reference-group-held.json'
PROPOSAL_SHA = 'e3df495b387d253732915923b113924c74fef74b8dd51310d20bcdbe68408f50'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO, text=True).strip()

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def blob(path):
    raw = Path(path).read_bytes()
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()

def imports(text):
    return re.findall(r'^import\s+(\S+)', text, re.M)

def names(text):
    return re.findall(r'^(?:(?:noncomputable|protected)\s+)?'
        r'(?:theorem|def|structure|abbrev|class|inductive|opaque)\s+([^\s(:{]+)', text, re.M)

parser = argparse.ArgumentParser()
parser.add_argument('--stage-label', type=int)
args = parser.parse_args()
assert digest(PROPOSAL) == PROPOSAL_SHA
proposal = json.loads(PROPOSAL.read_text())
ledger_path = ROOT / 'n04-reviewed-provider-rebindings-ci148.json'
ledger_sha = '0ddeba8feb48ce3bd897d07c3bf77e28c85033c5f203f614f24c924e840388d2'
assert digest(ledger_path) == ledger_sha
ledger = json.loads(ledger_path.read_text())
repaired = ledger['transitions']
for review in ledger['reviews']:
    assert digest(review['path']) == review['sha256']
for edges in repaired.values():
    for edge in edges:
        for side in ('before', 'after'):
            source = edge[side + '_source']
            assert digest(source['path']) == source['sha256']
            assert blob(source['path']) == source['blob'] == edge[side]
        assert digest(edge['review']) == edge['review_sha256']

def provider_matches(mod, expected, actual):
    if actual == expected:
        return True
    queue, visited = [expected], set()
    while queue:
        current = queue.pop()
        if current in visited:
            continue
        visited.add(current)
        for edge in repaired.get(mod, []):
            if edge['before'] == current:
                if edge['after'] == actual:
                    return True
                queue.append(edge['after'])
    return False

cp_path = ROOT / 'n04-active-checkpoint.json'
cp_bytes = cp_path.read_bytes()
cp = json.loads(cp_bytes)
assert not git('status', '--porcelain')
assert git('rev-parse', 'HEAD') == cp['head']
assert git('rev-parse', 'HEAD^{tree}') == cp['tree']
assert git('merge-base', 'HEAD', 'origin/main') == git('rev-parse', 'origin/main')
files = proposal['files']
assert len(files) == 41
selected = {f['module']: Path(f['source']) for f in files}
public = []
for f in files:
    src = Path(f['source'])
    text = src.read_text()
    assert digest(src) == f['sha256'] and blob(src) == f['blob']
    assert len(text.splitlines()) == f['lines']
    assert imports(text) == f['imports'] and names(text) == f['public_names']
    assert not (REPO / f['file']).exists()
    assert not re.search(r'\b(?:sorry|axiom|unsafe|native_decide)\b', text)
    for key in ('reviewed_manifest', 'independent_review'):
        assert digest(f[key]['path']) == f[key]['sha256']
    for extra in f['supplemental_reviews']:
        assert digest(extra['path']) == extra['sha256']
    public += f['public_names']
assert len(public) == len(set(public)) == proposal['public_name_count'] == 105
installed = {str(p.relative_to(REPO / 'src')).removesuffix('.lean').replace('/', '.'): p
    for p in (REPO / 'src/ContinuousFlexibility').rglob('*.lean')}
prerequisite = proposal['prerequisite_group']
assert digest(prerequisite['path']) == prerequisite['sha256']
prior = json.loads(Path(prerequisite['path']).read_text())
prior_sources = {f['module']: Path(f['source']) for f in prior['files']}
missing_prior = []
providers = dict(installed)
for f in prior['files']:
    if f['module'] not in installed:
        missing_prior.append(f['module'])
        assert digest(f['source']) == f['sha256'] and blob(f['source']) == f['blob']
        providers[f['module']] = Path(f['source'])
    else:
        assert provider_matches(f['module'], f['blob'], blob(installed[f['module']])), f['module']
for mod, expected in proposal['provider_blobs'].items():
    assert mod in providers and provider_matches(mod, expected, blob(providers[mod])), mod
old_names = {n for p in providers.values() for n in names(p.read_text())}
assert not (set(public) & old_names), sorted(set(public) & old_names)
providers.update(selected)
seen, visiting, order = set(), set(), []

def walk(mod):
    if not mod.startswith('ContinuousFlexibility.') or mod in seen:
        return
    assert mod in providers and mod not in visiting, mod
    visiting.add(mod)
    for dep in imports(providers[mod].read_text()):
        walk(dep)
    visiting.remove(mod)
    seen.add(mod)
    if mod in selected:
        order.append(mod)

for mod in proposal['topological_order']:
    walk(mod)
assert order == proposal['topological_order']
assert len(seen) == proposal['project_closure_count'] == 865
assert digest(proposal['inventory']['path']) == proposal['inventory']['sha256']
for review in proposal['independent_reviews']:
    assert digest(review['path']) == review['sha256']
assert len(proposal['independent_reviews']) == 34
report = {'kind': 'reference_family_static_preflight', 'status': 'HELD_NOT_ACTIVATED',
    'checked_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'head': cp['head'], 'tree': cp['tree'], 'proposal': str(PROPOSAL),
    'proposal_sha256': PROPOSAL_SHA, 'files': 41, 'source_lines': 4902,
    'project_closure': 865, 'providers': 824, 'public_names': 105, 'unique_reviews': 34,
    'reviewed_provider_transition_graph': {'path': str(ledger_path), 'sha256': ledger_sha},
    'reviewed_provider_rebindings': repaired,
    'missing_prerequisite_modules': missing_prior, 'current_ci': cp['current_ci']}
report_path = ROOT / 'n04-next-reference-current-preflight.json'
report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
if args.stage_label is not None:
    assert not missing_prior
    assert cp['current_ci']['status'] == 'success'
    assert cp['last_full_green']['sha'] == cp['head']
    assert args.stage_label == cp['current_ci']['label'] + 1
    plan_path = ROOT / f'n04-ci{args.stage_label}-plan.json'
    payload_path = ROOT / f'n04-ci{args.stage_label}-tree-payload.json'
    assert not plan_path.exists() and not payload_path.exists()
    for f in files:
        (REPO / f['file']).write_bytes(Path(f['source']).read_bytes())
    subprocess.run(['python3', 'scripts/gen_root.py'], cwd=REPO, check=True)
    paths = [f['file'] for f in files] + ['src/ContinuousFlexibility.lean']
    subprocess.run(['git', 'add', '--', *paths], cwd=REPO, check=True)
    subprocess.run(['git', 'diff', '--cached', '--check'], cwd=REPO, check=True)
    assert set(git('diff', '--cached', '--name-only').splitlines()) == set(paths)
    assert not git('diff', '--name-only')
    stats = git('diff', '--cached', '--numstat', cp['last_full_green']['sha'], '--', '*.lean')
    added = sum(int(row.split('\t')[0]) for row in stats.splitlines())
    deleted = sum(int(row.split('\t')[1]) for row in stats.splitlines())
    assert added == 4943 and deleted == 0 and added <= 20000
    payload = {'repository_full_name': 'Rogerhu12/continuous-flexibility',
        'base_tree_sha': cp['tree'], 'tree_elements': [
            {'path': p, 'mode': '100644', 'type': 'blob', 'content': (REPO / p).read_text()}
            for p in paths]}
    payload_path.write_text(json.dumps(payload, ensure_ascii=False))
    plan = {'label': args.stage_label, 'parent': cp['head'], 'base_tree': cp['tree'],
        'tree': git('write-tree'), 'added': added, 'deleted': deleted,
        'changed_lean_files': len(paths), 'payload': str(payload_path),
        'held_group': str(PROPOSAL), 'held_group_sha256': PROPOSAL_SHA,
        'preflight': str(report_path), 'preflight_sha256': digest(report_path),
        'current_main': git('rev-parse', 'origin/main'),
        'source_all_total': len(list((REPO / 'src/ContinuousFlexibility').rglob('*.lean'))),
        'all_src_lean_including_library_roots': len(list((REPO / 'src').rglob('*.lean'))),
        'generated_root_imports': len(imports((REPO / 'src/ContinuousFlexibility.lean').read_text()))}
    plan_path.write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(plan))
else:
    print(json.dumps({k: v for k, v in report.items() if k != 'current_ci'}, ensure_ascii=False))
assert cp_path.read_bytes() == cp_bytes
