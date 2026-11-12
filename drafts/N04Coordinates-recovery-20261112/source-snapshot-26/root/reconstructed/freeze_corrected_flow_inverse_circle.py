from pathlib import Path
import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
OUT = ROOT / 'n04-drafts/root/reconstructed'
GENERIC = 'c5c48d262157a11a76604113c40d2438d480433f'
CONTRACT = 'bb419aa4e85af1b01a3edb0f6113e5f0a242f6d7'
INPUT = OUT / 'N04CorrectedFlowCircleCandidateManifest.json'
SOURCE = OUT / 'N04CorrectedFlowInverseCircle.lean'
MODULE = 'ContinuousFlexibility.Analysis.N04CorrectedFlowInverseCircle'

def ident(path):
    data = Path(path).read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(data).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest(),
            'lines': len(data.splitlines())}

def verify(item, data):
    assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == item['blob']
    assert len(data.splitlines()) == item['lines']

mf = json.loads(INPUT.read_text())
ci = mf['closure_inventory']
verify(ci, Path(ci['path']).read_bytes())
selected = {x['module']: x for x in json.loads(Path(ci['path']).read_text())['modules']}
source = ident(SOURCE)
source.update(target='src/' + MODULE.replace('.', '/') + '.lean')
selected[MODULE] = {**source, 'module': MODULE, 'selected_ref': 'LOCAL_NEW_CORRECTED_FLOW_INVERSE'}
raw = subprocess.check_output(['git', 'ls-tree', '-rz', GENERIC, 'src'], cwd=REPO)
tree = {}
for row in raw.split(b'\0'):
    if row:
        info, path = row.split(b'\t', 1)
        tree[path.decode()] = info.decode().split()[2]
proc = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=REPO,
    stdin=subprocess.PIPE, stdout=subprocess.PIPE)
def blob(sha):
    proc.stdin.write((sha + '\n').encode())
    proc.stdin.flush()
    h = proc.stdout.readline().decode().split()
    assert h[1] == 'blob'
    data = proc.stdout.read(int(h[2]))
    assert proc.stdout.read(1) == b'\n'
    return data

found, pending, contents = {}, [MODULE], {}
while pending:
    mod = pending.pop()
    if mod in found:
        continue
    if mod in selected:
        item = dict(selected[mod])
        data = Path(item['path']).read_bytes() if Path(item['path']).is_absolute() else blob(item['blob'])
        verify(item, data)
    else:
        path = 'src/' + mod.replace('.', '/') + '.lean'
        assert path in tree, mod
        data = blob(tree[path])
        item = {'module': mod, 'path': path, 'selected_ref': GENERIC,
                'sha256': hashlib.sha256(data).hexdigest(), 'blob': tree[path],
                'lines': len(data.splitlines())}
    imports = re.findall(r'^import\s+(\S+)', data.decode(), re.M)
    if 'imports' in item:
        assert item['imports'] == imports
    item['imports'] = imports
    found[mod], contents[mod] = item, data.decode()
    pending += [x for x in imports if x.startswith('ContinuousFlexibility.')]
proc.stdin.close()
proc.wait()
active, done = set(), set()
def visit(mod):
    assert mod not in active, mod
    if mod in done:
        return
    active.add(mod)
    for dep in found[mod]['imports']:
        if dep in found:
            visit(dep)
    active.remove(mod)
    done.add(mod)
visit(MODULE)
names = re.findall(r'^(?:def|theorem)\s+(\S+)', SOURCE.read_text(), re.M)
for mod, text in contents.items():
    if mod != MODULE:
        for name in names:
            assert not re.search(r'^(?:def|theorem)\s+' + re.escape(name) + r'\b', text, re.M)
excluded = ['ContinuousFlexibility.Analysis.N01SectorFlowTower',
            'ContinuousFlexibility.Analysis.N01EndpointParameterTower']
assert not any(x in found for x in excluded)
pending_providers = [x for x in [
    'ContinuousFlexibility.Analysis.N01FlowParameterVariation',
    'ContinuousFlexibility.Analysis.N01FlowMixedParameterBound'] if x in found]
closure = {'kind': 'static_exact_selected_import_inventory_not_elaboration',
    'target_module': MODULE, 'selected_generic_ref': GENERIC, 'selected_N01_contract_ref': CONTRACT,
    'module_count': len(found), 'missing': [], 'cycles': [], 'excluded_old_uniform_loss_modules': excluded,
    'known_pending_provider_ports': pending_providers,
    'reused_inventory': ci, 'modules': [found[x] for x in sorted(found)]}
cp = OUT / 'N04CorrectedFlowInverseCircleClosureInventory.json'
assert not cp.exists()
cp.write_text(json.dumps(closure, ensure_ascii=False, indent=2) + '\n')
providers = ['N04CorrectedFlowCircle', 'N01InterpolationInverseCircle', 'N01SelectorInverse',
    'CirclePositiveInversePerturbation', 'CirclePositiveInverseSmoothTame', 'CircleJointEvaluation']
manifest = {'kind': 'actual_corrected_flow_inverse_circle_and_state_angle_tower',
    'status': 'HELD_UNCOMPILED_PENDING_INDEPENDENT_REVIEW_AND_PROVIDER_PORTS',
    'author': '/root', 'source': source, 'public_names': names,
    'input_candidate_manifest': ident(INPUT), 'closure_inventory': ident(cp),
    'selected_providers': [found['ContinuousFlexibility.Analysis.' + x] for x in providers],
    'checks': [
        'The positive derivative is proved for the actual composition from the existing original-flow and actual interpolation positive-lift certificates. The scalar chain rule gives the literal corrected flow derivative.',
        'The affine inverse is identified by complete function equality with Function.invFun of that same corrected flow; no separately selected inverse is substituted.',
        'The existing positive-inverse circle operator supplies its actual inverse displacement. The decoder retains exactly the opposite original optical translation.',
        'Smooth tameness is genuine composition on the positive-lift domain. The same realized inverse circle tower and joint decoder give an actual state-and-angle SmoothDirections tower.',
        'All exact selected contents, source identities and acyclicity were checked; upstream parameter-loss ports remain separately marked pending.'],
    'scope_limits': [
        'A fixed closed radius selector is used; radial derivatives, quantitative height-gain bounds and moving canonical coordinates remain separate.',
        'The complete selected graph is uncompiled. The two recorded c5 flow-variation providers still require their explicitly assigned parameter-loss ports; static import closure is not semantic or compiler closure.',
        'No final CurrentJets premise, open Blueprint theorem, active source/index/ref or toolchain/resource-limit mutation is introduced.'],
    'compiled': False, 'independent_reviews': [],
    'created_at': datetime.now(timezone.utc).isoformat()}
mp = OUT / 'N04CorrectedFlowInverseCircleCandidateManifest.json'
assert not mp.exists()
mp.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'source': source, 'manifest': ident(mp), 'closure_modules': len(found),
    'pending_provider_ports': pending_providers}))
