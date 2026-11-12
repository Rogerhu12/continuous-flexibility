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
ACTUAL = '34a496f78ec2c9f35f74d2eb3dfd48a1d4190909'
INPUT = ROOT / 'n04-drafts/positive/gateway/n01c-n02-compat/N02N03AndCorrectedFlowParameterOrderSelectedInventory.json'
SOURCE = OUT / 'N04MinusFirstIntegralCircle.lean'
MODULE = 'ContinuousFlexibility.Analysis.N04MinusFirstIntegralCircle'

def ident(path):
    data = Path(path).read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(data).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest(),
            'lines': len(data.splitlines())}

def verify(item, data):
    assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == item['blob']
    assert len(data.splitlines()) == item['lines']

assert ident(INPUT)['sha256'] == '0ffb77aab1a331e32d8a32614f0ffea3256bfc4ae9f65dadbaf59e21ce698701'
ci = ident(INPUT)
verify(ci, Path(ci['path']).read_bytes())
selected = {x['module']: x for x in json.loads(Path(ci['path']).read_text())['modules']}
source = ident(SOURCE)
source.update(target='src/' + MODULE.replace('.', '/') + '.lean')
selected[MODULE] = {**source, 'module': MODULE, 'selected_ref': 'LOCAL_NEW_ACTUAL_MINUS_FIRST_INTEGRAL'}
raw = subprocess.check_output(['git', 'ls-tree', '-rz', GENERIC, 'src'], cwd=REPO)
tree = {}
for row in raw.split(b'\0'):
    if row:
        info, path = row.split(b'\t', 1)
        tree[path.decode()] = info.decode().split()[2]
fallback_tree = {}
for row in subprocess.check_output(['git', 'ls-tree', '-rz', ACTUAL, 'src'], cwd=REPO).split(b'\0'):
    if row:
        info, path = row.split(b'\t', 1)
        fallback_tree[path.decode()] = info.decode().split()[2]
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
        assert path in tree or path in fallback_tree, mod
        selected_blob = tree.get(path, fallback_tree.get(path))
        data = blob(selected_blob)
        item = {'module': mod, 'path': path, 'selected_ref': GENERIC if path in tree else ACTUAL,
                'sha256': hashlib.sha256(data).hexdigest(), 'blob': selected_blob,
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
closure = {'kind': 'static_exact_selected_import_inventory_not_elaboration',
    'target_module': MODULE, 'selected_generic_ref': GENERIC,
    'fallback_actual_ref': ACTUAL, 'selected_N01_contract_ref': CONTRACT,
    'module_count': len(found), 'missing': [], 'cycles': [],
    'excluded_old_uniform_loss_modules': excluded,
    'reused_inventory': ci, 'modules': [found[x] for x in sorted(found)]}
cp = OUT / 'N04MinusFirstIntegralCircleClosureInventory.json'
assert not cp.exists()
cp.write_text(json.dumps(closure, ensure_ascii=False, indent=2) + '\n')
providers = ['N04CorrectedFlowInverseCircle', 'N01ReturnInverseCircle',
    'N01CircleLinearTame', 'CircleJointEvaluation', 'N04bCharacteristicFirstIntegrals',
    'ParameterizedCircleInverse']
manifest = {'kind': 'actual_minus_first_integral_circle_and_state_angle_tower',
    'status': 'HELD_UNCOMPILED_PENDING_INDEPENDENT_REVIEW_AND_MAIN_INTEGRATION',
    'author': '/root', 'source': source, 'public_names': names,
    'selected_input_inventory': ident(INPUT), 'closure_inventory': ident(cp),
    'selected_providers': [found['ContinuousFlexibility.Analysis.' + x] for x in providers],
    'checks': [
        'The same actual corrected-flow inverse circle is composed with the prescribed left-chart coordinate, with positive opticalTravel in the composition argument.',
        'The decoded displacement is exactly the existing n04bMinusFirstIntegral minus angle plus optical travel. Its definition uses the literal fiberwise Function.invFun of that same corrected flow.',
        'Genuine smooth tame composition of the inverse and actual sector chart supplies one circle-valued family; the joint circle affine lift supplies its state-and-angle SmoothDirections tower.',
        'Full selected content fingerprints, source imports, dependency acyclicity and public-name uniqueness checked without elaboration.'],
    'scope_limits': [
        'A fixed closed radius selector is used. Radial derivatives, uniform sampled height-gain bounds and moving canonical compositions remain separate.',
        'The input selected graph is static and uncompiled. Main integration and full CI are separate gates; no semantic closure is inferred merely from imports.',
        'No final CurrentJets premise, new inverse selection, open Blueprint theorem or active source/index/ref/CI/resource-limit mutation.'],
    'compiled': False, 'independent_reviews': [],
    'created_at': datetime.now(timezone.utc).isoformat()}
mp = OUT / 'N04MinusFirstIntegralCircleCandidateManifest.json'
assert not mp.exists()
mp.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'source': source, 'manifest': ident(mp), 'closure_modules': len(found),
    'local_sources': sum(Path(x['path']).is_absolute() for x in found.values())}))
