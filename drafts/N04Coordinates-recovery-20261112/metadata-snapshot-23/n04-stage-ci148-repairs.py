"""Activate only the five fully reviewed exact CI147 elaboration repairs."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
DRAFTS = ROOT / 'n04-drafts'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO, text=True).strip()

def record(path):
    raw = Path(path).read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(),
        'blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
        'lines': len(raw.splitlines())}

def verify(item):
    actual = record(item['path'])
    for key in ('sha256', 'blob', 'lines'):
        if key in item:
            assert actual[key] == item[key], (item['path'], key)

def load_verified(path, expected):
    assert record(path)['sha256'] == expected, path
    value = json.loads(path.read_text())
    return value, record(path)

cp_path = ROOT / 'n04-active-checkpoint.json'
cp_raw = cp_path.read_bytes()
cp = json.loads(cp_raw)
assert git('branch', '--show-current') == 'line/N04Coordinates'
assert not git('status', '--porcelain')
assert git('rev-parse', 'HEAD') == cp['head'] == '2058ced3cbf364e7e3ec9980dc76a90785890554'
assert git('rev-parse', 'HEAD^{tree}') == cp['tree'] == '412f884b14caddd7586ab614ff4d092ef093849b'
assert cp['current_ci']['label'] == 147 and cp['current_ci']['conclusion'] == 'failure'
assert cp['last_full_green']['sha'] == '03e526021c371413f03fc0ce052476b63e105361'
assert git('merge-base', 'HEAD', 'origin/main') == git('rev-parse', 'origin/main')

specs = [
    ('root/repair147/AtlasAliasCI147ReviewedManifest.json',
     '52713e45c4fc6a24de99e55d61467b8f6e62ba07008d073a085afd1c244991c6'),
    ('quantitative/repair147/CI147TwoQuantitativeRepairsReviewedManifest.json',
     'f2d3090040a00517a1166a95fbf0e33e43bfbdbab94937a085c63007c7651d74'),
    ('audit/repair147/N03RootEndpointPhysicalJetsRepairReviewedManifest.json',
     '5d0822047694e746a7783c31fd7c1fceb36414737ed7ab25ac89ceed1ea43d13')]
owners, reviews, files = [], [], []
for i, (name, expected) in enumerate(specs):
    owner, owner_record = load_verified(DRAFTS / name, expected)
    owners.append(owner_record)
    verify(owner['candidate_manifest'])
    verify(owner['independent_review'])
    reviews.append(owner['independent_review'])
    review = json.loads(Path(owner['independent_review']['path']).read_text())
    if i == 0:
        for row in review['sources']:
            files.append({'target_path': row['target'], 'before': row['base'],
                'after': row['source'], 'diff': row['diff']})
    elif i == 1:
        for row in review['rows']:
            files.append({'target_path': row['target'], 'before': row['base'],
                'after': row['after'], 'diff': row['diff']})
    else:
        files.append({k: review[k] for k in ('target_path', 'before', 'after', 'diff')})
assert len(files) == 5
for item in files:
    for side in ('before', 'after', 'diff'):
        verify(item[side])
    target = REPO / item['target_path']
    assert target.read_bytes() == Path(item['before']['path']).read_bytes()
    source = Path(item['after']['path']).read_text()
    assert not re.search(r'\b(?:sorry|axiom|unsafe|native_decide)\b', source)
    assert re.findall(r'^set_option .*$', source, re.M) == re.findall(
        r'^set_option .*$', target.read_text(), re.M)

plan_path = ROOT / 'n04-ci148-plan.json'
payload_path = ROOT / 'n04-ci148-tree-payload.json'
assert not plan_path.exists() and not payload_path.exists()
for item in files:
    (REPO / item['target_path']).write_bytes(Path(item['after']['path']).read_bytes())
subprocess.run(['python3', 'scripts/gen_root.py'], cwd=REPO, check=True)
paths = sorted(item['target_path'] for item in files)
assert set(git('diff', '--name-only').splitlines()) == set(paths)
subprocess.run(['git', 'add', '--', *paths], cwd=REPO, check=True)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=REPO, check=True)
assert not git('diff', '--name-only')
assert sorted(git('diff', '--cached', '--name-only').splitlines()) == paths
stats = git('diff', '--cached', '--numstat', cp['last_full_green']['sha'], '--', '*.lean')
added = sum(int(row.split('\t')[0]) for row in stats.splitlines())
deleted = sum(int(row.split('\t')[1]) for row in stats.splitlines())
assert added == 2922 and deleted == 0 and added <= 20000
payload = {'repository_full_name': 'Rogerhu12/continuous-flexibility',
    'base_tree_sha': cp['tree'], 'tree_elements': [
        {'path': path, 'mode': '100644', 'type': 'blob', 'content': (REPO / path).read_text()}
        for path in paths]}
payload_path.write_text(json.dumps(payload, ensure_ascii=False))
plan = {'label': 148, 'parent': cp['head'], 'base_tree': cp['tree'],
    'tree': git('write-tree'), 'current_main': git('rev-parse', 'origin/main'),
    'files': files, 'owners': owners, 'reviews': reviews, 'paths': paths,
    'added_since_full_green': added, 'deleted_since_full_green': deleted,
    'payload': str(payload_path), 'payload_sha256': record(payload_path)['sha256'],
    'payload_codepoints': len(payload_path.read_text()),
    'project_source_total': len(list((REPO / 'src/ContinuousFlexibility').rglob('*.lean'))),
    'all_src_lean_including_library_roots': len(list((REPO / 'src').rglob('*.lean'))),
    'generated_root_imports': len(re.findall(r'^import ',
        (REPO / 'src/ContinuousFlexibility.lean').read_text(), re.M)),
    'status': 'Five exact reviewed CI147 repairs staged; not compiled.',
    'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat()}
plan_path.write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
assert cp_path.read_bytes() == cp_raw
print(json.dumps({k:v for k,v in plan.items() if k not in ('files','owners','reviews')}, indent=2))
