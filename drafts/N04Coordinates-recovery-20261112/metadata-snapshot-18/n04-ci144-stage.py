"""Stage the three independently reviewed CI143 proof repairs."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
HEAD = '597e5c478ed253d74b89cb7a077dc39a12acc44c'
REVIEW = ROOT / 'n04-drafts/audit/reviews/CI143WholeAtlasThreeRepairsIndependentReview.json'
REVIEW_SHA = 'a8f1b638e108c6a115a3cca9c0045d85a5b435978a32ffb0e4e5f2d1659b957b'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

assert git('rev-parse', 'HEAD').decode().strip() == HEAD
assert not git('status', '--porcelain').strip()
cp_path = ROOT / 'n04-active-checkpoint.json'
cp_bytes = cp_path.read_bytes()
cp = json.loads(cp_bytes)
assert cp['head'] == HEAD and cp['current_ci']['label'] == 143
assert cp['current_ci']['status'] == 'failure'
assert sha(REVIEW.read_bytes()) == REVIEW_SHA
review = json.loads(REVIEW.read_text())
assert review['actual_base_commit'] == HEAD
assert review['actual_base_tree'] == cp['tree']
assert review['result'] == 'passed_full_source_exact_delta_and_actual_provider_static_review'
for record in [*review['candidate_manifests'], review['cached_log'], *review['actual_providers']]:
    assert sha(Path(record['path']).read_bytes()) == record['sha256']
files = review['sources']
assert len(files) == 3
for f in files:
    for key in ('before', 'after', 'diff'):
        data = Path(f[key]['path']).read_bytes()
        assert sha(data) == f[key]['sha256'] and blob(data) == f[key]['blob']
        assert len(data.splitlines()) == f[key]['lines']
    before = Path(f['before']['path']).read_bytes()
    after = Path(f['after']['path']).read_bytes()
    assert before == (REPO / f['target_path']).read_bytes()
    assert before == git('show', HEAD + ':' + f['target_path'])
    headers = lambda raw: re.findall(rb'^theorem\b[\s\S]*?(?=:=)', raw, re.M)
    assert headers(before) == headers(after)
    assert re.findall(rb'^import .+$', before, re.M) == re.findall(rb'^import .+$', after, re.M)
for f in files:
    (REPO / f['target_path']).write_bytes(Path(f['after']['path']).read_bytes())
subprocess.run(['python3', 'scripts/gen_root.py'], cwd=REPO, check=True)
paths = [f['target_path'] for f in files]
subprocess.run(['git', 'add', '--', *paths], cwd=REPO, check=True)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=REPO, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == set(paths)
assert not git('diff', '--name-only').strip()
assert not git('ls-files', '--others', '--exclude-standard').strip()
stats = git('diff', '--cached', '--numstat', cp['last_full_green']['sha'], '--', '*.lean').decode()
added = sum(int(x.split('\t')[0]) for x in stats.splitlines())
deleted = sum(int(x.split('\t')[1]) for x in stats.splitlines())
assert added == 2862 and deleted == 0 and added < 20000
payload = {'repository_full_name': 'Rogerhu12/continuous-flexibility',
           'base_tree_sha': cp['tree'],
           'tree_elements': [{'path': p, 'mode': '100644', 'type': 'blob',
                              'content': (REPO / p).read_text()} for p in paths]}
payload_text = json.dumps(payload, ensure_ascii=False)
(ROOT / 'n04-ci144-tree-payload.json').write_text(payload_text)
plan = {'label': 144, 'parent': HEAD, 'base_tree': cp['tree'],
        'tree': git('write-tree').decode().strip(),
        'main_included': '8cebde34f6668c523facece3312949e9dbec3444',
        'current_main_checked': git('rev-parse', 'origin/main').decode().strip(),
        'pending_main_merge_reason': cp['pending_main_merge']['reason'],
        'added_since_green': added, 'deleted_since_green': deleted,
        'payload': str(ROOT / 'n04-ci144-tree-payload.json'),
        'payload_sha256': sha(payload_text.encode()), 'payload_codepoints': len(payload_text),
        'files': files, 'independent_review': {'path': str(REVIEW), 'sha256': REVIEW_SHA},
        'paths': paths, 'source_all_total': 3681, 'generated_root_imports': 3624,
        'status': 'Staged three precise CI143 proof repairs; not compiled.'}
(ROOT / 'n04-ci144-plan.json').write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
assert cp_path.read_bytes() == cp_bytes
print(json.dumps({k: v for k, v in plan.items() if k not in ('files',)}, ensure_ascii=False))
