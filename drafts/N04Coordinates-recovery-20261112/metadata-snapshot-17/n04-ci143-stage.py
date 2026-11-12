"""Stage the five reviewed CI142 repairs before the large N06 integration merge."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
HEAD = '7a9eaacbc01e206ab2a91cc1d538cc48505130d9'
REVIEWS = [
    ('root/reviews/WholePositivePrincipalJetMatchingCI142IndependentReview.json',
     '0309eed545bf2fc260c69e7ab1c0935ca5c6766b3c19de43601ac99d92dd4f91'),
    ('quantitative/recovery/reviews/CI142WholeAtlasTwoRepairsIndependentReview.json',
     '922df76b0d5e8e8660f76897faeaa438f52202f065d65c2135f278dfc32131ac'),
    ('positive/reviews/CI142WholeAtlasFieldRepairsIndependentReview.json',
     '16f340575c7af3ce10995f159310bc3fc45dd4b110509bb231f34f51545ed870'),
]

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
assert cp['head'] == HEAD and cp['current_ci']['label'] == 142
assert cp['current_ci']['status'] == 'failure'
files = []
for name, expected in REVIEWS:
    path = ROOT / 'n04-drafts' / name
    assert sha(path.read_bytes()) == expected
    review = json.loads(path.read_text())
    assert review['baseline']['head'] == HEAD and review['result'].startswith('passed_static')
    candidate = review['candidate_manifest']
    assert sha(Path(candidate['path']).read_bytes()) == candidate['sha256']
    for record in review['files']:
        f = dict(record)
        f['target_path'] = f.get('target_path', f.get('path'))
        for key in ('before', 'after'):
            data = Path(f[key]['path']).read_bytes()
            assert sha(data) == f[key]['sha256'] and blob(data) == f[key]['blob']
            if 'lines' in f[key]:
                assert len(data.splitlines()) == f[key]['lines']
        before = Path(f['before']['path']).read_bytes()
        after = Path(f['after']['path']).read_bytes()
        assert before == (REPO / f['target_path']).read_bytes()
        assert before == git('show', HEAD + ':' + f['target_path'])
        heads = lambda raw: re.findall(rb'^theorem\b[\s\S]*?(?=:=)', raw, re.M)
        assert heads(before) == heads(after)
        assert re.findall(rb'^import .+$', before, re.M) == re.findall(rb'^import .+$', after, re.M)
        f['independent_review'] = {'path': str(path), 'sha256': expected}
        files.append(f)
assert len(files) == 5
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
assert added == 2836 and deleted == 0 and added < 20000
payload = {'repository_full_name': 'Rogerhu12/continuous-flexibility',
           'base_tree_sha': cp['tree'],
           'tree_elements': [{'path': p, 'mode': '100644', 'type': 'blob',
                              'content': (REPO / p).read_text()} for p in paths]}
payload_text = json.dumps(payload, ensure_ascii=False)
(ROOT / 'n04-ci143-tree-payload.json').write_text(payload_text)
plan = {'label': 143, 'parent': HEAD, 'base_tree': cp['tree'],
        'tree': git('write-tree').decode().strip(),
        'main_included': '8cebde34f6668c523facece3312949e9dbec3444',
        'current_main_checked': git('rev-parse', 'origin/main').decode().strip(),
        'pending_main_merge_reason': 'Main integrated N06 after CI142. Finish the current five-module repair group first, then merge and validate main before any new source activation. Nonlinear and Blueprint statement interfaces used here are unchanged.',
        'added_since_green': added, 'deleted_since_green': deleted,
        'payload': str(ROOT / 'n04-ci143-tree-payload.json'),
        'payload_sha256': sha(payload_text.encode()), 'payload_codepoints': len(payload_text),
        'files': files, 'reviews': REVIEWS, 'paths': paths,
        'source_all_total': 3681, 'generated_root_imports': 3624,
        'status': 'Staged precise CI142 repairs; not compiled.'}
(ROOT / 'n04-ci143-plan.json').write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
assert cp_path.read_bytes() == cp_bytes
print(json.dumps({k: v for k, v in plan.items() if k not in ('files', 'reviews')}, ensure_ascii=False))
