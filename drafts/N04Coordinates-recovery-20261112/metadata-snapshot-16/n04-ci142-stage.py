"""Stage only the five independently reviewed CI141 repairs and the current main merge."""
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
HEAD = '51f748cb71b876e4664d9d750240c7522d0cf92f'
MAIN = '8cebde34f6668c523facece3312949e9dbec3444'
REVIEWS = [
    ('WholeCanonicalAtlasDataCI141IndependentReview.json',
     'a1d455a70183b3a907e1b3dea856af92665b54deede8b1573b5e7aaf2e548062'),
    ('CI141FiniteJetAndAdjugateIndependentReview.json',
     '09ffb5fdc7fe8be97d9e9d2c8b2d4599a6583e8ad2b674e1425137813f32eed9'),
    ('CI141PrincipalScalarIndependentReview.json',
     'cb4e306610e43e259ed342b16bbcce47ced68551b050e831569753ed424e244d'),
]

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

assert git('rev-parse', 'HEAD').decode().strip() == HEAD
assert git('rev-parse', 'origin/main').decode().strip() == MAIN
assert git('rev-parse', 'MERGE_HEAD').decode().strip() == MAIN
assert git('diff', '--cached', '--name-only').decode().splitlines() == ['.github/workflows/build.yml']
assert not git('diff', '--name-only').strip()
cp_bytes = (ROOT / 'n04-active-checkpoint.json').read_bytes()
cp = json.loads(cp_bytes)
assert cp['head'] == HEAD and cp['current_ci']['label'] == 141
assert cp['current_ci']['status'] == 'failure'
files = []
for name, expected in REVIEWS:
    path = ROOT / 'n04-drafts/positive/reviews' / name
    assert sha(path.read_bytes()) == expected
    review = json.loads(path.read_text())
    assert review['baseline']['head'] == HEAD
    assert review['result'] == 'passed_static_review_not_compiled'
    candidate = review['candidate_manifest']
    assert sha(Path(candidate['path']).read_bytes()) == candidate['sha256']
    for f in review['files']:
        target = REPO / f['target_path']
        for key in ('before', 'after'):
            record = f[key]
            data = Path(record['path']).read_bytes()
            assert sha(data) == record['sha256'] and blob(data) == record['blob']
            assert len(data.splitlines()) == record['lines']
        before = Path(f['before']['path']).read_bytes()
        assert target.read_bytes() == before == git('show', HEAD + ':' + f['target_path'])
        assert f['verified_exact_single_substitution']
        assert f['complete_declaration_headers_imports_options_other_bytes_unchanged']
        files.append(f)
assert len(files) == 5
for f in files:
    (REPO / f['target_path']).write_bytes(Path(f['after']['path']).read_bytes())
subprocess.run(['python3', 'scripts/gen_root.py'], cwd=REPO, check=True)
paths = ['.github/workflows/build.yml'] + [f['target_path'] for f in files]
subprocess.run(['git', 'add', '--', *paths], cwd=REPO, check=True)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=REPO, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == set(paths)
assert not git('diff', '--name-only').strip()
assert not git('ls-files', '--others', '--exclude-standard').strip()
stats = git('diff', '--cached', '--numstat', cp['last_full_green']['sha'], '--', '*.lean').decode()
added = sum(int(x.split('\t')[0]) for x in stats.splitlines())
deleted = sum(int(x.split('\t')[1]) for x in stats.splitlines())
assert added == 2808 and deleted == 0 and added < 20000
payload = {'repository_full_name': 'Rogerhu12/continuous-flexibility',
           'base_tree_sha': cp['tree'],
           'tree_elements': [{'path': p, 'mode': '100644', 'type': 'blob',
                              'content': (REPO / p).read_text()} for p in paths]}
payload_text = json.dumps(payload, ensure_ascii=False)
(ROOT / 'n04-ci142-tree-payload.json').write_text(payload_text)
plan = {'label': 142, 'parent': HEAD, 'additional_parents': [MAIN],
        'base_tree': cp['tree'], 'tree': git('write-tree').decode().strip(),
        'current_main': MAIN, 'added_since_green': added, 'deleted_since_green': deleted,
        'payload': str(ROOT / 'n04-ci142-tree-payload.json'),
        'payload_sha256': sha(payload_text.encode()), 'payload_codepoints': len(payload_text),
        'files': files, 'reviews': REVIEWS, 'paths': paths,
        'source_all_total': 3681, 'generated_root_imports': 3624,
        'status': 'Staged precise repairs; not compiled.'}
(ROOT / 'n04-ci142-plan.json').write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
assert (ROOT / 'n04-active-checkpoint.json').read_bytes() == cp_bytes
print(json.dumps({k: v for k, v in plan.items() if k not in ('files', 'reviews')}, ensure_ascii=False))
