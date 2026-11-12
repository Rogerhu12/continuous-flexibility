"""Integrate the verified upstream N06 tree after the current repair group is green."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
MAIN = 'ebfd528f2dd0c690799187be45b7c5a5c4c6b26a'
REVIEW = ROOT / 'n04-drafts/quantitative/recovery/reviews/MainN06CompatibilityIndependentReview.json'
REVIEW_SHA = 'ca74c6028f4668a8294d5afb35447bd35944ecbbb628a8016789ecbd516b3722'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

cp_path = ROOT / 'n04-active-checkpoint.json'
cp_bytes = cp_path.read_bytes()
cp = json.loads(cp_bytes)
assert cp['current_ci']['status'] == 'success'
assert cp['last_full_green']['sha'] == cp['head']
assert git('rev-parse', 'HEAD').decode().strip() == cp['head']
merge_state = subprocess.run(['git', 'rev-parse', '-q', '--verify', 'MERGE_HEAD'],
    cwd=REPO, capture_output=True, text=True)
resuming = merge_state.returncode == 0
if resuming:
    assert merge_state.stdout.strip() == MAIN
else:
    assert not git('status', '--porcelain').strip()
assert git('rev-parse', 'origin/main').decode().strip() == MAIN
assert sha(REVIEW.read_bytes()) == REVIEW_SHA
review = json.loads(REVIEW.read_text())
candidate = review['candidate_manifest']
assert sha(Path(candidate['path']).read_bytes()) == candidate['sha256']
assert review['main'] == MAIN
for f in review['files']:
    before = Path(f['before']['path']).read_bytes()
    after = Path(f['after']['path']).read_bytes()
    assert sha(before) == f['before']['sha256']
    assert sha(after) == f['after']['sha256']
    assert (REPO / f['target_path']).read_bytes() == (after if resuming else before)
    assert git('show', 'HEAD:' + f['target_path']) == before

upstream_receipt = json.loads((ROOT / 'n04-main-n06-upstream-ci.json').read_text())
assert upstream_receipt['integration']['head'] == '898ddb7862b9c2b4c60afcc1363cb169287c9bda'
assert upstream_receipt['integration']['conclusion'] == 'success'
assert upstream_receipt['line']['conclusion'] == 'success'
merge_base = git('merge-base', 'HEAD', MAIN).decode().strip()
label = cp['current_ci']['label'] + 1
plan_path = ROOT / f'n04-ci{label}-plan.json'
payload_path = ROOT / f'n04-ci{label}-tree-payload.json'
assert not plan_path.exists() and not payload_path.exists()
if not resuming:
    result = subprocess.run(['git', 'merge', '--no-commit', '--no-ff', MAIN], cwd=REPO,
                            capture_output=True, text=True)
    assert result.returncode in (0, 1), result.stderr
conflicts = set(git('diff', '--name-only', '--diff-filter=U').decode().splitlines())
assert conflicts <= {'src/ContinuousFlexibility.lean',
    'src/ContinuousFlexibility/Analysis/CanonicalBoundaryImage.lean',
    'src/ContinuousFlexibility/Analysis/CanonicalStripGeometry.lean'}, conflicts
for f in review['files']:
    (REPO / f['target_path']).write_bytes(Path(f['after']['path']).read_bytes())
subprocess.run(['python3', 'scripts/gen_root.py'], cwd=REPO, check=True)
subprocess.run(['git', 'add', '--', 'src/ContinuousFlexibility.lean',
    *[f['target_path'] for f in review['files']]], cwd=REPO, check=True)
assert not git('diff', '--name-only', '--diff-filter=U').strip()
assert not git('diff', '--name-only').strip()
whitespace = subprocess.run(['git', 'diff', '--cached', '--check'], cwd=REPO,
    capture_output=True, text=True)
inherited_whitespace = []
for diagnostic in whitespace.stdout.splitlines():
    match = re.fullmatch(r'(.+):[0-9]+: new blank line at EOF\.', diagnostic)
    assert match, diagnostic
    path = match.group(1)
    assert (REPO / path).read_bytes() == git('show', MAIN + ':' + path)
    inherited_whitespace.append(diagnostic)
assert whitespace.returncode in (0, 2) and not whitespace.stderr
subprocess.run(['git', 'diff', '--cached', '--check', '--',
    'src/ContinuousFlexibility.lean', *[f['target_path'] for f in review['files']]],
    cwd=REPO, check=True)
assert git('rev-parse', 'MERGE_HEAD').decode().strip() == MAIN
tree = git('write-tree').decode().strip()

known_blobs = set()
for ref in (cp['head'], MAIN):
    for row in git('ls-tree', '-r', ref).decode().splitlines():
        meta, _ = row.split('\t', 1)
        mode, kind, blob = meta.split()
        if kind == 'blob':
            known_blobs.add(blob)
paths = git('diff', '--cached', '--name-only', cp['head']).decode().splitlines()
elements = []
new_blob_paths = []
for path in paths:
    entries = git('ls-files', '--stage', '--', path).decode().splitlines()
    if not entries:
        elements.append({'path': path, 'mode': '100644', 'type': 'blob', 'sha': None})
        continue
    assert len(entries) == 1
    meta, actual_path = entries[0].split('\t', 1)
    mode, blob, stage = meta.split()
    assert actual_path == path and stage == '0'
    entry = {'path': path, 'mode': mode, 'type': 'blob'}
    if blob in known_blobs:
        entry['sha'] = blob
    else:
        entry['content'] = (REPO / path).read_text()
        new_blob_paths.append(path)
    elements.append(entry)

def additions(ref, cached=False):
    args = ['diff'] + (['--cached'] if cached else []) + ['--numstat', ref]
    if not cached:
        args.append(MAIN)
    args += ['--', '*.lean']
    rows = git(*args).decode().splitlines()
    return sum(int(x.split('\t')[0]) for x in rows), sum(int(x.split('\t')[1]) for x in rows)

raw_added, raw_deleted = additions(cp['head'], True)
upstream_added, upstream_deleted = additions(merge_base)
own_new_lines = sum(len((REPO / p).read_text().splitlines()) for p in new_blob_paths
                    if p.endswith('.lean') and p != 'src/ContinuousFlexibility.lean')
assert own_new_lines < 20000
payload = {'repository_full_name': 'Rogerhu12/continuous-flexibility',
    'base_tree_sha': cp['tree'], 'tree_elements': elements}
text = json.dumps(payload, ensure_ascii=False)
payload_path.write_text(text)
plan = {'label': label, 'parent': cp['head'], 'additional_parent': MAIN,
    'base_tree': cp['tree'], 'tree': tree, 'merge_base': merge_base,
    'scope': 'Required current-main N06 integration, plus four independently reviewed compatibility resolutions. No held source group activated.',
    'paths': paths, 'new_blob_paths': new_blob_paths,
    'raw_added_lean_since_green': raw_added, 'raw_deleted_lean_since_green': raw_deleted,
    'already_upstream_compiled_added_lean': upstream_added,
    'already_upstream_compiled_deleted_lean': upstream_deleted,
    'own_full_new_lean_blob_lines_excluding_generated_root': own_new_lines,
    'budget_note': 'The large bulk change is the existing successful upstream integration, not new uncompiled development. Further source activation remains blocked until this exact merged tree passes complete CI.',
    'upstream_ci': upstream_receipt,
    'independent_review': {'path': str(REVIEW), 'sha256': REVIEW_SHA},
    'inherited_upstream_whitespace': inherited_whitespace,
    'payload': str(payload_path), 'payload_sha256': sha(text.encode()),
    'payload_codepoints': len(text),
    'source_all_total': len(list((REPO / 'src/ContinuousFlexibility').rglob('*.lean'))),
    'all_src_lean_including_library_roots': len(list((REPO / 'src').rglob('*.lean'))),
    'root_imports': (REPO / 'src/ContinuousFlexibility.lean').read_text().count('\nimport ') +
        int((REPO / 'src/ContinuousFlexibility.lean').read_text().startswith('import ')),
    'status': 'Merged and staged; not yet compiled.'}
plan_path.write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
assert cp_path.read_bytes() == cp_bytes
print(json.dumps({k: v for k, v in plan.items() if k not in ('paths', 'upstream_ci')}, ensure_ascii=False))
