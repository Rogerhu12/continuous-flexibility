import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
PARENT = '7f083833b93046e013d7980d7713078defb10067'
GREEN = '03e526021c371413f03fc0ce052476b63e105361'
OLD_INDEX_COMMIT = '7f083833b93046e013d7980d7713078defb10067'
PREFIX = 'drafts/N04Coordinates-recovery-20261112'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)

def digest(data):
    return hashlib.sha256(data).hexdigest()

old_index = json.loads(git('show', f'{OLD_INDEX_COMMIT}:{PREFIX}/SOURCE-INDEX.json'))
known = {}
for item in old_index['files']:
    loc = dict(item['stored_at'])
    if loc['commit'] == 'THIS_SNAPSHOT':
        loc['commit'] = OLD_INDEX_COMMIT
    known[item['sha256']] = loc

tree = git('ls-tree', '-r', '-z', PARENT, '--', PREFIX)
existing_blobs = {}
for row in tree.split(b'\0'):
    if not row:
        continue
    info, path = row.split(b'\t', 1)
    mode, kind, blob = info.decode().split()
    if kind != 'blob':
        continue
    path = path.decode()
    existing_blobs[blob] = path
    if '/rescue-after-1058/' in path:
        data = git('cat-file', 'blob', blob)
        known[digest(data)] = {'commit': PARENT, 'path': path}

entries, index, new_sources = [], [], []
for path in sorted((ROOT / 'n04-drafts').rglob('*')):
    if not path.is_file():
        continue
    before = path.stat()
    data = path.read_bytes()
    after = path.stat()
    assert (before.st_mtime_ns, before.st_size) == (after.st_mtime_ns, after.st_size), path
    sha = digest(data)
    if sha in known:
        loc = known[sha]
    else:
        dest = f'{PREFIX}/source-snapshot-27/{path.relative_to(ROOT / "n04-drafts").as_posix()}'
        loc = {'commit': 'THIS_SNAPSHOT', 'path': dest}
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        entry = {'path': dest, 'mode': '100644', 'type': 'blob'}
        if blob in existing_blobs:
            entry['sha'] = blob
        else:
            entry['content'] = data.decode()
        entries.append(entry)
        known[sha] = loc
        if path.suffix == '.lean':
            new_sources.append({'source': str(path), 'sha256': sha, 'lines': len(data.splitlines())})
    index.append({'source': str(path), 'sha256': sha, 'lines': len(data.splitlines()), 'stored_at': loc})

metadata = ['n04-active-checkpoint.json', 'n04-backup26-pushed.json', 'n04-backup27-freeze.py', 'n04-pr18-current.md', 'n04-ci153-plan.json', 'n04-ci-153-run.json', 'n04-ci-153-jobs.json', 'n04-ci-153.log', 'n04-ci154-plan.json', 'n04-ci154-tree-payload.json', 'n04-ci-154-run.json', 'n04-ci-154-jobs.json', 'n04-ci-154.log', 'n04-stage-ci154-repair.py', 'n04-record-ci154.py', 'n04-ci-146-green-receipt.json', 'n04-next-reference-group-held.json', 'n04-reference-next-group-review-inventory.json', 'n04-next-reference-current-preflight.json', 'n04-reviewed-provider-rebindings-ci154.json', 'n04-extend-reviewed-provider-rebindings-ci154.py', 'n04-preflight-reference-family-ci154.py', 'n04-review-buffered294.py']
for name in metadata:
    path = ROOT / name
    data = path.read_bytes()
    entries.append({'path': f'{PREFIX}/metadata-snapshot-27/{name}', 'mode': '100644',
                    'type': 'blob', 'content': data.decode()})

stamp = datetime.now(timezone.utc).isoformat()
head = git('rev-parse', 'HEAD').decode().strip()
line_tree = git('rev-parse', 'HEAD^{tree}').decode().strip()
frozen_index = {'kind': 'incremental_source_preservation', 'snapshot': 27,
                'prior_commit': PARENT, 'line_head': head, 'line_tree': line_tree,
                'frozen_at': stamp, 'files': index}
entries.append({'path': f'{PREFIX}/SOURCE-INDEX.json', 'mode': '100644', 'type': 'blob',
                'content': json.dumps(frozen_index, ensure_ascii=False, indent=2) + '\n'})
# Previous bytes remain reachable through PARENT; the current recovery tree
# advances its source baseline to an independently verified full-green commit.
old_added = 0
new_lines = sum(x['lines'] for x in new_sources)
assert old_added + new_lines <= 20000, (old_added, new_lines)
plan = {'snapshot': 27, 'branch': 'backup/N04Coordinates-recovery-20261112-0755',
        'parent': PARENT, 'additional_parents': [GREEN],
        'base_tree': git('rev-parse', GREEN+'^{tree}').decode().strip(),
        'compiled_baseline': GREEN,
        'prior_versions': 'All historical source locations remain immutable and reachable through the backup parent; SOURCE-INDEX names their exact commit and path.',
        'line_head': head, 'line_tree': line_tree, 'frozen_at': stamp,
        'indexed_files': len(index), 'new_sources': new_sources,
        'new_source_lines': new_lines, 'existing_added_lean_from_compiled_baseline146': old_added,
        'projected_added_lean_from_compiled_baseline146': old_added + new_lines,
        'status': 'Source preservation only; outside src, no CI activation or completion claim.',
        'entries': len(entries)}
(ROOT/'n04-backup27-plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
entries.append({'path': f'{PREFIX}/SNAPSHOT-27.json', 'mode':'100644', 'type':'blob',
                'content':json.dumps(plan,ensure_ascii=False,indent=2)+'\n'})
payload = json.dumps(entries,ensure_ascii=False)
(ROOT/'n04-backup27-tree-payload.json').write_text(payload)
print(json.dumps({'indexed':len(index),'entries':len(entries),'new_sources':len(new_sources),
                  'new_lean_lines':new_lines,'projected_added_lean':old_added+new_lines,
                  'payload_codepoints':len(payload),'payload_bytes':len(payload.encode()),
                  'payload_sha256':digest(payload.encode())}))
