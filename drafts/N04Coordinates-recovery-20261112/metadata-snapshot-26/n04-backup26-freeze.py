import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
PARENT = 'c7d420fa319e4fd7a53a764c041f983938553051'
OLD_INDEX_COMMIT = 'c7d420fa319e4fd7a53a764c041f983938553051'
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
        dest = f'{PREFIX}/source-snapshot-26/{path.relative_to(ROOT / "n04-drafts").as_posix()}'
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

metadata = ['n04-active-checkpoint.json', 'n04-backup25-pushed.json', 'n04-backup26-freeze.py', 'n04-pr18-current.md', 'n04-ci152-plan.json', 'n04-ci152-tree-payload.json', 'n04-ci-152-run.json', 'n04-ci-152-jobs.json', 'n04-ci-152.log', 'n04-stage-ci152-repair.py', 'n04-next-reference-group-held.json', 'n04-reference-next-group-review-inventory.json', 'n04-next-reference-current-preflight.json', 'n04-reviewed-provider-rebindings-ci152.json', 'n04-extend-reviewed-provider-rebindings-ci152.py', 'n04-preflight-reference-family-ci152.py', 'n04-reference-ci152-preflight-output.txt']
for name in metadata:
    path = ROOT / name
    data = path.read_bytes()
    entries.append({'path': f'{PREFIX}/metadata-snapshot-26/{name}', 'mode': '100644',
                    'type': 'blob', 'content': data.decode()})

stamp = datetime.now(timezone.utc).isoformat()
head = git('rev-parse', 'HEAD').decode().strip()
line_tree = git('rev-parse', 'HEAD^{tree}').decode().strip()
frozen_index = {'kind': 'incremental_source_preservation', 'snapshot': 26,
                'prior_commit': PARENT, 'line_head': head, 'line_tree': line_tree,
                'frozen_at': stamp, 'files': index}
entries.append({'path': f'{PREFIX}/SOURCE-INDEX.json', 'mode': '100644', 'type': 'blob',
                'content': json.dumps(frozen_index, ensure_ascii=False, indent=2) + '\n'})
old_added = sum(int(x.split()[0]) for x in git('diff', '--numstat',
    '14d76e94d35b6e0aff823c24e9eb90c290c9f3d6', PARENT, '--', '*.lean').decode().splitlines()
    if x.split()[0].isdigit())
new_lines = sum(x['lines'] for x in new_sources)
assert old_added + new_lines <= 20000, (old_added, new_lines)
plan = {'snapshot': 26, 'branch': 'backup/N04Coordinates-recovery-20261112-0755',
        'parent': PARENT, 'base_tree': git('rev-parse', PARENT+'^{tree}').decode().strip(),
        'line_head': head, 'line_tree': line_tree, 'frozen_at': stamp,
        'indexed_files': len(index), 'new_sources': new_sources,
        'new_source_lines': new_lines, 'existing_added_lean_from_compiled_baseline140': old_added,
        'projected_added_lean_from_compiled_baseline140': old_added + new_lines,
        'status': 'Source preservation only; outside src, no CI activation or completion claim.',
        'entries': len(entries)}
(ROOT/'n04-backup26-plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
entries.append({'path': f'{PREFIX}/SNAPSHOT-26.json', 'mode':'100644', 'type':'blob',
                'content':json.dumps(plan,ensure_ascii=False,indent=2)+'\n'})
payload = json.dumps(entries,ensure_ascii=False)
(ROOT/'n04-backup26-tree-payload.json').write_text(payload)
print(json.dumps({'indexed':len(index),'entries':len(entries),'new_sources':len(new_sources),
                  'new_lean_lines':new_lines,'projected_added_lean':old_added+new_lines,
                  'payload_codepoints':len(payload),'payload_bytes':len(payload.encode()),
                  'payload_sha256':digest(payload.encode())}))
