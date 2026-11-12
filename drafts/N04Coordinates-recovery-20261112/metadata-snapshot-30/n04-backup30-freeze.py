import base64
import gzip
import hashlib
import json
import os
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
PARENT = '34563c9cf53ad95b24e2c22d7f1c1c001559db99'
GREEN = '23d28b145e1361fd8c683ba77415226b82be7bb3'
PREFIX = 'drafts/N04Coordinates-recovery-20261112'
SNAP = 30

def git(*args, data=None, env=None):
    return subprocess.check_output(['git', *args], cwd=REPO, input=data, env=env)

def digest(b):
    return hashlib.sha256(b).hexdigest()

def blobid(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()

assert not git('status', '--porcelain')
active_head = git('rev-parse', 'HEAD').decode().strip()
active_tree = git('write-tree').decode().strip()
old_index = json.loads(git('show', f'{PARENT}:{PREFIX}/SOURCE-INDEX.json'))
known = {}
for item in old_index['files']:
    loc = dict(item['stored_at'])
    if loc['commit'] == 'THIS_SNAPSHOT':
        loc['commit'] = PARENT
    known[item['sha256']] = loc
existing_blobs = {}
for row in git('ls-tree', '-r', '-z', PARENT, '--', PREFIX).split(b'\0'):
    if not row:
        continue
    info, path = row.split(b'\t', 1)
    mode, kind, sha = info.decode().split()
    if kind == 'blob':
        existing_blobs[sha] = path.decode()
entries, index, new_sources, compressed = [], [], [], []
blobs = {}

def entry_for(dest, raw, binary=False):
    sha = blobid(raw)
    e = {'path': dest, 'mode': '100644', 'type': 'blob'}
    if binary or sha in existing_blobs:
        e['sha'] = sha
        if sha not in existing_blobs:
            blobs[sha] = {'expected_sha': sha, 'encoding': 'base64',
                          'content': base64.b64encode(raw).decode()}
            assert git('hash-object', '-w', '--stdin', data=raw).decode().strip() == sha
    else:
        e['content'] = raw.decode()
    entries.append(e)

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
        dest = f'{PREFIX}/source-snapshot-{SNAP}/{path.relative_to(ROOT / "n04-drafts").as_posix()}'
        loc = {'commit': 'THIS_SNAPSHOT', 'path': dest}
        if path.suffix == '.json' and len(data) > 300000:
            packed = gzip.compress(data, mtime=0)
            assert gzip.decompress(packed) == data
            dest += '.storage.gz'
            loc.update(path=dest, compression='gzip')
            entry_for(dest, packed, binary=True)
            compressed.append({'source': str(path), 'path': dest,
                'uncompressed_sha256': sha, 'uncompressed_bytes': len(data),
                'gzip_bytes': len(packed), 'blob': blobid(packed)})
        else:
            try:
                data.decode()
                binary = False
            except UnicodeDecodeError:
                binary = True
            entry_for(dest, data, binary=binary)
        known[sha] = loc
        if path.suffix == '.lean':
            new_sources.append({'source': str(path), 'sha256': sha, 'lines': len(data.splitlines())})
    index.append({'source': str(path), 'sha256': sha, 'lines': len(data.splitlines()), 'stored_at': loc})

metadata = ['n04-active-checkpoint.json', 'n04-backup29-pushed.json', 'n04-backup30-freeze.py', 'n04-backup-restore-index.py', 'n04-pr18-current.md', 'n04-pr18-ci160-history.md', 'n04-ci-146-green-receipt.json', 'n04-ci-159-green-receipt.json', 'n04-next-reference-group-held.json', 'n04-next-reference-current-preflight.json', 'n04-reviewed-provider-rebindings-ci154.json', 'n04-stage-main-cohort1.py', 'n04-ci157-plan.json', 'n04-ci157-pushed.json', 'n04-ci157-result.json', 'n04-ci-157.log', 'n04-ci-157-run-first.json', 'n04-ci-157-jobs-first.json', 'n04-stage-ci157-repair.py', 'n04-record-ci157-push.py', 'n04-ci158-plan.json', 'n04-ci158-pushed.json', 'n04-ci158-result.json', 'n04-ci-158.log', 'n04-ci-158-run-first.json', 'n04-ci-158-jobs-first.json', 'n04-stage-ci158-repair.py', 'n04-record-ci158-push.py', 'n04-ci159-plan.json', 'n04-ci159-pushed.json', 'n04-ci159-result.json', 'n04-ci-159.log', 'n04-ci-159-run-first.json', 'n04-ci-159-jobs-first.json', 'n04-ci-159-run-complete.json', 'n04-stage-ci159-repair.py', 'n04-record-ci159-push.py', 'n04-record-ci159-green.py', 'n04-ci160-plan.json', 'n04-ci160-pushed.json', 'n04-record-ci160-push.py']
for name in metadata:
    entry_for(f'{PREFIX}/metadata-snapshot-{SNAP}/{name}', (ROOT / name).read_bytes())

stamp = datetime.now(timezone.utc).isoformat()
old_added = sum(int(row.split()[0]) for row in git('diff', '--numstat', '--no-renames', GREEN, PARENT, '--', '*.lean').decode().splitlines())
assert old_added == 10151
new_lines = sum(x['lines'] for x in new_sources)
assert old_added + new_lines <= 20000, (old_added, new_lines)
plan = {'snapshot': SNAP, 'branch': 'backup/N04Coordinates-recovery-20261112-0755',
    'parent': PARENT, 'additional_parents': [GREEN],
    'base_tree': git('rev-parse', PARENT + '^{tree}').decode().strip(),
    'compiled_baseline': GREEN, 'line_head': active_head, 'line_tree': active_tree,
    'frozen_at': stamp, 'indexed_files': len(index), 'new_sources': new_sources,
    'new_source_lines': new_lines, 'existing_added_lean_from_compiled_baseline159': old_added,
    'projected_added_lean_from_compiled_baseline159': old_added + new_lines,
    'line_count_method': 'Conservative git diff --numstat --no-renames over every Lean file. Content similarity or move detection gives no reduction in the hard source budget.',
    'compressed_diagnostics': compressed,
    'compression_note': 'Lossless gzip for large JSON diagnostics; original source SHA256 and restore behavior preserved. Lean sources remain uncompressed. Binary gzip copies are also preserved exactly.',
    'prior_versions': 'All historical source versions remain immutable and reachable through the backup parent and exact SOURCE-INDEX locations.',
    'status': 'Source preservation only; outside src, no CI activation or completion claim.'}
frozen_index = {'kind': 'incremental_source_preservation', 'snapshot': SNAP,
    'prior_commit': PARENT, 'line_head': active_head, 'line_tree': active_tree,
    'frozen_at': stamp, 'files': index,
    'storage_note': 'Decompress only entries with stored_at.compression=gzip before verifying original sha256. Binary original .gz sources have no compression flag. Use metadata-snapshot-30/n04-backup-restore-index.py.'}
entry_for(PREFIX + '/SOURCE-INDEX.json', (json.dumps(frozen_index, ensure_ascii=False, indent=2) + '\n').encode())
plan['entries'] = len(entries) + 1
entry_for(PREFIX + '/SNAPSHOT-30.json', (json.dumps(plan, ensure_ascii=False, indent=2) + '\n').encode())
assert len({e['path'] for e in entries}) == len(entries)
task_env = dict(os.environ)
task_env['GIT_INDEX_FILE'] = str(ROOT / 'n04-backup30-local.index')
git('read-tree', plan['base_tree'], env=task_env)
rows = []
for entry in entries:
    sha = entry.get('sha') or git('hash-object', '-w', '--stdin', data=entry['content'].encode()).decode().strip()
    rows.append((entry['mode'] + ' ' + sha + '\t' + entry['path']).encode() + b'\0')
git('update-index', '-z', '--index-info', data=b''.join(rows), env=task_env)
tree = git('write-tree', env=task_env).decode().strip()
added = sum(int(row.split()[0]) for row in git('diff', '--numstat', '--no-renames', GREEN, tree, '--', '*.lean').decode().splitlines())
assert added == old_added + new_lines
assert git('rev-parse', 'HEAD').decode().strip() == active_head and git('write-tree').decode().strip() == active_tree
payload = json.dumps(entries, ensure_ascii=False)
blob_payload = json.dumps(list(blobs.values()), ensure_ascii=False)
(ROOT / 'n04-backup30-plan.json').write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
(ROOT / 'n04-backup30-tree-payload.json').write_text(payload)
(ROOT / 'n04-backup30-blob-payloads.json').write_text(blob_payload)
(ROOT / 'n04-backup30-local-tree.txt').write_text(tree + '\n')
print(json.dumps({'tree': tree, 'indexed_files': len(index), 'entries': len(entries),
    'new_sources': len(new_sources), 'new_lean_lines': new_lines, 'added_lean': added,
    'compressed_files': len(compressed), 'binary_blobs': len(blobs),
    'tree_payload_codepoints': len(payload), 'tree_payload_sha256': digest(payload.encode()),
    'blob_payload_codepoints': len(blob_payload), 'blob_payload_sha256': digest(blob_payload.encode())}))
