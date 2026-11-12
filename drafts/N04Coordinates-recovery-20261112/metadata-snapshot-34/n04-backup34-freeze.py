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
PARENT = '6cf0c8d0517e0d53f368a4eecf0d0c53f69deb3c'
GREEN = '18f7f6330eceeb9280b84ad0ca0b25c9cd7e3e67'
PREFIX = 'drafts/N04Coordinates-recovery-20261112'
SNAP = 34

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
# Only exact copies of modules covered by completed CI163 may be
# replaced by a reference to that compiled commit. Every older archive
# remains reachable at PARENT and through the existing commit history.
compiled = {}
for row in git('ls-tree', '-r', '-z', GREEN, '--', 'src/ContinuousFlexibility/').split(b'\0'):
    if not row:
        continue
    info, path = row.split(b'\t', 1)
    mode, kind, sha = info.decode().split()
    rel = path.decode()
    if kind == 'blob' and rel.endswith('.lean') and not rel.endswith(
        ('/ProjectiveNewtonCommonOrbit.lean', '/ProjectiveNewtonParameterGrowth.lean')):
        compiled[sha] = rel
compiled_dedup = []
for sha, rel in existing_blobs.items():
    if rel.endswith('.lean') and sha in compiled:
        raw = git('cat-file', 'blob', sha)
        assert blobid(raw) == sha
        record = {'archive_path': rel, 'blob': sha, 'lines': len(raw.splitlines()),
                  'compiled_commit': GREEN, 'compiled_path': compiled[sha],
                  'sha256': digest(raw), 'historical_copy_commit': PARENT}
        compiled_dedup.append(record)
        known[digest(raw)] = {'commit': GREEN, 'path': compiled[sha]}
assert len(compiled_dedup) == 23
assert sum(row['lines'] for row in compiled_dedup) == 4481
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

metadata = ['n04-active-checkpoint.json', 'n04-backup33-pushed.json', 'n04-backup34-freeze.py',
    'n04-backup-restore-index.py', 'n04-pr18-current.md', 'n04-stage-main-next-cohort.py',
    'n04-record-main-cohort-push.py', 'n04-record-full-green.py',
    'n04-reviewed-provider-rebindings-current-main.json', 'n04-preflight-reference-family-main.py',
    'n04-prepare-reference-main-rebindings.py', 'n04-ci163-plan.json', 'n04-ci163-pushed.json',
    'n04-ci163-build-source-coverage.json', 'n04-ci-163-green-receipt.json',
    'n04-ci-163.log', 'n04-ci-163-run-complete.json', 'n04-ci-163-jobs-complete.json',
    'n04-ci164-plan.json', 'n04-ci164-pushed.json']
for name in metadata:
    raw = (ROOT / name).read_bytes()
    dest = f'{PREFIX}/metadata-snapshot-{SNAP}/{name}'
    if len(raw) > 300000:
        packed = gzip.compress(raw, mtime=0)
        assert gzip.decompress(packed) == raw
        entry_for(dest + '.storage.gz', packed, binary=True)
        compressed.append({'source': str(ROOT / name), 'path': dest + '.storage.gz',
            'uncompressed_sha256': digest(raw), 'uncompressed_bytes': len(raw),
            'gzip_bytes': len(packed), 'blob': blobid(packed)})
    else:
        entry_for(dest, raw)

# Refresh the compiled repository bytes to the actual complete-green baseline.
# Every previously archived source remains in the same subtree, unchanged.
archive_tree = git('rev-parse', PARENT + ':' + PREFIX).decode().strip()
compiled_tree = git('rev-parse', GREEN + '^{tree}').decode().strip()
refresh_env = dict(os.environ)
refresh_env['GIT_INDEX_FILE'] = str(ROOT / 'n04-backup34-refresh.index')
git('read-tree', compiled_tree, env=refresh_env)
git('read-tree', '--prefix=' + PREFIX + '/', archive_tree, env=refresh_env)
refresh_tree = git('write-tree', env=refresh_env).decode().strip()
assert not git('diff', PARENT + ':' + PREFIX, refresh_tree + ':' + PREFIX)

stamp = datetime.now(timezone.utc).isoformat()
old_added = sum(int(row.split()[0]) for row in git('diff', '--numstat', '--no-renames', GREEN, refresh_tree, '--', '*.lean').decode().splitlines())
assert old_added == 19585
removed_compiled_lines = sum(row['lines'] for row in compiled_dedup)
new_lines = sum(x['lines'] for x in new_sources)
assert old_added - removed_compiled_lines + new_lines <= 20000, (old_added, new_lines)
plan = {'snapshot': SNAP, 'branch': 'backup/N04Coordinates-recovery-20261112-0755',
    'parent': PARENT, 'additional_parents': [GREEN],
    'base_tree': refresh_tree,
    'compiled_tree': compiled_tree, 'preserved_archive_tree': archive_tree,
    'compiled_tree_refresh': 'Use exact complete-green repository bytes while grafting the full previous archive subtree unchanged; source preservation is not compilation.',
    'compiled_baseline': GREEN, 'line_head': active_head, 'line_tree': active_tree,
    'frozen_at': stamp, 'indexed_files': len(index), 'new_sources': new_sources,
    'new_source_lines': new_lines, 'existing_added_lean_from_compiled_baseline163': old_added,
    'removed_redundant_compiled_archives': compiled_dedup,
    'removed_compiled_copy_lines': removed_compiled_lines,
    'compiled_dedup_note': 'Only twenty-three byte-identical copies of already compiled CI163 source are replaced by exact commit/path references. No uncompiled source is removed or renamed; every historical archive path remains reachable at the previous backup commit.',
    'projected_added_lean_from_compiled_baseline163': old_added - removed_compiled_lines + new_lines,
    'line_count_method': 'Conservative git diff --numstat --no-renames over every Lean file. Content similarity or move detection gives no reduction in the hard source budget.',
    'compressed_diagnostics': compressed,
    'compression_note': 'Lossless gzip for large JSON diagnostics; original source SHA256 and restore behavior preserved. Lean sources remain uncompressed. Binary gzip copies are also preserved exactly.',
    'prior_versions': 'All historical source versions remain immutable and reachable through the backup parent and exact SOURCE-INDEX locations.',
    'status': 'Source preservation only; outside src, no CI activation or completion claim.'}
frozen_index = {'kind': 'incremental_source_preservation', 'snapshot': SNAP,
    'prior_commit': PARENT, 'line_head': active_head, 'line_tree': active_tree,
    'frozen_at': stamp, 'files': index,
    'storage_note': 'Decompress only entries with stored_at.compression=gzip before verifying original sha256. Binary original .gz sources have no compression flag. Use metadata-snapshot-34/n04-backup-restore-index.py.'}
entry_for(PREFIX + '/SOURCE-INDEX.json', (json.dumps(frozen_index, ensure_ascii=False, indent=2) + '\n').encode())
for item in compiled_dedup:
    entries.append({'path': item['archive_path'], 'mode': '100644', 'type': 'blob', 'sha': None})
plan['entries'] = len(entries) + 1
entry_for(PREFIX + '/SNAPSHOT-34.json', (json.dumps(plan, ensure_ascii=False, indent=2) + '\n').encode())
assert len({e['path'] for e in entries}) == len(entries)
task_env = dict(os.environ)
task_env['GIT_INDEX_FILE'] = str(ROOT / 'n04-backup34-local.index')
git('read-tree', plan['base_tree'], env=task_env)
rows = []
for entry in entries:
    if 'sha' in entry and entry['sha'] is None:
        rows.append(('0 ' + '0' * 40 + '\t' + entry['path']).encode() + b'\0')
    else:
        sha = entry.get('sha') or git('hash-object', '-w', '--stdin', data=entry['content'].encode()).decode().strip()
        rows.append((entry['mode'] + ' ' + sha + '\t' + entry['path']).encode() + b'\0')
git('update-index', '-z', '--index-info', data=b''.join(rows), env=task_env)
tree = git('write-tree', env=task_env).decode().strip()
added = sum(int(row.split()[0]) for row in git('diff', '--numstat', '--no-renames', GREEN, tree, '--', '*.lean').decode().splitlines())
assert added == old_added - removed_compiled_lines + new_lines
for item in index:
    loc = item['stored_at']
    ref = tree if loc['commit'] == 'THIS_SNAPSHOT' else loc['commit']
    raw = git('show', ref + ':' + loc['path'])
    if loc.get('compression') == 'gzip':
        raw = gzip.decompress(raw)
    assert digest(raw) == item['sha256'], item['source']
for item in compiled_dedup:
    assert digest(git('show', PARENT + ':' + item['archive_path'])) == item['sha256']
assert git('rev-parse', 'HEAD').decode().strip() == active_head and git('write-tree').decode().strip() == active_tree
payload = json.dumps(entries, ensure_ascii=False)
blob_payload = json.dumps(list(blobs.values()), ensure_ascii=False)
(ROOT / 'n04-backup34-plan.json').write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
(ROOT / 'n04-backup34-tree-payload.json').write_text(payload)
(ROOT / 'n04-backup34-blob-payloads.json').write_text(blob_payload)
(ROOT / 'n04-backup34-local-tree.txt').write_text(tree + '\n')
print(json.dumps({'tree': tree, 'base_tree': refresh_tree, 'compiled_tree': compiled_tree, 'archive_tree': archive_tree, 'indexed_files': len(index), 'entries': len(entries),
    'new_sources': len(new_sources), 'new_lean_lines': new_lines, 'removed_compiled_copy_lines': removed_compiled_lines, 'added_lean': added,
    'compressed_files': len(compressed), 'binary_blobs': len(blobs),
    'tree_payload_codepoints': len(payload), 'tree_payload_sha256': digest(payload.encode()),
    'blob_payload_codepoints': len(blob_payload), 'blob_payload_sha256': digest(blob_payload.encode())}))
