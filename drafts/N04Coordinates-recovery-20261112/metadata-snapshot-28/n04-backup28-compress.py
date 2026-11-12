import base64
import gzip
import hashlib
import json
import os
import subprocess
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
PREFIX = 'drafts/N04Coordinates-recovery-20261112'
payload_path = ROOT / 'n04-backup28-tree-payload.json'
plan_path = ROOT / 'n04-backup28-plan.json'
entries = json.loads(payload_path.read_text())
plan = json.loads(plan_path.read_text())
assert plan['snapshot'] == 28 and plan['parent'] == 'dd75d89da8aa123761259df71b8271d11cfacc87'
index_entry = next(e for e in entries if e['path'] == PREFIX + '/SOURCE-INDEX.json')
index = json.loads(index_entry['content'])
blobs, compressed = {}, []
for entry in entries:
    text = entry.get('content', '')
    if len(text) <= 300000 or '/source-snapshot-28/' not in entry['path']:
        continue
    old_path = entry['path']
    raw = text.encode()
    data = gzip.compress(raw, mtime=0)
    assert gzip.decompress(data) == raw
    blob = subprocess.check_output(['git', 'hash-object', '-w', '--stdin'], cwd=REPO, input=data).decode().strip()
    raw_sha = hashlib.sha256(raw).hexdigest()
    dest = old_path + '.gz'
    matches = [i for i in index['files'] if i['stored_at']['commit'] == 'THIS_SNAPSHOT' and i['stored_at']['path'] == old_path]
    assert matches and all(i['sha256'] == raw_sha for i in matches)
    for item in matches:
        item['stored_at']['path'] = dest
        item['stored_at']['compression'] = 'gzip'
    entry.clear()
    entry.update({'path': dest, 'mode': '100644', 'type': 'blob', 'sha': blob})
    blobs[blob] = {'expected_sha': blob, 'encoding': 'base64', 'content': base64.b64encode(data).decode()}
    compressed.append({'path': dest, 'uncompressed_sha256': raw_sha, 'uncompressed_bytes': len(raw),
                       'gzip_bytes': len(data), 'blob': blob})
assert len(compressed) == 5 and 1 <= len(blobs) <= 5
index['storage_note'] = 'stored_at.compression=gzip denotes a gzip Git blob; decompress before verifying the original sha256 and restoring its source path. All Lean sources remain uncompressed. Use metadata-snapshot-28/n04-backup-restore-index.py.'
index_entry['content'] = json.dumps(index, ensure_ascii=False, indent=2) + '\n'
plan['compressed_diagnostics'] = compressed
plan['compression_note'] = 'Lossless gzip of five large reproducible JSON analyses; original SHA256 identities and restoration are verified. All source identities/line budgets are unchanged.'
for name in ['n04-backup-restore-index.py', 'n04-backup28-compress.py']:
    entries.append({'path': PREFIX + '/metadata-snapshot-28/' + name, 'mode': '100644',
                    'type': 'blob', 'content': (ROOT / name).read_text()})
plan['entries'] = len(entries)
next(e for e in entries if e['path'] == PREFIX + '/SNAPSHOT-28.json')['content'] = json.dumps(plan, ensure_ascii=False, indent=2) + '\n'
plan_path.write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
payload = json.dumps(entries, ensure_ascii=False)
payload_path.write_text(payload)
blob_payload = json.dumps(list(blobs.values()), ensure_ascii=False)
(ROOT / 'n04-backup28-blob-payloads.json').write_text(blob_payload)
task_env = dict(os.environ)
task_env['GIT_INDEX_FILE'] = str(ROOT / 'n04-backup28-local.index')
subprocess.run(['git', 'read-tree', plan['base_tree']], cwd=REPO, env=task_env, check=True)
rows = []
for e in entries:
    if 'sha' in e:
        blob = e['sha']
    else:
        blob = subprocess.check_output(['git', 'hash-object', '-w', '--stdin'], cwd=REPO, input=e['content'].encode()).decode().strip()
    rows.append((e['mode'] + ' ' + blob + '\t' + e['path']).encode() + b'\0')
subprocess.run(['git', 'update-index', '-z', '--index-info'], cwd=REPO, env=task_env, input=b''.join(rows), check=True)
tree = subprocess.check_output(['git', 'write-tree'], cwd=REPO, env=task_env).decode().strip()
(ROOT / 'n04-backup28-local-tree.txt').write_text(tree + '\n')
actual_added = sum(int(row.split()[0]) for row in subprocess.check_output(
    ['git', 'diff', '--numstat', plan['compiled_baseline'], tree, '--', '*.lean'], cwd=REPO).decode().splitlines())
assert actual_added == plan['projected_added_lean_from_compiled_baseline146'] == 8142
print(json.dumps({'tree': tree, 'entries': len(entries), 'compressed_files': len(compressed),
                  'unique_binary_blobs': len(blobs), 'tree_payload_codepoints': len(payload),
                  'tree_payload_sha256': hashlib.sha256(payload.encode()).hexdigest(),
                  'blob_payload_codepoints': len(blob_payload),
                  'blob_payload_sha256': hashlib.sha256(blob_payload.encode()).hexdigest(),
                  'added_lean': actual_added}))
