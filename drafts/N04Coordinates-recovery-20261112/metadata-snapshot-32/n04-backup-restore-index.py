"""Restore exact source bytes from a recovery snapshot, including gzip diagnostics."""
import argparse
import gzip
import hashlib
import json
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('repository')
parser.add_argument('snapshot')
parser.add_argument('destination')
args = parser.parse_args()
prefix = 'drafts/N04Coordinates-recovery-20261112'

def read(ref, path):
    return subprocess.check_output(['git', 'show', ref + ':' + path], cwd=args.repository)

index = json.loads(read(args.snapshot, prefix + '/SOURCE-INDEX.json'))
destination = Path(args.destination).resolve()
for item in index['files']:
    loc = item['stored_at']
    ref = args.snapshot if loc['commit'] == 'THIS_SNAPSHOT' else loc['commit']
    data = read(ref, loc['path'])
    if loc.get('compression') == 'gzip':
        data = gzip.decompress(data)
    elif loc.get('compression') is not None:
        raise ValueError('Unsupported compression: ' + str(loc['compression']))
    assert hashlib.sha256(data).hexdigest() == item['sha256'], item['source']
    relative = item['source'].split('/n04-drafts/', 1)[1]
    target = (destination / relative).resolve()
    assert target.is_relative_to(destination)
    if target.exists():
        assert target.read_bytes() == data, 'Existing file differs: ' + str(target)
    else:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
print(json.dumps({'restored_files': len(index['files']), 'snapshot': args.snapshot}))
