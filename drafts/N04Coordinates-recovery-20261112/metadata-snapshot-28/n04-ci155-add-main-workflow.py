import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
MAIN = 'b629bc27223b74ed17e9fd76fbb8212dcc9163f1'
OLD_TREE = '759e92e770fca22e6436147451a4d31c6b0686ba'
WORKFLOW = '.github/workflows/build.yml'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)

plan = json.loads((ROOT / 'n04-ci155-plan.json').read_text())
assert git('rev-parse', 'HEAD').decode().strip() == plan['head_before']
assert git('write-tree').decode().strip() == OLD_TREE == plan['tree']
assert git('rev-parse', 'origin/main').decode().strip() == MAIN
assert not git('diff')
old = (REPO / WORKFLOW).read_bytes()
assert old == git('show', plan['head_before'] + ':' + WORKFLOW)
new = git('show', MAIN + ':' + WORKFLOW)
assert old != new
assert git('diff', '--name-only', MAIN + '^', MAIN).decode().splitlines() == [WORKFLOW]
(REPO / WORKFLOW).write_bytes(new)
git('add', '--', WORKFLOW)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=REPO, check=True)
paths = git('diff', '--cached', '--name-only').decode().splitlines()
assert len(paths) == 5 and paths[0] == WORKFLOW
tree = git('write-tree').decode().strip()
plan['tree'] = tree
plan['main_checked'] = MAIN
plan['main_workflow_file_integrated'] = {
    'main': MAIN, 'path': WORKFLOW,
    'sha256': hashlib.sha256(new).hexdigest(),
    'blob': git('hash-object', WORKFLOW).decode().strip(),
    'method': 'Exact file copy; main ancestry is still pending source batches.'}
plan['workflow_added_at'] = datetime.now(timezone.utc).isoformat()
plan['scope'] += ' Includes the exact current-main workflow cache retry and successful-main-build cache guard; no source or rule changes from this workflow-only upstream commit.'
(ROOT / 'n04-ci155-plan.json').write_text(json.dumps(plan, ensure_ascii=False, indent=2) + '\n')
payload = [{'path': p, 'mode': '100644', 'type': 'blob', 'content': (REPO / p).read_text()} for p in paths]
(ROOT / 'n04-ci155-tree-payload.json').write_text(json.dumps(payload, ensure_ascii=False))
(ROOT / 'n04-ci155-workflow-payload.json').write_text(json.dumps([payload[0]], ensure_ascii=False))
print(json.dumps({'tree': tree, 'paths': paths, 'workflow': plan['main_workflow_file_integrated'],
                  'added_lean_since_full_green': plan['added_lean_since_full_green']}))
