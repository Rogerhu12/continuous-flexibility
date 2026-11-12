import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
repo = root / 'continuous-flexibility'
cp_path = root / 'n04-active-checkpoint.json'
cp = json.loads(cp_path.read_text())
cur = cp['current_ci']
run = json.loads((root / 'n04-ci-159-run-complete.json').read_text())
jobs = json.loads((root / 'n04-ci-159-jobs-first.json').read_text())
job = next(j for j in jobs['jobs'] if j['id'] == 131334470593)
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
assert head == cur['head'] == run['head_sha'] == '23d28b145e1361fd8c683ba77415226b82be7bb3'
assert cur['label'] == 159 and cur['status'] == 'pending'
assert run['head_branch'] == 'line/N04Coordinates'
assert run['status'] == job['status'] == 'completed'
assert run['conclusion'] == job['conclusion'] == 'success'
steps = {s['name']: s['conclusion'] for s in job['steps']}
for step in ['Generate the root import', 'Quick check of the changed modules',
             'Build every library', 'Count compiled modules', 'Blueprint status and endpoint axioms']:
    assert steps[step] == 'success', step
raw = (root / 'n04-ci-159.log').read_bytes()
log = raw.decode()
assert hashlib.sha256(raw).hexdigest() == 'f2dfc3b72ce15ae288abe3683e8701b698b7c7e54f43e65a5e83bec5c02018cf'
assert 'Build completed successfully (8194 jobs).' in log
assert 'modules compiled / total: 4209 / 4211' in log
assert 'blueprint statements proved / total: 37 / 42' in log
assert 'open: [N01c, N02N03, N04b, N04Coordinates, N05]' in log
stamp = datetime.now(timezone.utc).isoformat()
receipt = {
    'kind': 'new_verified_full_ci_success', 'label': 159, 'head': head,
    'tree': cur['tree'], 'main': cur['main'], 'main_checked': cur['main_checked'],
    'run': run['id'], 'job': job['id'], 'run_conclusion': 'success', 'job_conclusion': 'success',
    'source_all_compiled': 4209, 'source_all_total': 4211, 'root_imports': 4152,
    'build_jobs': 8194, 'blueprint_proved': 37, 'blueprint_total': 42,
    'open': 5, 'open_nodes': ['N01c', 'N02N03', 'N04b', 'N04Coordinates', 'N05'],
    'log': 'n04-ci-159.log', 'log_sha256': hashlib.sha256(raw).hexdigest(),
    'steps': [{'name': s['name'], 'conclusion': s['conclusion']} for s in job['steps']],
    'completed_run_updated_at': run['updated_at'], 'checked_at': stamp,
    'note': 'Exact current head passed changed-module checking, every default library including AxiomAudit, generated root and Blueprint status with default limits. The final positive source-prefix repair compiled in 0.3 minutes. This is a compilation baseline, not completion of the open N04Coordinates parent or Realization. Held reference sources and new main source batches are not in this head.'
}
receipt_path = root / 'n04-ci-159-green-receipt.json'
receipt_path.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
cp['full_green_history'].append(cp['last_full_green'])
cp['last_full_green'] = {k: v for k, v in receipt.items() if k not in ('kind', 'label', 'head', 'steps', 'note', 'run_conclusion', 'job_conclusion')}
cp['last_full_green'].update(sha=head, receipt=receipt_path.name,
    receipt_sha256=hashlib.sha256(receipt_path.read_bytes()).hexdigest())
cur.update(status='success', run=run['id'], job=job['id'],
    first_check_observed_at='2026-11-12 16:49:48 UTC',
    completed_run_updated_at=run['updated_at'], checked_at=stamp,
    quick_check='success', full_build='success', axiom_audit='success', blueprint='success',
    source_all_compiled=4209, build_jobs=8194, blueprint_proved=37, blueprint_total=42,
    log='n04-ci-159.log', log_sha256=receipt['log_sha256'],
    receipt=receipt_path.name, receipt_sha256=cp['last_full_green']['receipt_sha256'])
cp['updated_at'] = stamp
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n')
(root / 'n04-ci159-result.json').write_text(json.dumps(cur, ensure_ascii=False, indent=2) + '\n')
pr_path = root / 'n04-pr18-current.md'
pr = pr_path.read_text()
assert '**CI159 is pending**' in pr
pr = pr.replace('**CI159 is pending**, pushed at **2026-11-12 16:43:09 UTC**.',
    '**CI159 passed completely** at the exact current head: changed modules, all default libraries including AxiomAudit, generated root, and Blueprint status. The log reports **8194 build jobs**, **4209 / 4211 compiled project modules** and **37 / 42 blueprint statements proved**; N04Coordinates and Realization remain open. This is the new complete-green baseline for bounded source integration. Run **43261713672**, job **131334470593**, exact log SHA-256 **f2dfc3b72ce15ae288abe3683e8701b698b7c7e54f43e65a5e83bec5c02018cf**. Pushed at **2026-11-12 16:43:09 UTC**.')
pr_path.write_text(pr)
print(json.dumps({'head': head, 'status': 'full_green', 'receipt_sha256': cp['last_full_green']['receipt_sha256']}))
