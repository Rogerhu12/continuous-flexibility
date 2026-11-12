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
run = json.loads((root / 'n04-ci-160-run-complete.json').read_text())
jobs = json.loads((root / 'n04-ci-160-jobs-complete.json').read_text())
job = next(j for j in jobs['jobs'] if j['id'] == 131340981489)
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
assert head == cur['head'] == run['head_sha'] == '03ea768c1f2211dff62714b932be808345dcf918'
assert cur['label'] == 160 and cur['status'] == 'pending'
assert run['head_branch'] == 'line/N04Coordinates'
assert run['status'] == job['status'] == 'completed'
assert run['conclusion'] == job['conclusion'] == 'failure'
steps = {s['name']: s['conclusion'] for s in job['steps']}
assert steps['Quick check of the changed modules'] == 'failure'
assert steps['Build every library'] == 'skipped'
raw = (root / 'n04-ci-160.log').read_bytes()
log = raw.decode()
assert hashlib.sha256(raw).hexdigest() == '62386517362d0eeeed8b0663c0d399f4ccfdce08dcbcebe07ef90fd4167ca097'
assert 'modules compiled / total: 4210 / 4214' in log
errors = sorted(set(re.findall(r'error: src/ContinuousFlexibility/Analysis/([^:]+):([0-9]+):([0-9]+): ([^\n]+)', log)))
assert [(a, b, c) for a, b, c, _ in errors] == [
    ('N01ControlFlowBounds.lean', '210', '2'),
    ('N01ControlFlowBounds.lean', '85', '2'),
    ('N01NeighborhoodRestriction.lean', '101', '4')]
assert all('isDefEq' in msg and '(200000)' in msg for _, _, _, msg in errors)
stamp = datetime.now(timezone.utc).isoformat()
cur.update(status='failure', completed_run_updated_at=run['updated_at'], checked_at=stamp,
    last_checked_at='2026-11-12 17:21:47 UTC', observed_run_status='completed',
    quick_check='failure', full_build='skipped', axiom_audit='skipped', blueprint='skipped',
    compiled_modules_partial=4210, modules_total_reported=4214,
    log='n04-ci-160.log', log_sha256=hashlib.sha256(raw).hexdigest(), failure_log='cached_once',
    failed_modules=['ContinuousFlexibility.Analysis.N01ControlFlowBounds',
                    'ContinuousFlexibility.Analysis.N01NeighborhoodRestriction'],
    failure='The bounded current-main contract cohort hit default200000 isDefEq limits at the two ControlFlowBounds theorem extractions (85 and210) and neighborhood transport101. Complete public contracts and resource limits remain unchanged; next source batch remains gated.')
receipt = {'kind': 'exact_current_head_complete_ci_failure', 'label': 160,
    'head': head, 'tree': cur['tree'], 'run': run['id'], 'job': job['id'],
    'run_conclusion': run['conclusion'], 'job_conclusion': job['conclusion'],
    'completed_run_updated_at': run['updated_at'], 'checked_at': stamp,
    'log': cur['log'], 'log_sha256': cur['log_sha256'], 'errors': errors,
    'compiled_modules_partial': 4210, 'modules_total_reported': 4214,
    'steps': [{'name': s['name'], 'conclusion': s['conclusion']} for s in job['steps']],
    'latest_complete_green_unchanged': cp['last_full_green']['sha']}
receipt_path = root / 'n04-ci-160-failure-receipt.json'
assert not receipt_path.exists()
receipt_path.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
cur['receipt'] = receipt_path.name
cur['receipt_sha256'] = hashlib.sha256(receipt_path.read_bytes()).hexdigest()
assert not any(x['label'] == 160 for x in cp['failed_ci'])
cp['failed_ci'].append(dict(cur))
cp['updated_at'] = stamp
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n')
(root / 'n04-ci160-result.json').write_text(json.dumps(cur, ensure_ascii=False, indent=2) + '\n')
pr_path = root / 'n04-pr18-current.md'
pr = pr_path.read_text()
assert '**CI160 is pending**' in pr
pr = pr.replace('**CI160 is pending**, pushed at **2026-11-12 16:53:26 UTC**.',
    '**CI160 failed** at the exact current head. [Run 43263558841](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43263558841), job **131340981489**, completed at **2026-11-12 17:21:09 UTC**. Changed-module checking reported default **200000-heartbeat `isDefEq` timeouts** in `N01NeighborhoodRestriction` at line 101 and `N01ControlFlowBounds` at lines 85 and 210. The full-library and axiom gates were skipped. The complete log is cached once, SHA-256 **62386517362d0eeeed8b0663c0d399f4ccfdce08dcbcebe07ef90fd4167ca097**. Focused proof repairs are in progress with the same public contracts and default limits. Pushed at **2026-11-12 16:53:26 UTC**.')
pr = pr.replace('The fixed-family principal estimates and four actual positive principal atoms use the same material datum and sampling point. A separate fixed-family potential adapter is under review, and a single actual family selection is being connected to all five atoms.',
    'One actual positive reference-family selection now feeds all fifteen geometric, principal and potential atoms. The source proofs and exact function identities have independent full reviews, retaining the same low envelope, inverse, height and sampling point. The three reference divided atoms are proved to be the literal zero functions; a reviewed common scalar-source estimate is being connected to the actual left and nu columns.')
pr = pr.replace('Actual negative optical factorization, host-to-original-sample transfer and Airy chart/height identities retain the original negative atlas. Whole-half height and potential material estimates are being completed from these actual fields.',
    'Actual negative optical factorization, host-to-original-sample transfer and Airy chart/height identities retain the original negative atlas. Every real power of the same stored height now has reviewed whole-half physical-radius material jets. The actual inverse and potential estimates and their complete atom packaging are being connected.')
pr = pr.replace('The fixed N03 correction gateway retains the actual coefficient/flow identities and the discriminant certificate from the same construction and common neighborhood.',
    'The fixed N03 correction gateway retains the actual coefficient/flow identities and the discriminant certificate. A stronger source leaf preserves all the same original collar, true-host, support, coefficient-lower-bound and flow-slope data for the quantitative current-jet consumers; it is pending independent review.')
pr_path.write_text(pr)
print(json.dumps({'head': head, 'status': 'failure', 'errors': len(errors),
                  'log_bytes': len(raw), 'receipt_sha256': cur['receipt_sha256']}))
