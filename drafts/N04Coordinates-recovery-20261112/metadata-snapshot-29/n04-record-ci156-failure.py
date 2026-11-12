import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
path = root / 'n04-active-checkpoint.json'
cp = json.loads(path.read_text())
ci = cp['current_ci']
assert ci['label'] == 156 and ci['status'] == 'pending'
digest = hashlib.sha256((root / 'n04-ci-156.log').read_bytes()).hexdigest()
assert digest == 'f78f91deeb61dc91d5b59f23622cbcf7adf54f3ccd86a223c1bd1608648f7f66'
ci.update(status='failure', run=43255304501, job=131311784279,
    first_check_observed_at='2026-11-12 16:12:59 UTC',
    completed_run_updated_at='2026-11-12T16:12:30Z', log='n04-ci-156.log',
    log_sha256=digest, failure_log='cached_once', quick_check='failure',
    full_build='skipped', axiom_audit='skipped', blueprint='skipped',
    compiled_modules_partial=4207,
    failed_modules=['ContinuousFlexibility.Analysis.CanonicalPositiveSourceJetBounds'],
    failure='The numeric and fixed-root proof layers passed their former error sites. The only reported error is default200000 isDefEq timeout at187:10, rewriting the positive endpoint radius inside the complete tame predicate. Public contracts and default limits remain unchanged.')
cp['updated_at'] = datetime.now(timezone.utc).isoformat()
path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n')
(root / 'n04-ci156-result.json').write_text(json.dumps(ci, ensure_ascii=False, indent=2) + '\n')
path = root / 'n04-pr18-current.md'
pr = path.read_text()
needle = '**CI156 is pending**, pushed at **2026-11-12 16:07:58 UTC**.'
assert needle in pr
pr = pr.replace(needle,
    '**CI156 failed** its quick check ([run43255304501](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43255304501), job **131311784279**). The numeric and fixed-root proof layers passed the previous failure sites; the only reported diagnostic is the default 200000-heartbeat timeout at the positive endpoint radius rewrite, line187. The log reports **4207 / 4211 project modules compiled**; full build, AxiomAudit and Blueprint were skipped. The complete log is cached once (SHA-256 **' + digest + '**). Pushed at **2026-11-12 16:07:58 UTC**.')
path.write_text(pr)
print(json.dumps({'ci':156, 'status':ci['status'], 'head':ci['head'], 'log_sha256':digest}))
