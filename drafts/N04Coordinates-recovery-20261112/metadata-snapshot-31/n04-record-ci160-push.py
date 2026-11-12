import json
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
plan = json.loads((root / 'n04-ci160-plan.json').read_text())
path = root / 'n04-active-checkpoint.json'
cp = json.loads(path.read_text())
old = cp['current_ci']
assert old['label'] == 159 and old['status'] == 'success'
assert cp['last_full_green']['sha'] == old['head'] == plan['head_before']
cp['ci_history'].append(old)
cp['head'] = '03ea768c1f2211dff62714b932be808345dcf918'
cp['tree'] = plan['tree']
cp['current_ci'] = {
    'label': 160, 'head': cp['head'], 'tree': cp['tree'],
    'main': plan['main_integrated'], 'main_checked': plan['main_checked'],
    'main_workflow_file_integrated': old['main_workflow_file_integrated'],
    'pushed': '2026-11-12 16:53:26 UTC', 'first_check_not_before': '2026-11-12 16:58:26 UTC',
    'status': 'pending', 'plan': 'n04-ci160-plan.json',
    'source_total': plan['source_total'], 'source_all_total': plan['source_all_total'],
    'root_imports': plan['root_imports'],
    'added_lean_since_full_green': plan['added_lean_since_full_green'],
    'main_source_batch': 1, 'main_source_batch_count': 5,
    'source_files': 32, 'scope': plan['scope']}
cp['updated_at'] = datetime.now(timezone.utc).isoformat()
path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n')
(root / 'n04-ci160-pushed.json').write_text(json.dumps(cp['current_ci'], ensure_ascii=False, indent=2) + '\n')
path = root / 'n04-pr18-current.md'
pr = path.read_text()
pr = pr.replace('Current head: **23d28b145e1361fd8c683ba77415226b82be7bb3**; tree: **6b784f09efb45c796f4e03648dedaed5e163ae86**.',
    'Current head: **03ea768c1f2211dff62714b932be808345dcf918**; tree: **84a1b13b975d16f42aed7de40b8601bd09fda8ae**.')
needle = '**CI159 passed completely**'
assert pr.count(needle) == 1
pr = pr.replace(needle,
    '**CI160 is pending**, pushed at **2026-11-12 16:53:26 UTC**. This is **current-main source batch 1 / 5**: **32 modules**, **966 additions / 306 deletions** in Lean, including the generated root. The new ordinary-flow parameter-order loss contract is installed atomically with all identified active consumers and seven independently reviewed local-port manifests. The exact upstream seminorm/restriction providers are included; the stronger blueprint witness stays paired with its factories for batch 2. The complete preimage and provider identities matched. Main ancestry and subsequent batches remain gated on full CI.\n\n' + needle)
path.write_text(pr)
print(json.dumps({'head':cp['head'], 'tree':cp['tree'], 'ci':160, 'first_check_not_before':cp['current_ci']['first_check_not_before']}))
