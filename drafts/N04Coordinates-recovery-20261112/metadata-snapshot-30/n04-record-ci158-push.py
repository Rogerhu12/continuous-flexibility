import json
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
plan = json.loads((root / 'n04-ci158-plan.json').read_text())
path = root / 'n04-active-checkpoint.json'
cp = json.loads(path.read_text())
assert cp['current_ci']['label'] == 157 and cp['current_ci']['status'] == 'failure'
old = cp['current_ci']
cp['ci_history'].append(old)
if not any(x.get('label') == 157 for x in cp['failed_ci']):
    cp['failed_ci'].append(old)
cp['head'] = '11d389a72308c6664091ed3e0bdc3cb5fa9b57bf'
cp['tree'] = plan['tree']
cp['current_ci'] = {
    'label': 158, 'head': cp['head'], 'tree': cp['tree'],
    'main': plan['main_integrated'], 'main_checked': plan['main_checked'],
    'main_workflow_file_integrated': plan['main_workflow_file_integrated'],
    'pushed': '2026-11-12 16:32:26 UTC', 'first_check_not_before': '2026-11-12 16:37:26 UTC',
    'status': 'pending', 'plan': 'n04-ci158-plan.json',
    'source_total': plan['source_total'], 'source_all_total': plan['source_all_total'],
    'root_imports': plan['root_imports'],
    'added_lean_since_full_green': plan['added_lean_since_full_green'],
    'repair_files': 1, 'scope': plan['scope']}
cp['updated_at'] = datetime.now(timezone.utc).isoformat()
path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n')
(root / 'n04-ci158-pushed.json').write_text(json.dumps(cp['current_ci'], ensure_ascii=False, indent=2) + '\n')
path = root / 'n04-pr18-current.md'
pr = path.read_text()
pr = pr.replace('Current head: **f44526b34baa27e45b8d32fe20d27deb52d24a80**; tree: **83843ffdcc1539971cdedad2ba36e935da0ad729**.',
    'Current head: **11d389a72308c6664091ed3e0bdc3cb5fa9b57bf**; tree: **4e374af7313e759e434f04a940682f6ceea85511**.')
needle = 'Current main **2aa3dbb138bedb82e9972e88158b4dd9c1bf8f1d**'
assert pr.count(needle) == 1
pr = pr.replace(needle,
    '**CI158 is pending**, pushed at **2026-11-12 16:32:26 UTC**. The exact 122-line repair moves the complete finite-prefix aggregation to a private theorem over an independent CanonicalData parameter, and then supplies the same actual atlas and compiled source-jet theorem. Its delta is **44 additions / 13 deletions**; both public contracts, the finite-sum argument, actual fields, common witnesses and default limits are unchanged. Independent full-source review SHA-256 is **6af3bcc7b5136ebcf64478a13c1a116ba20b2e2407b74f20fbc1dfd3e5903867**, and owner manifest SHA-256 is **12984b2f30138083268d6d72b48147e9c1b91a5618a39ef60b94f97d893cd0b5**. This head is **3310 added Lean lines** ahead of the last complete green.\n\n' + needle)
path.write_text(pr)
print(json.dumps({'head':cp['head'], 'tree':cp['tree'], 'ci':158, 'first_check_not_before':cp['current_ci']['first_check_not_before']}))
