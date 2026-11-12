import json
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
plan = json.loads((root / 'n04-ci157-plan.json').read_text())
path = root / 'n04-active-checkpoint.json'
cp = json.loads(path.read_text())
assert cp['current_ci']['label'] == 156 and cp['current_ci']['status'] == 'failure'
old = cp['current_ci']
cp['ci_history'].append(old)
if not any(x.get('label') == 156 for x in cp['failed_ci']):
    cp['failed_ci'].append(old)
cp['head'] = 'f44526b34baa27e45b8d32fe20d27deb52d24a80'
cp['tree'] = plan['tree']
cp['current_ci'] = {
    'label': 157, 'head': cp['head'], 'tree': cp['tree'],
    'main': plan['main_integrated'], 'main_checked': plan['main_checked'],
    'main_workflow_file_integrated': plan['main_workflow_file_integrated'],
    'pushed': '2026-11-12 16:21:25 UTC', 'first_check_not_before': '2026-11-12 16:26:25 UTC',
    'status': 'pending', 'plan': 'n04-ci157-plan.json',
    'source_total': plan['source_total'], 'source_all_total': plan['source_all_total'],
    'root_imports': plan['root_imports'],
    'added_lean_since_full_green': plan['added_lean_since_full_green'],
    'repair_files': 1, 'scope': plan['scope']}
cp['updated_at'] = datetime.now(timezone.utc).isoformat()
path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n')
(root / 'n04-ci157-pushed.json').write_text(json.dumps(cp['current_ci'], ensure_ascii=False, indent=2) + '\n')
path = root / 'n04-pr18-current.md'
pr = path.read_text()
pr = pr.replace('Current head: **4bb40f935b646a0c4bfa264cff6c2dbb1f67e17c**; tree: **4367e214f97e07d201860468f21cb0c2c0db23f4**.',
    'Current head: **f44526b34baa27e45b8d32fe20d27deb52d24a80**; tree: **83843ffdcc1539971cdedad2ba36e935da0ad729**.')
needle = 'Current main **2aa3dbb138bedb82e9972e88158b4dd9c1bf8f1d**'
assert pr.count(needle) == 1
pr = pr.replace(needle,
    '**CI157 is pending**, pushed at **2026-11-12 16:21:25 UTC**. The exact 309-line repair replaces the single failing endpoint rewrite with a pure Bool identity and a generic complete-certificate transport over opaque indexed functions and a radius equality. Its delta is **23 additions / 2 deletions**; the four public contracts, previously passed proof layers, actual fields and default resource limits are unchanged. Independent full-source review SHA-256 is **be8adebde7d9570023ef3ff87e78b6a5921c1fabe0b7c1890cbb9e5e6dc7d05b**, and owner manifest SHA-256 is **8d265fd91f28a61d7a727c09d55c0085329d68f6093c943358d9bdda010840a2**. This head is **3279 added Lean lines** ahead of the last complete green.\n\n' + needle)
path.write_text(pr)
print(json.dumps({'head':cp['head'], 'tree':cp['tree'], 'ci':157, 'first_check_not_before':cp['current_ci']['first_check_not_before']}))
