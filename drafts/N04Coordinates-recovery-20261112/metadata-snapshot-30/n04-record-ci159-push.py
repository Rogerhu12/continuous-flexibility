import json
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
plan = json.loads((root / 'n04-ci159-plan.json').read_text())
path = root / 'n04-active-checkpoint.json'
cp = json.loads(path.read_text())
assert cp['current_ci']['label'] == 158 and cp['current_ci']['status'] == 'failure'
old = cp['current_ci']
cp['ci_history'].append(old)
if not any(x.get('label') == 158 for x in cp['failed_ci']):
    cp['failed_ci'].append(old)
cp['head'] = '23d28b145e1361fd8c683ba77415226b82be7bb3'
cp['tree'] = plan['tree']
cp['current_ci'] = {
    'label': 159, 'head': cp['head'], 'tree': cp['tree'],
    'main': plan['main_integrated'], 'main_checked': plan['main_checked'],
    'main_workflow_file_integrated': plan['main_workflow_file_integrated'],
    'pushed': '2026-11-12 16:43:09 UTC', 'first_check_not_before': '2026-11-12 16:48:09 UTC',
    'status': 'pending', 'plan': 'n04-ci159-plan.json',
    'source_total': plan['source_total'], 'source_all_total': plan['source_all_total'],
    'root_imports': plan['root_imports'],
    'added_lean_since_full_green': plan['added_lean_since_full_green'],
    'repair_files': 1, 'scope': plan['scope']}
cp['updated_at'] = datetime.now(timezone.utc).isoformat()
path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n')
(root / 'n04-ci159-pushed.json').write_text(json.dumps(cp['current_ci'], ensure_ascii=False, indent=2) + '\n')
path = root / 'n04-pr18-current.md'
pr = path.read_text()
pr = pr.replace('Current head: **11d389a72308c6664091ed3e0bdc3cb5fa9b57bf**; tree: **4e374af7313e759e434f04a940682f6ceea85511**.',
    'Current head: **23d28b145e1361fd8c683ba77415226b82be7bb3**; tree: **6b784f09efb45c796f4e03648dedaed5e163ae86**.')
needle = 'Current main **2aa3dbb138bedb82e9972e88158b4dd9c1bf8f1d**'
assert pr.count(needle) == 1
pr = pr.replace(needle,
    '**CI159 is pending**, pushed at **2026-11-12 16:43:09 UTC**. The exact 130-line repair abstracts the finite-prefix aggregation over an independent module, grading, neighborhood, sector, center and source functions; the actual wrapper explicitly supplies the same original state, atlas and source-jet theorem. Its delta is **33 additions / 25 deletions**; both public contracts, the compiled numerical finite-sum proof, common witnesses and default resource limits are unchanged. Independent full-source review SHA-256 is **2b0158d70083c4ecc5f935d87443a207f1cd15b4a814b02a6c39eefd713a85ae**, and owner manifest SHA-256 is **b52ee86e22d9f18c56f430711b2f2dfe2b4fd00da75b2be640a9ad72b9b2fb66**. This head is **3318 added Lean lines** ahead of the last complete green.\n\n' + needle)
path.write_text(pr)
print(json.dumps({'head':cp['head'], 'tree':cp['tree'], 'ci':159, 'first_check_not_before':cp['current_ci']['first_check_not_before']}))
