import json
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
plan = json.loads((root / 'n04-ci161-plan.json').read_text())
path = root / 'n04-active-checkpoint.json'
cp = json.loads(path.read_text())
old = cp['current_ci']
assert old['label'] == 160 and old['status'] == 'failure'
assert old['head'] == plan['head_before']
cp['ci_history'].append(old)
cp['head'] = '7ac330b2e0c2420e449235a090055a8018ebf17e'
cp['tree'] = plan['tree']
cp['current_ci'] = {
    'label': 161, 'head': cp['head'], 'tree': cp['tree'],
    'main': old['main'], 'main_checked': plan['main_checked'],
    'main_workflow_file_integrated': old['main_workflow_file_integrated'],
    'pushed': '2026-11-12 17:32:46 UTC', 'first_check_not_before': '2026-11-12 17:37:46 UTC',
    'status': 'pending', 'plan': 'n04-ci161-plan.json',
    'source_total': plan['source_total'], 'source_all_total': plan['source_all_total'],
    'root_imports': plan['root_imports'],
    'added_lean_since_full_green': plan['added_lean_since_full_green'],
    'main_source_batch': 1, 'main_source_batch_count': 5,
    'source_files': 2, 'scope': plan['scope']}
cp['updated_at'] = datetime.now(timezone.utc).isoformat()
path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n')
(root / 'n04-ci161-pushed.json').write_text(json.dumps(cp['current_ci'], ensure_ascii=False, indent=2) + '\n')
path = root / 'n04-pr18-current.md'
pr = path.read_text().replace(old['head'], cp['head'], 1).replace(old['tree'], cp['tree'], 1)
needle = '- **CI160 failed** at the exact current head.'
assert pr.count(needle) == 1
pr = pr.replace(needle, '- **CI161 is pending**, pushed at **2026-11-12 17:32:46 UTC**. Only the two failed modules are changed: private proof boundaries and typed choice projections preserve all public contracts, the same flow tower, parameter-loss order and default resource limits. This repair has **126 additions / 96 deletions**; the conservative active distance from complete-green CI159 is **1079 added Lean lines**. Both repairs passed independent full-source reviews. Main source batch remains **1 / 5**.\n- **CI160 failed** at prior head **03ea768c1f2211dff62714b932be808345dcf918**.')
pr = pr.replace('Focused proof repairs are in progress with the same public contracts and default limits.', 'Its two focused repairs are now submitted in CI161 with the same public contracts and default limits.')
pr = pr.replace('A complete-build claim does not yet apply to CI160.', 'A complete-build claim does not yet apply to CI161.')
path.write_text(pr)
print(json.dumps({'head': cp['head'], 'tree': cp['tree'], 'ci': 161, 'first_check_not_before': cp['current_ci']['first_check_not_before']}))
