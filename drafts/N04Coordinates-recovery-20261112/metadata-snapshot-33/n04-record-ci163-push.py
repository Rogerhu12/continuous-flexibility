import json
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
plan = json.loads((root/'n04-ci163-plan.json').read_text())
p = root/'n04-active-checkpoint.json'
cp = json.loads(p.read_text())
old = cp['current_ci']
assert old['label'] == 162 and old['status'] == 'failure' and old['head'] == plan['head_before']
cp['ci_history'].append(old)
cp['head'] = '18f7f6330eceeb9280b84ad0ca0b25c9cd7e3e67'
cp['tree'] = plan['tree']
cp['current_ci'] = {
    'label':163, 'head':cp['head'], 'tree':cp['tree'], 'main':old['main'],
    'main_checked':plan['main_checked'],
    'main_workflow_file_integrated':old['main_workflow_file_integrated'],
    'pushed':'2026-11-12 17:58:13 UTC',
    'first_check_not_before':'2026-11-12 18:03:13 UTC',
    'status':'pending', 'plan':'n04-ci163-plan.json',
    'source_total':plan['source_total'], 'source_all_total':plan['source_all_total'],
    'root_imports':plan['root_imports'],
    'added_lean_since_full_green':plan['added_lean_since_full_green'],
    'main_source_batch':1, 'main_source_batch_count':5, 'source_files':1,
    'scope':plan['scope']
}
cp['updated_at'] = datetime.now(timezone.utc).isoformat()
p.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n')
(root/'n04-ci163-pushed.json').write_text(json.dumps(cp['current_ci'],ensure_ascii=False,indent=2)+'\n')
p = root/'n04-pr18-current.md'
pr = p.read_text().replace(old['head'],cp['head'],1).replace(old['tree'],cp['tree'],1)
needle = '- **CI162 failed** in'
assert needle in pr
pr = pr.replace(needle,'- **CI163 is pending**, pushed at **2026-11-12 17:58:13 UTC**. The independently reviewed repair to `ReturnCorrectionReferenceLower` captures the actual natural parameter loss and includes it in the existing existential base threshold. The exact diff is **3 added / 3 deleted lines** in one module; both public contracts, the same cutoff/host and output loss, all other source bytes and default limits are preserved. The active distance from complete-green159 is **1083 added Lean lines**, with main source batch still **1 / 5**.\n- **CI162 failed** in',1)
pr = pr.replace('A complete-build claim does not yet apply to CI162.','A complete-build claim does not yet apply to CI163.')
p.write_text(pr)
print(json.dumps({'ci':163,'head':cp['head'],'first_check_not_before':cp['current_ci']['first_check_not_before']}))
