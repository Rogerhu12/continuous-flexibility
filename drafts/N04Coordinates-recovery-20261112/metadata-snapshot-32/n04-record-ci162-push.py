import json
from datetime import datetime,timezone
from pathlib import Path

root=Path('/workspace/scratch/bbbea77e4163');plan=json.loads((root/'n04-ci162-plan.json').read_text())
p=root/'n04-active-checkpoint.json';cp=json.loads(p.read_text());old=cp['current_ci']
assert old['label']==161 and old['status']=='failure' and old['head']==plan['head_before']
cp['ci_history'].append(old);cp['head']='e6f0123c8cc5958988184914abf8ca6e27a75b12';cp['tree']=plan['tree']
cp['current_ci']={'label':162,'head':cp['head'],'tree':cp['tree'],'main':old['main'],
 'main_checked':plan['main_checked'],'main_workflow_file_integrated':old['main_workflow_file_integrated'],
 'pushed':'2026-11-12 17:48:10 UTC','first_check_not_before':'2026-11-12 17:53:10 UTC',
 'status':'pending','plan':'n04-ci162-plan.json','source_total':plan['source_total'],
 'source_all_total':plan['source_all_total'],'root_imports':plan['root_imports'],
 'added_lean_since_full_green':plan['added_lean_since_full_green'],
 'main_source_batch':1,'main_source_batch_count':5,'source_files':2,'scope':plan['scope']}
cp['updated_at']=datetime.now(timezone.utc).isoformat();p.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n')
(root/'n04-ci162-pushed.json').write_text(json.dumps(cp['current_ci'],ensure_ascii=False,indent=2)+'\n')
p=root/'n04-pr18-current.md';pr=p.read_text().replace(old['head'],cp['head'],1).replace(old['tree'],cp['tree'],1)
needle='- **CI161 failed** at the current head.';assert needle in pr
pr=pr.replace(needle,'- **CI162 is pending**, pushed at **2026-11-12 17:48:10 UTC**. Two minimal reviewed repairs replace the remaining existential pattern extraction with typed choice projections and specify the scalar endpoint function/interval explicitly. The complete diff is **3 added / 2 deleted lines** in the same two modules. Every public contract and every other source byte is unchanged; the default limits remain in force. Main source batch remains **1 / 5**, with **1080 added Lean lines** from the complete-green159 baseline.\n- **CI161 failed** at prior head **7ac330b2e0c2420e449235a090055a8018ebf17e**.')
pr=pr.replace('A complete-build claim does not yet apply to CI161.','A complete-build claim does not yet apply to CI162.')
p.write_text(pr)
print(json.dumps({'ci':162,'head':cp['head'],'first_check_not_before':cp['current_ci']['first_check_not_before']}))
