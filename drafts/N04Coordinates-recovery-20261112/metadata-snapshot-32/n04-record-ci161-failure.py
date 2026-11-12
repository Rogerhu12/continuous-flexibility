import hashlib, json, re, subprocess
from datetime import datetime, timezone
from pathlib import Path

root=Path('/workspace/scratch/bbbea77e4163'); repo=root/'continuous-flexibility'
cp_path=root/'n04-active-checkpoint.json'; cp=json.loads(cp_path.read_text()); cur=cp['current_ci']
run=json.loads((root/'n04-ci-161-run-complete.json').read_text())
jobs=json.loads((root/'n04-ci-161-jobs-complete.json').read_text())
job=next(j for j in jobs['jobs'] if j['id']==131365697676)
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
assert head==cur['head']==run['head_sha']=='7ac330b2e0c2420e449235a090055a8018ebf17e'
assert cur['label']==161 and cur['status']=='pending'
assert run['head_branch']=='line/N04Coordinates'
assert run['status']==job['status']=='completed' and run['conclusion']==job['conclusion']=='failure'
steps={s['name']:s['conclusion'] for s in job['steps']}
assert steps['Quick check of the changed modules']=='failure' and steps['Build every library']=='skipped'
raw=(root/'n04-ci-161.log').read_bytes(); log=raw.decode()
assert hashlib.sha256(raw).hexdigest()=='3cd24d16885a4ad19fec2df77775f3b5d2af9145610bdf9eb12216f28f11b48d'
errors=sorted(set(re.findall(r'error: src/ContinuousFlexibility/Analysis/([^:]+):([0-9]+):([0-9]+): ([^\n]+)',log)))
assert [(a,b,c) for a,b,c,_ in errors]==[('N01ControlFlowBounds.lean','222','8'),('N01NeighborhoodRestriction.lean','75','2')]
assert 'ContinuousOn abs (Icc ?m.206 (G h))' in log
assert 'modules compiled / total: 4632 / 4214' in log
stamp=datetime.now(timezone.utc).isoformat()
cur.update(status='failure',completed_run_updated_at=run['updated_at'],checked_at=stamp,
 last_checked_at='2026-11-12 17:39:04 UTC',observed_run_status='completed',
 quick_check='failure',full_build='skipped',axiom_audit='skipped',blueprint='skipped',
 cached_module_files_reported=4632,modules_total_reported=4214,
 module_count_note='Raw cache file count exceeds current source count; it includes restored artifacts and is not a validated compiled-current-source count.',
 log='n04-ci-161.log',log_sha256=hashlib.sha256(raw).hexdigest(),failure_log='cached_once',
 failed_modules=['ContinuousFlexibility.Analysis.N01ControlFlowBounds','ContinuousFlexibility.Analysis.N01NeighborhoodRestriction'],
 failure='The neighborhood private flow helper still times out at its existential obtain75; the control module no longer reports the prior choice timeouts but needs explicit f/a/b/K in its pure-real endpoint helper222. All contracts and default limits remain unchanged.')
cur.pop('note',None)
receipt={'kind':'exact_current_head_complete_ci_failure','label':161,'head':head,'tree':cur['tree'],
 'run':run['id'],'job':job['id'],'run_conclusion':run['conclusion'],'job_conclusion':job['conclusion'],
 'completed_run_updated_at':run['updated_at'],'checked_at':stamp,'log':cur['log'],'log_sha256':cur['log_sha256'],
 'errors':errors,'cached_module_files_reported':4632,'modules_total_reported':4214,
 'module_count_note':cur['module_count_note'],
 'steps':[{'name':s['name'],'conclusion':s['conclusion']} for s in job['steps']],
 'latest_complete_green_unchanged':cp['last_full_green']['sha']}
p=root/'n04-ci-161-failure-receipt.json'; assert not p.exists()
p.write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
cur['receipt']=p.name;cur['receipt_sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
assert not any(x['label']==161 for x in cp['failed_ci'])
cp['failed_ci'].append(dict(cur)); cp['updated_at']=stamp
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n')
(root/'n04-ci161-result.json').write_text(json.dumps(cur,ensure_ascii=False,indent=2)+'\n')
p=root/'n04-pr18-current.md'; pr=p.read_text()
needle='**CI161 is pending**, pushed at **2026-11-12 17:32:46 UTC**.'
assert needle in pr
pr=pr.replace(needle,'**CI161 failed** at the current head. [Run 43270571741](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/43270571741), job **131365697676**, completed at **2026-11-12 17:38:01 UTC**. The neighborhood helper still reaches default200000 at its existential extraction (line75); the control module now reports only an endpoint-helper implicit-argument mismatch (line222). Its former timeout diagnostics are absent. Complete-build and axiom gates were skipped. The log is cached once, SHA-256 **3cd24d16885a4ad19fec2df77775f3b5d2af9145610bdf9eb12216f28f11b48d**. Focused follow-up repairs preserve the contracts and default limits. Pushed at **2026-11-12 17:32:46 UTC**.')
pr=pr.replace('it is pending independent review.','it has passed a complete independent source/provider review, with its exact collar, same-field construction and retained numerical witnesses checked.')
p.write_text(pr)
print(json.dumps({'ci':161,'errors':errors,'receipt_sha256':cur['receipt_sha256']}))
