import json
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
plan = json.loads((ROOT / 'n04-ci155-plan.json').read_text())
path = ROOT / 'n04-active-checkpoint.json'
cp = json.loads(path.read_text())
assert cp['current_ci']['label'] == 154
old = cp['current_ci']
cp['ci_history'].append(old)
if not any(x.get('label') == 154 for x in cp['failed_ci']):
    cp['failed_ci'].append(old)
cp['head'] = 'bd249b94d15dd2242e189bcd91c7e378ea7875d9'
cp['tree'] = plan['tree']
cp['current_ci'] = {
    'label': 155, 'head': cp['head'], 'tree': cp['tree'],
    'main': plan['main_integrated'], 'main_checked': plan['main_checked'],
    'main_workflow_file_integrated': plan['main_workflow_file_integrated'],
    'pushed': '2026-11-12 15:49:49 UTC',
    'first_check_not_before': '2026-11-12 15:54:49 UTC',
    'status': 'pending', 'plan': 'n04-ci155-plan.json',
    'source_total': plan['source_total'], 'source_all_total': plan['source_all_total'],
    'root_imports': plan['root_imports'],
    'added_lean_since_full_green': plan['added_lean_since_full_green'],
    'repair_files': 3, 'scope': plan['scope']}
cp['pending_main_merge']['sha'] = plan['main_checked']
cp['pending_main_merge']['source_changes_through'] = 'c9cd90e7cbf7f1c8445477ec543c414c3cd06c42'
backup = json.loads((ROOT / 'n04-backup27-pushed.json').read_text())
if not any(x.get('snapshot') == 27 for x in cp['recovery_backups']):
    cp['recovery_backups'].append(backup)
cp['updated_at'] = datetime.now(timezone.utc).isoformat()
path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n')
(ROOT / 'n04-ci155-pushed.json').write_text(json.dumps(cp['current_ci'], ensure_ascii=False, indent=2) + '\n')

prpath = ROOT / 'n04-pr18-current.md'
pr = prpath.read_text()
pr = pr.replace('Current head: **34a496f78ec2c9f35f74d2eb3dfd48a1d4190909**; tree: **6976c913d75d04075537b04c6c31fd52b82742c2**.',
                'Current head: **bd249b94d15dd2242e189bcd91c7e378ea7875d9**; tree: **93221bdfea014a7ed555112fe6f2cf136d94df35**.')
needle = 'Current main **c9cd90e7cbf7f1c8445477ec543c414c3cd06c42** was fetched and its rules reread before this push.'
assert needle in pr
pr = pr.replace(needle,
    '**CI155 is pending**, pushed at **2026-11-12 15:49:49 UTC**. This independently reviewed repair adds the 40-line complete-function interior-division equality provider, uses it in the unchanged actual finite factory contract, and splits the positive source estimate into a private per-source root-family lemma. Independent review SHA-256 values are **1239ee94e1673a1c12c84038289f5dd20e9376d857b7b9bba45c610182de8b3d** and **8e6f56484f231f6b221394c1067ad0855573067a745e00b8d638a7db6361101a**. The successful endpoint and height sources, all actual functions and numerical choices, and default resource limits are retained. The head is **3186 added Lean lines** ahead of the last complete green.\n\n'
    'Current main **b629bc27223b74ed17e9fd76fbb8212dcc9163f1** was fetched and its rules reread before this push. Its workflow-only cache retry and successful-main-build cache guard are copied exactly into this head (workflow blob **8acb3130e16927715bbda4ec46856e2e520bc110**). Main source changes remain those at **c9cd90e7cbf7f1c8445477ec543c414c3cd06c42**; this file copy does not claim main ancestry integration.')
pr = pr.replace('**4151 generated root imports / 4210 project source modules** (**4214** Lean files across `src`)',
                '**4152 generated root imports / 4211 project source modules** (**4215** Lean files across `src`)')
start = pr.index('The next **41-module reference-family group**')
end = pr.index('\n\n## Further reviewed work', start)
pr = pr[:start] + ('The next **41-module reference-family group** remains held until the active actual-family tree passes a complete build and current main is integrated. Its immutable proposal records **4902 source lines**, **865 project modules in its closure**, **105 public declarations**, and **34 unique independent reviews**. The last successful exact preflight was against CI153 and its then-current integrated main. The later CI154 preflight correctly stopped at the current-main ancestry gate after the large upstream integration arrived. Reviewed provider transitions have been recorded, but no fresh preflight success or compilation result is claimed for this held group.') + pr[end:]
old_end = 'The selected endpoint dependency graph has 328 modules, including 30 local compatibility sources. Extending the audit to the full 615-module fixed-witness construction found four further genuine old-arity calls; those consumers are being ported before final assembly or compilation claims. No incompatible contracts or open Blueprint statements are silently composed.'
new_end = 'The selected N02/N03 and corrected-flow dependency graph now has 616 modules, including 46 local compatibility sources. All further endpoint/correction consumers have candidate ports and independent reviews. Comparing them with the active branch found eight exact old preimages and 38 not-yet-installed modules. Current-main integration therefore uses the minimal active-consumer cohort rather than activating the entire held graph. Two active type-only ports are independently reviewed, and seven active alias/value/Jacobian/inverse ports (577 plus 760 source lines) are frozen for full peer review. Parameter loss is selected before every spatial order; the same actual flow, neighborhood and height gain are retained. No incompatible contracts or open Blueprint statements are silently composed.'
assert old_end in pr
pr = pr.replace(old_end, new_end)
start = pr.index('The latest backup is [snapshot 26,')
end = pr.index('\n\nSource preservation is not', start)
pr = pr[:start] + ('The latest backup is [snapshot 27, dd75d89d](https://github.com/Rogerhu12/continuous-flexibility/commit/dd75d89da8aa123761259df71b8271d11cfacc87), on `backup/N04Coordinates-recovery-20261112-0755`, pushed at **2026-11-12 15:44:05 UTC**. Its index records **1837 exact files** and preserves **26 new Lean source versions / 5309 lines** outside `src` over the full-green146 recovery baseline. It includes the then-frozen main compatibility work, actual fixed-reference profile and inverse estimates, corrected-flow and first-integral constructions, and cached CI154 evidence. Earlier exact source versions remain immutable and reachable through the backup history and the commit/path index. Later review receipts and work remain uncompiled until a matching CI result is available.') + pr[end:]
prpath.write_text(pr)
print(json.dumps({'head': cp['head'], 'tree': cp['tree'], 'ci': 155, 'pr_characters': len(pr),
                  'first_check_not_before': cp['current_ci']['first_check_not_before']}))
