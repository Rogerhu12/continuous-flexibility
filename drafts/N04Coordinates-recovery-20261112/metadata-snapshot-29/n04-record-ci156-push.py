import json
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
plan = json.loads((ROOT / 'n04-ci156-plan.json').read_text())
path = ROOT / 'n04-active-checkpoint.json'
cp = json.loads(path.read_text())
assert cp['current_ci']['label'] == 155
old = cp['current_ci']
cp['ci_history'].append(old)
if not any(x.get('label') == 155 for x in cp['failed_ci']):
    cp['failed_ci'].append(old)
cp['head'] = '4bb40f935b646a0c4bfa264cff6c2dbb1f67e17c'
cp['tree'] = plan['tree']
cp['current_ci'] = {
    'label': 156, 'head': cp['head'], 'tree': cp['tree'],
    'main': plan['main_integrated'], 'main_checked': plan['main_checked'],
    'main_workflow_file_integrated': plan['main_workflow_file_integrated'],
    'pushed': '2026-11-12 16:07:58 UTC',
    'first_check_not_before': '2026-11-12 16:12:58 UTC',
    'status': 'pending', 'plan': 'n04-ci156-plan.json',
    'source_total': plan['source_total'], 'source_all_total': plan['source_all_total'],
    'root_imports': plan['root_imports'],
    'added_lean_since_full_green': plan['added_lean_since_full_green'],
    'repair_files': 1, 'scope': plan['scope']}
cp['pending_main_merge']['sha'] = plan['main_checked']
cp['pending_main_merge']['source_changes_through'] = 'c9cd90e7cbf7f1c8445477ec543c414c3cd06c42'
cp['updated_at'] = datetime.now(timezone.utc).isoformat()
path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n')
(ROOT / 'n04-ci156-pushed.json').write_text(json.dumps(cp['current_ci'], ensure_ascii=False, indent=2) + '\n')

prpath = ROOT / 'n04-pr18-current.md'
pr = prpath.read_text()
pr = pr.replace('Current head: **bd249b94d15dd2242e189bcd91c7e378ea7875d9**; tree: **93221bdfea014a7ed555112fe6f2cf136d94df35**.',
                'Current head: **4bb40f935b646a0c4bfa264cff6c2dbb1f67e17c**; tree: **4367e214f97e07d201860468f21cb0c2c0db23f4**.')
start = pr.index('Current main **b629bc27223b74ed17e9fd76fbb8212dcc9163f1**')
end = pr.index(' Its N01c/N05 integration introduces', start)
pr = pr[:start] + (
    '**CI156 is pending**, pushed at **2026-11-12 16:07:58 UTC**. The independently reviewed 288-line source repair separates numerical envelope transport, fixed-root endpoint family construction, and actual positive-source matching into private proof layers. Its four public declarations, complete actual functions, witnesses, max/min choices and default resource limits are unchanged. Independent review SHA-256 is **84630bed19daf55c1bb38b2c5eda944796e1fbd9396effb1e4c6822f0e356822**, and owner manifest SHA-256 is **e0dd141fff5b9f194a322d6f7e36a1cc1b7bcc52edcad0339425b354d15d0bdf**. This head is **3258 added Lean lines** ahead of the last complete green.\n\n'
    'Current main **2aa3dbb138bedb82e9972e88158b4dd9c1bf8f1d** was fetched and its rules checked before this push. Its exact workflow adds ancestor line-build artifact reuse for a branch without its own packed cache and removes the generic fallback that could overwrite that cache (workflow blob **3152629f2ebb53a7af652218ea5bd2d64d16d493**). Main source changes remain those at **c9cd90e7cbf7f1c8445477ec543c414c3cd06c42**; this workflow file copy does not claim main ancestry integration.'
) + pr[end:]
pr = pr.replace('and seven active alias/value/Jacobian/inverse ports (577 plus 760 source lines) are frozen for full peer review.',
    'and seven active alias/value/Jacobian/inverse ports (577 plus 760 source lines) now have full independent reviews and owner manifests. The two common-provider duplicate removals also have complete independent reviews. A five-batch dependency-complete main migration proposal is frozen; each batch remains gated on exact-base revalidation and complete CI.')
prpath.write_text(pr)
print(json.dumps({'head': cp['head'], 'tree': cp['tree'], 'ci': 156,
                  'pr_characters': len(pr), 'first_check_not_before': cp['current_ci']['first_check_not_before']}))
