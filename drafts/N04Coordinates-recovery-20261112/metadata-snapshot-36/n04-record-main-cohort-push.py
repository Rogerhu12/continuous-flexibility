import json
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
repo = root / 'continuous-flexibility'
label = int(sys.argv[1])
plan = json.loads((root / f'n04-ci{label}-plan.json').read_text())
identity = json.loads((root / f'n04-ci{label}-push-identity.json').read_text())
cp_path = root / 'n04-active-checkpoint.json'
cp = json.loads(cp_path.read_text())
old = cp['current_ci']

def git(*args):
    return subprocess.check_output(['git', *args], cwd=repo, text=True).strip()

head = git('rev-parse', 'HEAD')
tree = git('rev-parse', 'HEAD^{tree}')
assert not git('status', '--porcelain')
assert label == old['label'] + 1 == plan['label']
assert old['status'] == 'success'
assert old['head'] == plan['head_before'] == cp['last_full_green']['sha']
assert identity['head'] == head and identity['tree'] == tree == plan['tree']
assert git('rev-parse', 'HEAD^') == old['head']
assert git('rev-parse', 'origin/line/N04Coordinates') == head
assert plan['main_source_batch'] == old['main_source_batch'] + 1
assert 2 <= plan['main_source_batch'] <= 5
assert plan['added_lean_since_full_green'] <= 20000
pushed = datetime.strptime(identity['pushed'], '%Y-%m-%d %H:%M:%S UTC').replace(tzinfo=timezone.utc)
cur = {
    'label': label, 'head': head, 'tree': tree, 'main': old['main'],
    'main_checked': plan['main_checked'],
    'main_workflow_file_integrated': plan['main_workflow_file_integrated'],
    'pushed': identity['pushed'],
    'first_check_not_before': (pushed + timedelta(minutes=5)).strftime('%Y-%m-%d %H:%M:%S UTC'),
    'status': 'pending', 'plan': f'n04-ci{label}-plan.json',
    'source_total': plan['source_total'], 'source_all_total': plan['source_all_total'],
    'root_imports': plan['root_imports'],
    'added_lean_since_full_green': plan['added_lean_since_full_green'],
    'main_source_batch': plan['main_source_batch'], 'main_source_batch_count': 5,
    'source_files': len(plan['sources']) + len(plan['other_Lean_files']),
    'scope': plan['scope']
}
cp['ci_history'].append(old)
cp.update(head=head, tree=tree, current_ci=cur, updated_at=datetime.now(timezone.utc).isoformat())
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n')
(root / f'n04-ci{label}-pushed.json').write_text(json.dumps(cur, ensure_ascii=False, indent=2) + '\n')

green = cp['last_full_green']
compiled = green.get('source_all_compiled')
coverage = (f"**{compiled} / {green['source_all_total']} current project modules**"
            if compiled is not None else 'all modules reached by the default library targets')
section = f'''## Current branch and validation

- Current head: **{head}**; tree: **{tree}**.
- **CI{label} is pending**, pushed at **{identity['pushed']}**. It installs current-main source batch **{cur['main_source_batch']} / 5**: **{cur['source_files']} source modules**, **{plan['added_lean_since_full_green']} added / {plan['deleted_lean_since_full_green']} deleted Lean lines**, including the generated root. Every frozen preimage and the complete import graph were checked. The previous batch passed the complete CI before this activation.
- Current source counts: **{cur['source_total']} project modules**, **{cur['source_all_total']} Lean files across `src`**, **{cur['root_imports']} generated root imports**. A complete-build claim does not yet apply to CI{label}.
- The latest complete-green baseline is **CI{old['label']}**, head **{green['sha']}**, tree **{green['tree']}**. [Run {green['run']}](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/{green['run']}), job **{green['job']}**, completed at **{green['completed_run_updated_at']}**. Changed-module checking, all default libraries including AxiomAudit, root generation and Blueprint status passed with default limits.
- That exact successful build covers {coverage}, with **{green['blueprint_proved']} / {green['blueprint_total']} blueprint statements proved**. Open statements: {', '.join(green['open_nodes'])}. Source coverage is distinguished from the raw cached-artifact count. Exact log SHA-256: **{green['log_sha256']}**; green receipt SHA-256: **{green['receipt_sha256']}**.

Earlier failed-run logs and their focused repair reviews are preserved with exact identities in the recovery records. No heartbeat or other resource limit was raised. N04Coordinates and Realization remain open.

'''
pr_path = root / 'n04-pr18-current.md'
pr = pr_path.read_text()
start = pr.index('## Current branch and validation\n')
end = pr.index('## Current-main integration\n', start)
pr = pr[:start] + section + pr[end:]
pr = pr.replace('The three reference divided atoms are proved to be the literal zero functions; a reviewed common scalar-source estimate is being connected to the actual left and nu columns.',
                'The three reference divided atoms are the literal zero functions. The actual positive left and nu columns now share a reviewed common scalar-source estimate on that same family.')
pr = pr.replace('The actual inverse and potential estimates and their complete atom packaging are being connected.',
                'The actual inverse and potential estimates have complete source reviews. The height/profile products and their compositions with the literal inverse now have reviewed finite-prefix bounds; the remaining geometry and scalar-column packaging is being completed.')
pr_path.write_text(pr)
print(json.dumps({'ci': label, 'head': head, 'batch': cur['main_source_batch'],
                  'first_check_not_before': cur['first_check_not_before']}))
