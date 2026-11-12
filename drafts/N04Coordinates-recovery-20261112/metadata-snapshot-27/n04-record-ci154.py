import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
repo = root / 'continuous-flexibility'
head = '34a496f78ec2c9f35f74d2eb3dfd48a1d4190909'
tree = '6976c913d75d04075537b04c6c31fd52b82742c2'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo).decode().strip() == head
assert subprocess.check_output(['git', 'rev-parse', 'HEAD^{tree}'], cwd=repo).decode().strip() == tree
assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=repo)
path = root / 'n04-active-checkpoint.json'
cp = json.loads(path.read_text())
assert cp['current_ci']['label'] == 153 and cp['current_ci']['status'] == 'failure'
cp.setdefault('ci_history', []).append(cp['current_ci'])
plan = json.loads((root / 'n04-ci154-plan.json').read_text())
cp['head'], cp['tree'] = head, tree
cp['current_ci'] = {
    'label': 154, 'head': head, 'tree': tree,
    'main': plan['main_integrated'], 'main_checked': plan['main_checked'],
    'pushed': '2026-11-12 15:32:59 UTC',
    'first_check_not_before': '2026-11-12 15:37:59 UTC',
    'status': 'pending', 'plan': 'n04-ci154-plan.json',
    'source_total': 4210, 'source_all_total': 4214, 'root_imports': 4151,
    'added_lean_since_full_green': 3131, 'repair_files': 1,
    'scope': plan['scope']}
cp['pending_main_merge'] = plan['pending_main']
cp['updated_at'] = datetime.now(timezone.utc).isoformat()
path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n')
pr = root / 'n04-pr18-current.md'
text = pr.read_text()
text = text.replace('Current head: **11eeb8aebced4bef16f743c11484df9b0c0907a1**; tree: **13c563567ec6c0ecdce19ef2f192970d2400b8b2**.',
                    'Current head: **34a496f78ec2c9f35f74d2eb3dfd48a1d4190909**; tree: **6976c913d75d04075537b04c6c31fd52b82742c2**.')
needle = 'The exact parent signature is unchanged:'
addition = ('**CI154 is pending**, pushed at **2026-11-12 15:32:59 UTC**. It changes exactly one scalar inequality application in the 167-line finite endpoint bound, with independent full-source review **0653af8daf3038f61470cd8da4eae38844208c92e7993860f73b4910bcc08f2d** and owner manifest **693f3c813312bd57a6dbe0a42f8164f30c775590f192c1fe941f693e412003e1**. The successful Height268 source is byte-identical.\n\n'
            'Current main **c9cd90e7cbf7f1c8445477ec543c414c3cd06c42** was fetched and its rules reread before this push. Its N01c/N05 integration introduces **67562 added / 640 deleted Lean lines** relative to the already integrated main. To respect the hard 20000-line distance while adopting the new main, the current failed group is being made green first, then upstream dependencies will be integrated in compiling batches before the final main merge. The 1932 upstream modules of the retained N01 construction graph are already byte-identical to this new main; no port of those sources is necessary. The exact new main has not yet been merged or compiled on this line.\n\n')
assert needle in text and '**CI154 is pending**' not in text
text = text.replace(needle, addition + needle, 1)
pr.write_text(text)
print(json.dumps({'head': head, 'tree': tree, 'checkpoint': 'updated', 'pr_body_chars': len(text)}))
