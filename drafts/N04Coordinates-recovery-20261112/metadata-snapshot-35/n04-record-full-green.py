import hashlib
import json
import re
import subprocess
import sys
import tomllib
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
repo = root / 'continuous-flexibility'
label = int(sys.argv[1])
cp_path = root / 'n04-active-checkpoint.json'
cp = json.loads(cp_path.read_text())
cur = cp['current_ci']
run_path = root / f'n04-ci-{label}-run-complete.json'
jobs_path = root / f'n04-ci-{label}-jobs-complete.json'
log_path = root / f'n04-ci-{label}.log'
run = json.loads(run_path.read_text())
jobs = json.loads(jobs_path.read_text())
job = next(j for j in jobs['jobs'] if j['id'] == cur['job'])

def git(*args):
    return subprocess.check_output(['git', *args], cwd=repo, text=True).strip()

def ident(path):
    raw = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
            'bytes': len(raw)}

head = git('rev-parse', 'HEAD')
tree = git('rev-parse', 'HEAD^{tree}')
assert cur['label'] == label and cur['status'] == 'pending'
assert head == cur['head'] == run['head_sha']
# The connector's normalized job omits head_sha; its run_id below binds
# it to this exact-head workflow run.
if 'head_sha' in job:
    assert job['head_sha'] == head
assert tree == cur['tree']
assert not git('status', '--porcelain')
assert run['id'] == cur['run'] == job['run_id']
assert run['head_branch'] == 'line/N04Coordinates'
assert run['status'] == job['status'] == 'completed'
assert run['conclusion'] == job['conclusion'] == 'success'
steps = {s['name']: s['conclusion'] for s in job['steps']}
for step in ['Generate the root import', 'Quick check of the changed modules',
             'Build every library', 'Count compiled modules', 'Blueprint status and endpoint axioms']:
    assert steps[step] == 'success', step

log = log_path.read_text()
builds = re.findall(r'Build completed successfully \((\d+) jobs\)\.', log)
assert builds, 'Complete build success must be present in the saved log'
raw_counts = re.findall(r'modules compiled / total:\s*(\d+)\s*/\s*(\d+)', log)
bp_counts = re.findall(r'blueprint statements proved / total:\s*(\d+)\s*/\s*(\d+)', log)
open_matches = re.findall(r'open:\s*\[([^\]]*)\]', log)
assert raw_counts and bp_counts and open_matches
raw_compiled, raw_total = map(int, raw_counts[-1])
bp_proved, bp_total = map(int, bp_counts[-1])
open_nodes = [x.strip() for x in open_matches[-1].split(',') if x.strip()]
assert len(open_nodes) == bp_total - bp_proved

graph = {}
src_files = list((repo / 'src').rglob('*.lean'))
for path in src_files:
    name = str(path.relative_to(repo / 'src')).removesuffix('.lean').replace('/', '.')
    graph[name] = re.findall(r'^import\s+(\S+)', path.read_text(), re.M)
targets = ['ContinuousFlexibility', 'AxiomAudit', 'FlexibleSphereChallenge', 'FlexibleSphereSolution']
lakefile = tomllib.loads((repo / 'lakefile.toml').read_text())
assert lakefile['defaultTargets'] == targets
for library in lakefile['lean_lib']:
    target = library['name']
    if target in targets:
        path = repo / library['srcDir'] / (target + '.lean')
        assert path.exists()
        graph[target] = re.findall(r'^import\s+(\S+)', path.read_text(), re.M)
covered = set()
pending = list(targets)
while pending:
    name = pending.pop()
    if name in covered or name not in graph:
        continue
    covered.add(name)
    pending.extend(graph[name])
project = {name for name in graph if name.startswith('ContinuousFlexibility.')}
project_covered = project & covered
excluded = sorted(project - project_covered)
assert len(project) == cur['source_total']
assert len(src_files) == cur['source_all_total']
assert excluded == ['ContinuousFlexibility.Analysis.ProjectiveNewtonCommonOrbit',
                    'ContinuousFlexibility.Analysis.ProjectiveNewtonParameterGrowth']
root_imports = sum(line.startswith('import ') for line in
                   (repo / 'src/ContinuousFlexibility.lean').read_text().splitlines())
assert root_imports == cur['root_imports']
stamp = datetime.now(timezone.utc).isoformat()
receipt = {
    'kind': 'new_verified_full_ci_success', 'label': label, 'head': head, 'tree': tree,
    'main': cur['main'], 'main_checked': cur['main_checked'],
    'main_source_batch': cur.get('main_source_batch'),
    'run': run['id'], 'job': job['id'], 'run_conclusion': 'success', 'job_conclusion': 'success',
    'job_head_binding': 'Normalized job.run_id equals the ID of the exact-head workflow run',
    'source_all_compiled': len(project_covered), 'source_all_total': len(project),
    'all_src_lean_files': len(src_files), 'root_imports': root_imports,
    'source_coverage_basis': 'Exact current source import graph of all successful default library targets',
    'excluded_project_modules': excluded, 'default_targets': targets,
    'covered_names_sha256': hashlib.sha256(('\n'.join(sorted(project_covered)) + '\n').encode()).hexdigest(),
    'raw_cached_olean_compiled': raw_compiled, 'raw_ci_reported_source_total': raw_total,
    'raw_count_caution': 'Restored caches may retain .olean files for deleted modules; use current source coverage above.',
    'build_jobs': int(builds[-1]), 'blueprint_proved': bp_proved, 'blueprint_total': bp_total,
    'open': len(open_nodes), 'open_nodes': open_nodes,
    'log': log_path.name, 'log_sha256': ident(log_path)['sha256'],
    'saved_run': ident(run_path), 'saved_jobs': ident(jobs_path),
    'steps': [{'name': s['name'], 'conclusion': s['conclusion']} for s in job['steps']],
    'completed_run_updated_at': run['updated_at'], 'checked_at': stamp,
    'note': 'Exact head passed changed modules, all default libraries including AxiomAudit, generated root and Blueprint status at default limits. This compilation baseline does not close the open N04Coordinates parent or Realization. Held leaves outside src were not compiled.'
}
receipt_path = root / f'n04-ci-{label}-green-receipt.json'
assert not receipt_path.exists()
receipt_path.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
old_green = cp['last_full_green']
cp['full_green_history'].append(old_green)
cp['last_full_green'] = {k: v for k, v in receipt.items()
                        if k not in ['kind', 'label', 'head', 'steps', 'note', 'run_conclusion', 'job_conclusion']}
cp['last_full_green'].update(sha=head, receipt=receipt_path.name,
    receipt_sha256=ident(receipt_path)['sha256'])
cur.update(status='success', checked_at=stamp, completed_run_updated_at=run['updated_at'],
    quick_check='success', full_build='success', axiom_audit='success', blueprint='success',
    source_all_compiled=len(project_covered), current_project_source_total=len(project),
    build_jobs=receipt['build_jobs'], blueprint_proved=bp_proved, blueprint_total=bp_total,
    log=log_path.name, log_sha256=receipt['log_sha256'],
    receipt=receipt_path.name, receipt_sha256=cp['last_full_green']['receipt_sha256'])
cp['updated_at'] = stamp
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n')
(root / f'n04-ci{label}-result.json').write_text(json.dumps(cur, ensure_ascii=False, indent=2) + '\n')

section = f'''## Current branch and validation

- Current head: **{head}**; tree: **{tree}**.
- **CI{label} passed completely** at this exact head: changed-module checking, every default library including AxiomAudit, generated root and Blueprint status. [Run {run['id']}](https://github.com/Rogerhu12/continuous-flexibility/actions/runs/{run['id']}), job **{job['id']}**, completed at **{run['updated_at']}**. Default resource limits were retained.
- This successful build covers **{len(project_covered)} / {len(project)} current project modules**, with **{root_imports} generated root imports**, **{receipt['build_jobs']} build jobs** and **{bp_proved} / {bp_total} blueprint statements proved**. Open statements: {', '.join(open_nodes)}. The two excluded modules remain outside the default build. Current source coverage is distinguished from the restored-cache count of {raw_compiled} .olean files.
- This is the new complete-green baseline for bounded integration. Current-main source batch: **{cur.get('main_source_batch')} / 5**; main ancestry is still checked separately. Exact log SHA-256: **{receipt['log_sha256']}**; green receipt SHA-256: **{cp['last_full_green']['receipt_sha256']}**.

Earlier failed-run logs and their focused repair reviews are preserved with exact identities in the recovery records. N04Coordinates and Realization remain open.

'''
pr_path = root / 'n04-pr18-current.md'
pr = pr_path.read_text()
start = pr.index('## Current branch and validation\n')
end = pr.index('## Current-main integration\n', start)
pr_path.write_text(pr[:start] + section + pr[end:])
print(json.dumps({'label': label, 'head': head, 'status': 'full_green',
                  'compiled_current_sources': len(project_covered), 'project_total': len(project),
                  'receipt_sha256': cp['last_full_green']['receipt_sha256']}))
