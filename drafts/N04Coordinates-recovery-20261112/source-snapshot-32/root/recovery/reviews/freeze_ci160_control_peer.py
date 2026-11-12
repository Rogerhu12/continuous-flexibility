import hashlib, json, re, subprocess
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
repo = root / 'continuous-flexibility'
folder = root / 'n04-drafts/quantitative/repair160'
manifest_path = folder / 'N01ControlFlowBoundsCI160RepairCandidateManifest.json'
manifest = json.loads(manifest_path.read_text())

def fp(path):
    path = Path(path)
    data = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(data).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest(),
            'lines': len(data.splitlines())}

def verify(row):
    got = fp(row['path'])
    for key in ('sha256', 'blob', 'lines'):
        if key in row:
            assert got[key] == row[key], (row['path'], key)
    return got

for key in ('source', 'base', 'diff', 'cached_log', 'selected_import_closure'):
    verify(manifest[key])
for row in manifest['providers']:
    verify(row)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip() == manifest['actual_base']['head']
base = Path(manifest['base']['path']).read_text()
source = Path(manifest['source']['path']).read_text()
assert subprocess.check_output(['git', 'show', 'HEAD:' + manifest['actual_base']['target']], cwd=repo).decode() == base
pattern = r'^theorem\s+(\S+)([\s\S]*?) := by'
before = {name: tail for name, tail in re.findall(pattern, base, re.M)}
after = {name: tail for name, tail in re.findall(pattern, source, re.M)}
assert len(before) == 6 and before == after
changed = {'N01Properties.controlTravelPartial_second_bound', 'N01Properties.controlTravel_second_bound'}
for name in before.keys() - changed:
    p = r'^theorem ' + re.escape(name) + r'\b[\s\S]*?(?=\n\n)'
    assert re.search(p, base, re.M).group() == re.search(p, source, re.M).group(), name
oldpoint = base.split('    intro m r hr\n', 1)[1].split('\n  exact ⟨parameterLoss, B, hB, hpoint⟩', 1)[0]
oldpoint = '    intro m r hr\n' + oldpoint
newpoint = source.split('  intro m r hr\n', 1)[1].split('\n\n/-- No derivative', 1)[0]
newpoint = '  intro m r hr\n' + newpoint
oldpoint = '\n'.join(line[2:] if line.startswith('  ') else line for line in oldpoint.splitlines())
assert oldpoint.replace('hdata.choose_spec.2 m 0 0', 'htowers m 0 0') == newpoint
assert set(re.findall(r'^import (.+)$', source, re.M)) - set(re.findall(r'^import (.+)$', base, re.M)) == {'ContinuousFlexibility.Analysis.N01JetBounds'}
assert not re.search(r'\b(sorry|admit|axiom)\b|set_option\s+(maxHeartbeats|maxRecDepth)', source)
closure = json.loads(Path(manifest['selected_import_closure']['path']).read_text())
modules = {row['module']: row for row in closure['modules']}
assert len(modules) == 89
for row in modules.values():
    verify(row)
    assert re.findall(r'^import (.+)$', Path(row['path']).read_text(), re.M) == row['imports']
    assert all(not name.startswith('ContinuousFlexibility.') or name in modules for name in row['imports'])
visited, visiting = set(), set()
def visit(name):
    if name in visited:
        return
    assert name not in visiting, name
    visiting.add(name)
    for dep in modules[name]['imports']:
        if dep in modules:
            visit(dep)
    visiting.remove(name)
    visited.add(name)
visit(closure['entry'])
assert len(visited) == 89
receipt = {
    'kind': 'CI160_actual_control_flow_choice_and_fixed_point_full_independent_review',
    'reviewer': '/root', 'status': 'PASSED_COMPLETE_STATIC_SOURCE_AND_EXACT_DELTA_REVIEW_UNCOMPILED',
    'source': manifest['source'], 'base': manifest['base'], 'diff': manifest['diff'],
    'candidate_manifest': fp(manifest_path), 'actual_base': manifest['actual_base'],
    'cached_log': manifest['cached_log'], 'actual_providers': manifest['providers'],
    'selected_import_closure': manifest['selected_import_closure'],
    'read_scope': [
        'All 263 selected source lines, all 200 supplied diff lines and the complete candidate manifest; actual previous public contracts and fixed-point body compared mechanically.',
        'Complete actual N01JetBounds74 and SmoothDirectionsScalarLine78 providers; actual singleton-kappa flow germ, joint scalar line, full optical second derivative and ordinary-flow contract statements.',
        'The unique cached CI160 diagnostics at 85:2 and 210:2; all 89 selected closure source identities, imports and topology verified.'
    ],
    'findings': [
        'The original order k=2, then parameterLoss, then spatial order s=0, then B is preserved. Named N01FlowJetBounds and AtOrder aliases expose the same contract without replacing the chosen actual tower.',
        'The private fixed-point proof is exactly the prior proof after indentation and renaming the fixed supplier. It uses the same ordinaryFlowFamily, original reference state, singleton control direction, sample C.cell and H^(3/4) factor.',
        'All six complete public headers are identical; all four other public declarations are byte-identical. The two modified public proofs only type the same choice projections and call the extracted private proofs.',
        'The endpoint lemma transfers the genuine negative curvature integral through absolute values and continuous extension of the open interval. Its specialization uses the actual partial and full second-derivative theorems, with no assumed endpoint jet or new bound.',
        'No proof placeholders, axioms, resource overrides, import cycles or missing project imports are introduced.'
    ],
    'mechanical_checks': {'public_headers': 6, 'unchanged_public_declarations': 4,
        'fixed_point_body_exact_after_indent_and_supplier_rename': True,
        'selected_closure_modules_verified': 89, 'actual_git_preimage_equal': True,
        'source_unchanged': True},
    'compiled': False,
    'scope_limits': ['Static mathematical/API and proof-boundary review only. Default-budget compiler performance remains for the next CI run.',
                     'No local compiler/elaborator, source/index/ref mutation, resource increase or CI query/download was performed for this review.'],
    'created_at': datetime.now(timezone.utc).isoformat()
}
out = Path(__file__).with_name('CI160N01ControlFlowBoundsIndependentReview.json')
assert not out.exists()
out.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(fp(out)))
