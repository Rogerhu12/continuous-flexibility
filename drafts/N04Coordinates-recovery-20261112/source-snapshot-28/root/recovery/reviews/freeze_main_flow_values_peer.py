import difflib
import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
BASE = ROOT / 'n04-drafts/positive/compatibility/main-c9-flow-values'
MANIFEST = BASE / 'CanonicalFlowValuesParameterOrderCandidateManifest.json'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)

def identity(path):
    path = Path(path)
    data = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(data).hexdigest(),
            'blob': git('hash-object', str(path)).decode().strip(), 'lines': len(data.splitlines())}

def verify(item):
    actual = identity(item['path'])
    assert all(actual[k] == item[k] for k in ('sha256', 'blob', 'lines')), item['path']
    return Path(item['path']).read_text()

def heads(text):
    rx = r'(?m)^(?:@\[[^\n]+\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev)\s+([^\s]+)'
    return {m.group(1): text[m.start():text.index(':=', m.end())] for m in re.finditer(rx, text)}

mi = identity(MANIFEST)
assert mi['sha256'] == 'd7597ff7a1f5c0e96bb1f1ef6d465a3ff5222a4ecef2f016a9b2bd5f55c238ac'
mf = json.loads(MANIFEST.read_text())
sources = []
for item in mf['sources']:
    new, old, diff = map(verify, (item['source'], item['base'], item['diff']))
    target = item['target_path']
    assert old.encode() == git('show', mf['active_preimage'] + ':' + target)
    assert old.encode() == git('show', 'bd249b94d15dd2242e189bcd91c7e378ea7875d9:' + target)
    assert diff == ''.join(difflib.unified_diff(old.splitlines(True), new.splitlines(True),
                            fromfile=item['base']['path'], tofile=item['source']['path']))
    oh, nh = heads(old), heads(new)
    assert oh.keys() == nh.keys()
    changed = [name for name in oh if oh[name] != nh[name]]
    assert changed == item['public_and_private_headers_changed'], (target, changed)
    same = [name for name in oh if oh[name] == nh[name]]
    expected = item['other_header_count_preserved']
    if item['module'].endswith('.CanonicalVariationBounds'):
        assert expected == 16 and len(same) == 18
        assert all(name in same for name in ['coefficientFamily_reference', 'ordinaryFlowFamily_reference'])
    else:
        assert len(same) == expected
    assert re.findall(r'(?m)^import .+$', old) == re.findall(r'(?m)^import .+$', new)
    assert re.findall(r'(?m)^set_option .+$', old) == re.findall(r'(?m)^set_option .+$', new)
    assert not re.search(r'\b(?:sorry|axiom|unsafe|native_decide|maxHeartbeats|maxRecDepth)\b', new)
    sources.append({**item['source'], 'target': target, 'base': item['base'], 'diff': item['diff'],
                    'preserved_headers': same, 'changed_headers': changed})
assert sum(s['lines'] for s in sources) == 760
contract_path = 'src/ContinuousFlexibility/Statements/Nonlinear.lean'
contract = git('show', mf['selected_contract_ref'] + ':' + contract_path)
assert git('rev-parse', mf['selected_contract_ref'] + ':' + contract_path).decode().strip() == mf['selected_contract_blob']
assert contract == git('show', 'b629bc27223b74ed17e9fd76fbb8212dcc9163f1:' + contract_path)
providers = [identity(ROOT / 'n04-drafts/quantitative/compatibility/main-n01c-parameter-order/N01JetBounds.lean'),
             identity(ROOT / 'n04-drafts/quantitative/compatibility/main-n01c-parameter-order/CanonicalNeighborhoodRestriction.lean')]
for name in ['ScalarInverseMaterialJets', 'N01OrdinaryFlowAngularRegularity', 'CanonicalMaterialAbsorption']:
    providers.append(identity(REPO / 'src/ContinuousFlexibility/Analysis' / (name + '.lean')))
consumer_names = ['ordinaryFlowFamily_le_displacement_of_n01', 'ordinaryFlowFamily_le_linear_high_of_n01',
                  'ordinaryFlowFamily_le_linear_high_on_closed_of_n01']
consumers = {}
allowed = {item['target'] for item in sources}
for name in consumer_names:
    paths = subprocess.check_output(['rg', '-l', r'\b' + name + r'\b', 'src/ContinuousFlexibility'], cwd=REPO).decode().splitlines()
    assert set(paths) <= allowed, (name, paths)
    consumers[name] = paths
receipt = {
    'kind': 'independent_full_source_active_flow_value_parameter_order_review',
    'status': 'PASSED_STATIC_FULL_SOURCE_REVIEW_UNCOMPILED_REQUIRES_NEW_MAIN_AND_QUANT_ALIAS_COHORT',
    'reviewer': '/root', 'candidate_manifest': mi, 'sources': sources,
    'contract': {'ref': mf['selected_contract_ref'], 'path': contract_path,
                 'blob': mf['selected_contract_blob'], 'sha256': hashlib.sha256(contract).hexdigest()},
    'actual_providers': providers, 'changed_public_contract_consumers': consumers,
    'read_scope': [
        'Full332+107+114+207 candidate lines and all four complete diffs, with the truncated combined display recovered explicitly for the closed/Jacobian sources and variation diff.',
        'Exact current-main coefficient and flow tame definitions and N01 conjuncts; full selected N01JetBounds74 alias.',
        'Full actual ScalarInverseMaterialJets and N01OrdinaryFlowAngularRegularity; complete uniform-smallness theorem and actual restriction terminal proofs.'
    ],
    'checks': [
        'The first-variation consumer selects parameterLoss at k=1 before every angular order; the same actual SmoothDirections witness supplies the line derivative and the same sampled H^(3/4) factor is retained.',
        'The radial-order-zero collar weight is exactly one. Nat.add_assoc identifies s+(loss+parameterLoss) with the selected flow alias s+loss+parameterLoss.',
        'Closing the actual angular jets uses genuine closed-strip continuity and the same material constant. Its helper separates the original N01 loss from the larger flow estimate loss without changing the actual neighborhood.',
        'The Jacobian estimate fixes high=max base (1+(loss+parameterLoss)) before one global neighborhood choice; its qualitative public outputs and same-witness restriction are unchanged.',
        'The inverse proof selects parameterLoss before low/outLoss, then obtains majorants by order. Component-dependent majorants are chosen only after the common loss. The true stored inverse, two-sided identities and first differential bound are retained.',
        'All old and current active preimages are exact, imports/options are identical, 34 public/private headers are preserved and exactly three numeric public plus three private headers change as declared.',
        'Every active use of the three changed numeric public contracts is inside this four-file cohort; no E0>=1 premise, hidden state-dependent constant, resource increase or terminal estimate premise is introduced.'
    ],
    'metadata_correction': 'The candidate manifest reports16 unchanged CanonicalVariationBounds heads; attribute-aware scanning counts18, including the two unchanged same-line @[simp] theorems coefficientFamily_reference and ordinaryFlowFamily_reference. Other counts3/4/9 are exact. Frozen source bytes and all changed-head claims are correct.',
    'scope_limits': [
        'Static full-source review only; the new main contract, quant alias/restriction/envelope ports and all other actual consumers must be integrated atomically in a compilable source batch.',
        'No active source/index/ref/compiler/CI changes by this review. Genuine Lean compilation and the complete build remain required.'
    ],
    'compiled': False, 'reviewed_at': datetime.now(timezone.utc).isoformat()
}
out = Path(__file__).parent / 'CanonicalFlowValuesParameterOrderIndependentReview.json'
assert not out.exists()
out.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(identity(out)))
