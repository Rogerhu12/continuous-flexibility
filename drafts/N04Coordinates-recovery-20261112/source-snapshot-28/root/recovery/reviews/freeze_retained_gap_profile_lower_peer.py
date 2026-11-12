import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
MATHLIB = Path('/workspace/scratch/continuous-flexibility-mathlib')
MANIFEST = ROOT / 'n04-drafts/quantitative/primitive-route/reconstructed/RetainedPositiveGapProfileLowerCandidateManifest.json'

def ident(path):
    path = Path(path)
    b = path.read_bytes()
    blob = subprocess.check_output(['git', 'hash-object', str(path)], cwd=REPO).decode().strip()
    return {'path': str(path), 'sha256': hashlib.sha256(b).hexdigest(), 'blob': blob, 'lines': len(b.splitlines())}

def verify(item):
    actual = ident(item['path'])
    assert all(actual[k] == item[k] for k in ('sha256', 'blob', 'lines')), item['path']
    return Path(item['path']).read_text()

mi = ident(MANIFEST)
assert mi['sha256'] == 'b9afc3e7518a32d613fb27f5fbb912b139a7d1964906ae42b9048fd2b8d1ae87'
mf = json.loads(MANIFEST.read_text())
source = verify(mf['source'])
for item in mf['selected_providers'] + mf['selected_provider_reviews']:
    verify(item)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=MATHLIB).decode().strip() == 'c55e6e786f49471c72fbddbec5415808896aec1e'
assert re.findall(r'(?m)^import (.+)$', source) == mf['imports']
assert re.findall(r'(?m)^theorem ([^\s]+)', source) == mf['public_names']
assert not re.search(r'\b(?:sorry|axiom|unsafe|native_decide|maxHeartbeats|maxRecDepth)\b', source)
for name in mf['public_names']:
    result = subprocess.run(['rg', '-l', r'\b' + name + r'\b', 'src/ContinuousFlexibility'], cwd=REPO, capture_output=True)
    assert result.returncode == 1 and not result.stdout
additional = ident(REPO / 'src/ContinuousFlexibility/Analysis/MaterialSampleBounds.lean')
out = Path(__file__).parent / 'RetainedPositiveGapProfileLowerIndependentReview.json'
assert not out.exists()
receipt = {
    'kind': 'independent_full_source_same_retained_positive_gap_profile_lower_review',
    'status': 'PASSED_STATIC_FULL_SOURCE_REVIEW_HELD_UNCOMPILED', 'reviewer': '/root',
    'candidate_manifest': mi, 'source': mf['source'],
    'actual_providers_verified': mf['selected_providers'],
    'provider_reviews_verified': mf['selected_provider_reviews'],
    'additional_actual_providers': [additional],
    'mathlib_pin': 'c55e6e786f49471c72fbddbec5415808896aec1e',
    'read_scope': [
        'Complete184-line candidate, both theorem quantifier orders and every algebraic/inequality step.',
        'Complete retained positive-gap component123, retained material-width62, scaled material-width118, installed N06 positive-component249 and retained Morse slope140 providers read during the same review.',
        'Actual materialSample_mem_interval and positivity providers from MaterialSampleBounds, and pinned ordered min/max product identities; pinned real-power API identities checked against the supplied source.'
    ],
    'checks': [
        'The real N06 two-root product lower is transported through the retained derivative identity with coefficient c*H/R^3. The two positive side constants are combined by an actual finite minimum; no profile or component is reselected.',
        'The physical gap midpoint selects the true material cell; the sample bound never assumes the entire gap lies in that cell. The model weight is evaluated at n+1 and charged by the same sample as the reciprocal physical width.',
        'The lower coefficient kappa=c*radialE(n+1)^(-P0)*gap/2 is strictly positive. Its exact inverse is (2/c)*radialE(n+1)^P0*gapInverse, bounded by B*sampleE0^(Aw+As).',
        'Only positive E0 is used in the real-power multiplication and inverse monotonicity. No E0>=1 assumption is introduced; Aw+As is nonnegative from the two actual material estimates.',
        'Both endpoint distances are nonnegative. Their maximum is at least half the positive gap, and max*min equals their product, giving the claimed linear minimum-distance lower including both endpoints.',
        'All constants precede side, tail index, sample cell and point. Retained P, actual connected reference, coordinate certificate and material datum remain explicit; the statement covers only the declared tail gaps.',
        'The candidate/provider/review hashes are exact, both public names are absent from the active tree, and no resource limits or public frozen contracts are altered.'
    ],
    'provider_note': 'The actual sample-membership lemma is supplied by MaterialSampleBounds; its identity is recorded in addition to the candidate-listed MaterialCellEndpointModels provider.',
    'scope_limits': ['Finite central exceptional components and the final same-family principal assembly are separate obligations.',
                     'No current-state tower, Through04 certificate or final canonical estimate is assumed or concluded. No active source/index/ref/compiler/CI changes.'],
    'compiled': False, 'reviewed_at': datetime.now(timezone.utc).isoformat()
}
out.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(ident(out)))
