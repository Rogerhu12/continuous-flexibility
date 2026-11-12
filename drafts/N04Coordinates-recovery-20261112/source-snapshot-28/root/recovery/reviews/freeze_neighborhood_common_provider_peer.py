import difflib
import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
BASE = ROOT / 'n04-drafts/positive/compatibility/main-c9-neighborhood-provider'
MANIFEST = BASE / 'N01NeighborhoodCommonProviderCandidateManifest.json'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)

def ident(path):
    path = Path(path)
    b = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(b).hexdigest(),
            'blob': git('hash-object', str(path)).decode().strip(), 'lines': len(b.splitlines())}

def verify(item):
    actual = ident(item['path'])
    assert all(actual[k] == item[k] for k in ('sha256', 'blob', 'lines'))
    return Path(item['path']).read_text()

mi = ident(MANIFEST)
assert mi['sha256'] == 'f0dfec0195cbb4486d63ea688125b1d4abdd51b62cae4a232724bafb03b8f4a0'
mf = json.loads(MANIFEST.read_text())
new, old, diff, provider, ownertext = map(verify, [mf[k] for k in
    ['source', 'base', 'diff', 'selected_provider', 'historical_reviewed_manifest']])
owner = json.loads(ownertext)
assert owner['sources'][0]['sha256'] == mf['base']['sha256']
assert Path(owner['sources'][0]['path']).read_text() == old
for review in owner['independent_reviews']:
    verify(review)
actual_provider_path = 'src/ContinuousFlexibility/Analysis/N01cStateSeminorms.lean'
assert provider.encode() == git('show', mf['provider_ref'] + ':' + actual_provider_path)
assert provider.encode() == git('show', 'b629bc27223b74ed17e9fd76fbb8212dcc9163f1:' + actual_provider_path)
assert diff == ''.join(difflib.unified_diff(old.splitlines(True), new.splitlines(True),
                        fromfile=mf['base']['path'], tofile=mf['source']['path']))
begin = old.index('\nsection RestrictDirections\n')
end = old.index('\ntheorem stateNeighborhood_isOpen', begin)
expected = (old[:begin] + old[end:]).replace(
    'import ContinuousFlexibility.Analysis.MaterialSampleCofinite\n',
    'import ContinuousFlexibility.Analysis.MaterialSampleCofinite\nimport ContinuousFlexibility.Analysis.N01cStateSeminorms\n', 1)
assert new == expected
assert new[new.index('theorem stateNeighborhood_isOpen'):] == old[old.index('theorem stateNeighborhood_isOpen'):]
assert re.findall(r'(?m)^theorem ([^\s]+)', new) == [
    'stateNeighborhood_isOpen', 'smoothDirections_restrict_oneHigh_bound',
    'stateNeighborhood_mono', 'N01Properties.restrict_neighborhood']
assert 'def SmoothDirections.restrict' not in new and 'theorem oneHighVariationWeight_mono' not in new
assert not re.search(r'\b(?:sorry|axiom|unsafe|native_decide|maxHeartbeats|maxRecDepth)\b', new)
out = Path(__file__).parent / 'N01NeighborhoodCommonProviderIndependentReview.json'
assert not out.exists()
receipt = {
    'kind': 'independent_full_source_main_common_neighborhood_provider_supersession',
    'status': 'PASSED_STATIC_FULL_SOURCE_REVIEW_HELD_UNCOMPILED', 'reviewer': '/root',
    'candidate_manifest': mi, 'source': mf['source'], 'base': mf['base'], 'diff': mf['diff'],
    'selected_provider': mf['selected_provider'], 'provider_ref': mf['provider_ref'],
    'historical_reviewed_manifest': mf['historical_reviewed_manifest'],
    'historical_independent_reviews': owner['independent_reviews'],
    'read_scope': ['Full126 candidate and complete51-line diff including both removed declarations.',
                   'Full331 exact main N01cStateSeminorms provider and historical595-group reviewed manifest.',
                   'Active source scan of both common declarations and their explicit consumers.'],
    'checks': [
        'The source is byte-exactly the reviewed160 source minus its duplicate provider section plus one direct import; all four retained public declarations and complete proofs are unchanged.',
        'Main SmoothDirections.restrict has the same actual J.D field, same explicit J/hV/hVU arguments and the same restricted zero/continuity/derivative fields. Its implicit domain/function parameters are moved from section scope into the definition without changing their meaning.',
        'Main oneHighVariationWeight_mono is the same monotonicity proposition with the same explicit hp/hb/hh/x/v order; natural-number binders are renamed and implicit k is placed before v. Actual consumers use compatible positional arguments and no old binder-name calls were found.',
        'The retained N01 neighborhood proof fixes each k-dependent parameterLoss before s, restricts the same directional tower, and retains every geometry/flow/material value. No hypothesis, actual derivative or resource limit changes.',
        'The exact main provider bytes are also identical at current b629. The original reviewed160 source and receipts remain immutable; this126 selection applies only to the combined main cohort.'
    ],
    'scope_limits': ['Import/name availability alone is not compilation. The combined graph needs its final collision/dependency audit and a complete CI build.',
                     'No active source/index/ref/compiler/CI changes by this review.'],
    'compiled': False, 'reviewed_at': datetime.now(timezone.utc).isoformat()
}
out.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(ident(out)))
