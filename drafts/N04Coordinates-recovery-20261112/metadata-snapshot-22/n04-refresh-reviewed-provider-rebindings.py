"""Retain exact reviewed proof/provider transitions without altering proposals."""
import hashlib
import json
from pathlib import Path

ROOT = Path('/workspace/scratch/bbbea77e4163')
DRAFTS = ROOT / 'n04-drafts'

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def verify(record):
    raw = Path(record['path']).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == record['sha256']
    assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == record['blob']

reviews = []
for label in (142, 143):
    plan = json.loads((ROOT / f'n04-ci{label}-plan.json').read_text())
    for name, expected in plan['reviews']:
        directory = DRAFTS / 'positive/reviews' if label == 142 else DRAFTS
        reviews.append((directory / name, expected))
for label in (144, 145):
    plan = json.loads((ROOT / f'n04-ci{label}-plan.json').read_text())
    record = plan['independent_review']
    reviews.append((Path(record['path']), record['sha256']))
reviews.append((DRAFTS / 'quantitative/recovery/reviews/MainN06CompatibilityIndependentReview.json',
    'ca74c6028f4668a8294d5afb35447bd35944ecbbb628a8016789ecbd516b3722'))

transitions = {}
for path, expected in reviews:
    assert sha(path) == expected
    review = json.loads(path.read_text())
    assert review['result'].startswith('passed_')
    if 'candidate_manifest' in review:
        candidate = review['candidate_manifest']
        assert sha(candidate['path']) == candidate['sha256']
    for candidate in review.get('candidate_manifests', []):
        assert sha(candidate['path']) == candidate['sha256']
    records = review.get('files', review.get('sources', [review]))
    for record in records:
        before, after = record['before'], record['after']
        verify(before)
        verify(after)
        target = record.get('target_path', record.get('path'))
        assert target.startswith('src/') and target.endswith('.lean')
        module = target.removeprefix('src/').removesuffix('.lean').replace('/', '.')
        transitions.setdefault(module, []).append({
            'before': before['blob'], 'after': after['blob'],
            'before_source': before, 'after_source': after,
            'review': str(path), 'review_sha256': expected,
            'scope': 'Reviewed upstream arbitrary-radial-set compatibility and exact boundary proof'
                if path.name == 'MainN06CompatibilityIndependentReview.json'
                else 'Reviewed proof-body repair; complete public headers unchanged'})
assert sum(map(len, transitions.values())) == 18
result = {'kind': 'exact_reviewed_provider_transition_graph',
    'immutable_proposal_unchanged': True,
    'reviews': [{'path': str(path), 'sha256': expected} for path, expected in reviews],
    'transitions': transitions}
out = ROOT / 'n04-reviewed-provider-rebindings.json'
out.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'modules': len(transitions), 'transitions': 18, 'sha256': sha(out)}))
