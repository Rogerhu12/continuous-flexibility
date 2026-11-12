import hashlib, json, re, subprocess
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
mfpath = root / 'n04-drafts/audit/reconstructed/ActualNegativeReferenceGeometryFieldsCandidateManifest.json'
def fp(p):
    p = Path(p)
    b = p.read_bytes()
    return {'path':str(p), 'sha256':hashlib.sha256(b).hexdigest(),
        'blob':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(),
        'lines':len(b.splitlines())}
def check(row):
    a = fp(row['path'])
    for k in ('sha256', 'blob', 'lines'):
        assert a[k] == row[k], (row['path'], k)
assert fp(mfpath)['sha256'] == 'd24f82d0e37649a0785d40a1a544152526f6f19c21f13e1b6ccb5169fbc0a082'
mf = json.loads(mfpath.read_text())
for row in [mf['source'], *mf['actual_providers'], *mf['selected_provider_owners'], mf['pinned_api']]:
    check(row)
s = Path(mf['source']['path']).read_text()
assert re.findall(r'^import (.*)$', s, re.M) == mf['source']['imports']
assert re.findall(r'^theorem (\S+)', s, re.M) == mf['source']['public_names']
assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b|set_option\s+(maxHeartbeats|maxRecDepth)', s)
collision = subprocess.run(['rg','-n',r'^(theorem|lemma|def|abbrev) n04Coordinates_actual_reference_negative_geometry_fields\b',str(root/'continuous-flexibility/src')],capture_output=True,text=True)
assert collision.returncode == 1, collision.stdout
receipt = {
    'kind':'actual_negative_reference_geometry_fields_full_independent_review',
    'reviewer':'/root',
    'status':'PASSED_COMPLETE_STATIC_SOURCE_AND_ACTUAL_PROVIDER_REVIEW_UNCOMPILED',
    'source':mf['source'], 'candidate_manifest':fp(mfpath),
    'actual_providers':mf['actual_providers'],
    'selected_provider_owners':mf['selected_provider_owners'],
    'pinned_api':mf['pinned_api'],
    'read_scope':[
        'Complete 124-line candidate and manifest; complete selected public136 scalar-normalization helper and exact Blueprint-qualified152 scalar-inverse provider.',
        'Actual radial-fields156 statement/proof interfaces, radial chart germ143, positive cylinder128 Jacobian proof, actual PartA producer101 and negative-half96 inclusion were checked against their exact recorded source bytes.',
        'The actual canonicalSource, chart-domain and geometry field definitions and pinned fderiv equality API were checked. The selected namespace and visibility owner receipts are bound explicitly; historical receipts remain unchanged.'
    ],
    'checks':[
        'Y, H and chi are literal zero-angle slices of the same original typed atlas K and its stored inverse, for the same enumeration and negative half. The original angle is retained in every planar formula.',
        'The actual PartA referenceDomain and charts MapsTo fields give the true forward range. The actual scalar inverse supplies the true inverse range and full inverse point identity.',
        'The radial open-neighborhood chart germ identifies the real Frechet derivative with that of the cylinder chart, so the actual plane Jacobian equals deriv Y. The real scalar parameter of fderiv_eq is explicit.',
        'The positive unit-density equality H^2*w*abs(deriv Y)=1 is used through the selected public scalar-normalization theorem. It yields the exact absolute Jacobian and reciprocal identities; no numerical lower bound is assumed here.',
        'Expanding the actual canonicalSource at the same stored inverse point and using its height and reciprocal Jacobian gives H^3*w. Total reciprocal and real-negative-integer-power identities give H^(-3)*w^(-1). All tuple projections and rewrite directions were checked.',
        'The new public name has no active declaration collision. The qualified PartA provider and public136 helper supersessions are required; the old private helper cannot serve this consumer.',
        'No replacement field, alternative inverse, material-envelope premise or final primitive certificate is introduced.'
    ],
    'findings':[], 'compiled':False, 'source_modified':False,
    'scope_limits':[
        'This proves exact field identities and ranges only. Numerical jet bounds and the final realization are still separate work.',
        'This is static full-source/API review, not CI or a combined-graph activation. No local elaboration, resource limit change, active source/index/ref operation or CI query was used for this review.'
    ],
    'created_at':datetime.now(timezone.utc).isoformat()
}
out = Path(__file__).with_name('ActualNegativeReferenceGeometryFieldsIndependentReview.json')
assert not out.exists()
out.write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(fp(out)))
