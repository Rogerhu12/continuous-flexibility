import hashlib, json, re
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
drafts = root / 'n04-drafts'
folder = drafts / 'audit/reconstructed'
candidate = folder / 'ActualNegativeReferenceInverseMaterialJetsCandidateManifest.json'
geometry_owner = folder / 'ActualNegativeReferenceScalarInverseReviewedManifest.json'
def fp(path):
    path = Path(path)
    raw = path.read_bytes()
    return {'path':str(path), 'sha256':hashlib.sha256(raw).hexdigest(),
        'blob':hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(),
        'lines':len(raw.splitlines())}
def verify(row):
    actual = fp(row['path'])
    for key in ('sha256','blob','lines'):
        if key in row:
            assert row[key] == actual[key], (row['path'],key)
assert fp(candidate)['sha256'] == 'b500575094559b25f8ce553de8ca50977f2723a1c569ff964209d07a7f52aece'
assert fp(geometry_owner)['sha256'] == 'e136252bba805148d49e501b11a0de84d50a4b003c6269177ef59e441cce3f38'
mf = json.loads(candidate.read_text())
for row in [mf['source'], *mf['actual_providers'], *mf['reviewed_provider_manifests'], mf['geometry_provider_candidate']]:
    verify(row)
go = json.loads(geometry_owner.read_text())
for row in go['sources']:
    verify(row)
    verify(row['independent_review'])
    assert any(p['sha256'] == row['sha256'] for p in mf['actual_providers'])
source = Path(mf['source']['path']).read_text()
assert re.findall(r'^import (.*)$', source, re.M) == mf['source']['imports']
assert re.findall(r'^theorem (\S+)', source, re.M) == mf['public_names']
assert not re.search(r'\b(sorry|admit|axiom)\b|set_option\s+(maxHeartbeats|maxRecDepth)', source)
assert source.count('n04bActualTypedAtlas_reference_half_height_physical_power_material_jets') == 1
receipt = {
    'kind': 'actual_negative_reference_inverse_material_jets_full_independent_review',
    'reviewer':'/root', 'status':'PASSED_COMPLETE_STATIC_SOURCE_AND_ACTUAL_PROVIDER_REVIEW_UNCOMPILED',
    'source':mf['source'], 'candidate_manifest':fp(candidate),
    'actual_providers':mf['actual_providers'],
    'reviewed_provider_manifests':mf['reviewed_provider_manifests'],
    'subsequently_completed_geometry_owner':fp(geometry_owner),
    'read_scope':[
        'Complete selected207 inverse-material source and manifest; complete actual152 stored scalar inverse and selected compatibility136 unit-density inverse polynomial.',
        'Complete103 reciprocal-profile and131 actual sample providers; previously full-reviewed293 physical-height power provider and its exact public physical adapter. Actual N01ReturnMargins and N04bReferenceHalves interfaces checked.',
        'Every recorded provider and owner identity verified. The new152/136 reviewed owner is bound separately without rewriting the historical candidate pending-status record.'
    ],
    'checks':[
        'One actual physical-height call fixes C0 before every real power and derivative order. H^2 and H^(-2) are two estimates for that same literal stored H, not reselected height families.',
        'The only compact bound used at ambient annulus endpoints concerns the smooth profile value w. Reciprocal profile jets come from real accumulating-profile cell estimates and then transfer to the original K.cell half sample.',
        'The actual host j of the full open component is kept distinct from K.cell. The raw optical hypothesis uses that host and is explicitly passed to the same height bounds.',
        'For each N the finite H^(-2) prefix, reciprocal-profile constant/exponent and forward-profile bound determine one A before all pieces, hosts and canonical points. M=A*(C0*E0sample)^A satisfies each numerical inverse hypothesis.',
        'The scalar inverse is the literal first component of K.inverseChart at angle zero. The actual geometry theorem maps the genuine canonical half into the genuine physical half and supplies inverse/unit-density germs on open neighborhoods.',
        'The unit-density inverse polynomial is evaluated at exactly those germs and that H/w. Its natural polynomial cost is explicitly converted to one real material exponent B(N) at the same original sample.',
        'The conclusion bounds positive inverse orders N+1 only. No zero-coordinate estimate, alternate inverse, changed material data or final ReferenceJets certificate is inserted.'
    ],
    'findings':[], 'compiled':False, 'source_modified':False,
    'scope_limits':[
        'Uniform K0 and the actual-host full-component raw optical lower bound remain explicit construction inputs. Final realization must produce them from the retained data.',
        'This is a full static source/API review, not CI or combined-graph activation. No local compiler, resource limit, active source/index/ref or CI operation was used.'
    ],
    'created_at':datetime.now(timezone.utc).isoformat()
}
out = Path(__file__).with_name('ActualNegativeReferenceInverseMaterialJetsIndependentReview.json')
assert not out.exists()
out.write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(fp(out)))
