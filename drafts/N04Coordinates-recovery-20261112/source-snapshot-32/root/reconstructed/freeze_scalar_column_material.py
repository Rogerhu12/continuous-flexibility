import hashlib, json, re
from datetime import datetime, timezone
from pathlib import Path

root=Path('/workspace/scratch/bbbea77e4163'); repo=root/'continuous-flexibility'; out=root/'n04-drafts/root/reconstructed'
def fp(path):
    path=Path(path); raw=path.read_bytes()
    return {'path':str(path),'sha256':hashlib.sha256(raw).hexdigest(),
        'blob':hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(),
        'lines':len(raw.splitlines())}
def verify(row):
    actual=fp(row['path'])
    assert all(actual[k]==row[k] for k in ('sha256','blob','lines') if k in row),row['path']
identity_candidate=out/'CanonicalReferenceScalarColumnIdentitiesCandidateManifest.json'
identity_peer=root/'n04-drafts/quantitative/recovery/reviews/CanonicalReferenceScalarColumnIdentitiesIndependentReview.json'
assert fp(identity_candidate)['sha256']=='f338f49986dae578bcca06daf665f77eda05c5602abd38af8b8cefc5b071d77c'
assert fp(identity_peer)['sha256']=='855edb34a399ea50a892f2c3cd29e6c7f86360121475909c648a4abe761150df'
im=json.loads(identity_candidate.read_text()); ip=json.loads(identity_peer.read_text())
assert ip['status']=='PASS_STATIC_FULL_SOURCE_AND_ACTUAL_CALLEE_REVIEW_UNCOMPILED' and not ip['findings']
for row in [im['source'],*im['actual_providers'],im['scalar_material_provider'],im['scalar_material_provider_owner']]:
    verify(row)
assert im['source']['sha256']==ip['source']['sha256']
owner={'kind':'actual_reference_scalar_column_identities_reviewed_owner','owner':'/root',
 'status':'FULL_SOURCE_INDEPENDENTLY_REVIEWED_HELD_UNCOMPILED','source':im['source'],
 'candidate_manifest':fp(identity_candidate),'independent_review':fp(identity_peer),
 'scope':'Actual left/nu source identity and fixed physical profile smoothness/pi-period only; same stored inverse and source factor, with true radial-core range.',
 'compiled':False,'created_at':datetime.now(timezone.utc).isoformat()}
identity_owner=out/'CanonicalReferenceScalarColumnIdentitiesReviewedManifest.json'
assert not identity_owner.exists()
identity_owner.write_text(json.dumps(owner,ensure_ascii=False,indent=2)+'\n')
source=out/'CanonicalReferenceScalarColumnMaterialJets.lean'; text=source.read_text()
assert not re.search(r'\b(sorry|admit|axiom)\b|set_option\s+(maxHeartbeats|maxRecDepth)',text)
manifest={'kind':'same_fixed_inverse_source_family_two_actual_reference_columns_material_jets',
 'owner':'/root','status':'CANDIDATE_HELD_UNCOMPILED_PENDING_FULL_INDEPENDENT_REVIEW',
 'source':fp(source),'public_names':re.findall(r'^theorem (\S+)',text,re.M),
 'imports':re.findall(r'^import (.*)$',text,re.M),
 'actual_providers':[fp(out/'CanonicalReferenceScalarColumnIdentities.lean'),
    fp(out/'FixedReferenceScalarSourceMaterialJets.lean'),
    fp(repo/'src/ContinuousFlexibility/Analysis/PhysicalTransmissionTrace.lean'),
    fp(repo/'src/ContinuousFlexibility/Statements/Nonlinear.lean')],
 'reviewed_provider_owners':[fp(identity_owner),fp(out/'FixedReferenceScalarSourceMaterialJetsReviewedManifest.json')],
 'pinned_api':fp(Path('/workspace/scratch/continuous-flexibility-mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean')),
 'checks':[
   'All source lines read with the exact104 and140 provider signatures. X,F,W are given fixed families; the generic index permits actual positive components or actual negative halves without a new family choice.',
   'Both scalar profile estimates use the same X,F,W. Their constants are added after s and before K, piece enumeration and either actual-field equality proof.',
   'The true open radial-core range supplies the closed annulus only for the fixed physical-profile compact bound. No inverse zero-jet magnitude is inserted.',
   'Each of the two model bounds is enlarged using W>=1; the same functions retain their smoothness and actual pi-period.',
   'Exact EqOn on the open unit strip transports smoothness, the periodic identity at both points, and every mixed derivative. The ContDiffOn.congr direction was checked against the pinned definition.',
   'No final ReferenceJets input, altered atlas/material/correction field, local compiler or resource option.'
 ],
 'scope_limits':['The actual inverse/source-factor scalar jet data and field equalities remain inputs for each side-specific producer; these inputs are not a final canonical-column certificate.',
   'Held static candidate only; no combined-DAG readiness or compilation claim.'],
 'compiled':False,'created_at':datetime.now(timezone.utc).isoformat()}
candidate=out/'CanonicalReferenceScalarColumnMaterialJetsCandidateManifest.json'
assert not candidate.exists()
candidate.write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'identities_owner':fp(identity_owner),'source':fp(source),'candidate':fp(candidate)}))
