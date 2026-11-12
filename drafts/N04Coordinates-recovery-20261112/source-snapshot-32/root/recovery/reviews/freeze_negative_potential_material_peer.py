import hashlib, json, re
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
folder = root/'n04-drafts/audit/reconstructed'
candidate = folder/'ActualNegativeReferencePotentialMaterialJetsCandidateManifest.json'
inverse_owner = folder/'ActualNegativeReferenceInverseMaterialJetsReviewedManifest.json'
def fp(path):
    path=Path(path); raw=path.read_bytes()
    return {'path':str(path),'sha256':hashlib.sha256(raw).hexdigest(),
        'blob':hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(),
        'lines':len(raw.splitlines())}
def verify(row):
    actual=fp(row['path'])
    assert all(actual[k]==row[k] for k in ('sha256','blob','lines') if k in row),row['path']
assert fp(candidate)['sha256']=='9c9dc0f5d204182bf1a9f0afca38188a4d2648c7466817355efad376d003327a'
assert fp(inverse_owner)['sha256']=='8673113760c3d0eeeec6cd2513e2b3863e1e74b80ae2e5c1a9a32eb50e8c7e28'
mf=json.loads(candidate.read_text())
for row in [*mf['sources'],*mf['actual_providers'],*mf['reviewed_provider_manifests'],*mf['pinned_api_sources'],mf['inverse_provider_candidate']]:
    verify(row)
selected=mf['sources'][1]
source=Path(selected['path']).read_text()
assert re.findall(r'^import (.*)$',source,re.M)==selected['imports']
assert re.findall(r'^theorem (\S+)',source,re.M)==selected['public_names']
assert not re.search(r'\b(sorry|admit|axiom)\b|set_option\s+(maxHeartbeats|maxRecDepth)',source)
assert source.count('n04bActualTypedAtlas_reference_half_height_physical_power_material_jets')==1
assert source.count('n04bActualTypedAtlas_reference_half_inverse_material_jets')==1
io=json.loads(inverse_owner.read_text())
verify(io['source']); verify(io['independent_review'])
receipt={
 'kind':'actual_negative_reference_potential_material_jets_full_independent_review',
 'reviewer':'/root','status':'PASSED_COMPLETE_STATIC_SOURCE_AND_ACTUAL_PROVIDER_REVIEW_UNCOMPILED',
 'source':selected,'candidate_manifest':fp(candidate),'actual_germ_source':mf['sources'][0],
 'actual_providers':mf['actual_providers'],'reviewed_provider_manifests':mf['reviewed_provider_manifests'],
 'subsequently_completed_inverse_owner':fp(inverse_owner),
 'read_scope':[
   'All222 selected material-source lines and complete manifest; all85 local numerical potential lemma and all70 actual planar-germ caller.',
   'The complete207 stored inverse material theorem and actual152 geometry were full-reviewed separately. The previously full-reviewed293 physical height provider and exact powers1/3 adapter were rechecked at their call sites.',
   'Actual mixed-germ/radial mixed API and the fixed profile smoothness/range facts; every recorded source, owner and pinned API fingerprint verified.'
 ],
 'checks':[
   'The literal K, physical height H, scalar inverse chi and original K.cell sample are fixed throughout. Independently obtained height and inverse numerical constants CH/Cinv are combined by addition; no equality of independently chosen numerical families is assumed.',
   'C0=CH+Cinv is chosen before N and dominates both positive floors. The profile-only compact bound is valid on the closed annulus; no reciprocal-profile bound is obtained by compactness there.',
   'For each N a single finite prefix through N+2 dominates B1,B3,BI before component, host and point selection. It supplies physical H through N+2, H^3 through N, w through N+1 and only positive inverse orders through N.',
   'The true half inverse map places chi(x) inside the physical half and radial core. The generic85 lemma is instantiated with local smoothness at those actual points, so no outside extension is charged.',
   'The generic cost CN*M^(N+4) is converted explicitly to coefficient times W^exponent and then dominated by B*W^B with W>=1. Every exponent comparison has the required positivity.',
   'The actual planar germ identifies the stored potential with the same w H^3 (w H-prime)-prime expression. b=0 uses the exact radial bound; b!=0 gives a zero mixed derivative and the nonnegative material right side.',
   'The genuine full-component optical host j is retained separately from K.cell; its original K0 hypothesis is never silently replaced by a half-sample or closed-buffer claim.'
 ],
 'findings':[],'compiled':False,'source_modified':False,
 'scope_limits':[
   'This receipt covers222. The separate70 source is an explicitly bound mathematical provider and has its own independent peer assignment.',
   'The actual-host raw optical lower input and uniform K0 still need the same retained-construction producer. Same-V unit rescaling/atom and final ReferenceJets packaging are later consumers.',
   'Full static source/API review only; no compiler/elaborator, resource override, active source/index/ref or CI action.'
 ],
 'created_at':datetime.now(timezone.utc).isoformat()
}
out=Path(__file__).with_name('ActualNegativeReferencePotentialMaterialJetsIndependentReview.json')
assert not out.exists()
out.write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(fp(out)))
