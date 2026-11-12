import hashlib,json,re,subprocess
from datetime import datetime,timezone
from pathlib import Path

root=Path('/workspace/scratch/bbbea77e4163');repo=root/'continuous-flexibility'
folder=root/'n04-drafts/quantitative/repair161'
candidate=folder/'N01ControlFlowBoundsCI161RepairCandidateManifest.json'
def fp(path):
    path=Path(path);raw=path.read_bytes()
    return {'path':str(path),'sha256':hashlib.sha256(raw).hexdigest(),
        'blob':hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(),'lines':len(raw.splitlines())}
def verify(row):
    actual=fp(row['path'])
    assert all(actual[k]==row[k] for k in ('sha256','blob','lines') if k in row),row['path']
assert fp(candidate)['sha256']=='ddb4e6eae9c832d2e47153962eae9d559698797de3ce746da31d1696ef418735'
mf=json.loads(candidate.read_text())
for key in ('source','preimage','diff','cached_log','previous_full_review','previous_owner'):verify(mf[key])
before=Path(mf['preimage']['path']).read_text();after=Path(mf['source']['path']).read_text()
assert before==subprocess.check_output(['git','show','7ac330b2e0c2420e449235a090055a8018ebf17e:'+mf['actual_base']['target_path']],cwd=repo,text=True)
old='    hlh hc.abs hinner)';new='    (f := fun r => |G r|) (a := l) (b := h) (K := K) hlh hc.abs hinner)'
assert before.count(old)==after.count(new)==1 and after==before.replace(old,new)
headers=lambda text:re.findall(r'^theorem\s+(\S+)([\s\S]*?) := by',text,re.M)
assert len(headers(before))==6 and headers(before)==headers(after)
assert not re.search(r'\b(sorry|admit|axiom)\b|set_option\s+(maxHeartbeats|maxRecDepth)',after)
receipt={
 'kind':'CI161_control_scalar_endpoint_explicit_arguments_full_source_delta_review',
 'reviewer':'/root','status':'PASSED_COMPLETE_KNOWN_SOURCE_AND_EXACT_SINGLE_DELTA_REVIEW_UNCOMPILED',
 'source':mf['source'],'preimage':mf['preimage'],'candidate_manifest':fp(candidate),
 'diff':mf['diff'],'cached_log':mf['cached_log'],'actual_base':mf['actual_base'],
 'previous_full_review':mf['previous_full_review'],
 'checks':[
   'The entire prior263 source and mathematical/callee context were full-reviewed; all candidate bytes are mechanically identical except the one explicitly inspected endpoint invocation.',
   'The exact CI161 cached type mismatch inferred f=abs and b=G(h). The explicit f=(fun r=>abs(G r)), a=l, b=h, K=K selects the already intended same-file endpoint theorem.',
   'The supplied hlh, hc.abs and hinner now match those explicit parameters, and the conclusion is abs(G h)<=K, exactly the middle expression in hend.trans_le.',
   'All six public complete headers, all other proof bytes, imports, actual flow choices, parameter-loss order and default resource settings remain unchanged.',
   'Source/base/diff/log/prior-owner/prior-peer identities and exact7ac Git preimage were checked; the inverse one-line transformation reproduces the full preimage.'
 ],
 'findings':[],'compiled':False,'source_modified':False,
 'scope_limits':['Static exact-source repair review only; complete validation and default-budget performance remain for the next authorized CI. No compiler, active source/index/ref or CI operation was performed for this review.'],
 'created_at':datetime.now(timezone.utc).isoformat()}
out=Path(__file__).with_name('CI161N01ControlFlowBoundsIndependentReview.json');assert not out.exists()
out.write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(fp(out)))
