import hashlib, json, re, subprocess
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
repo = root / 'continuous-flexibility'
out = root / 'n04-drafts/root/reconstructed'
def fp(path):
    path = Path(path)
    raw = path.read_bytes()
    return {'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(),
        'blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
        'lines': len(raw.splitlines())}
source = out / 'CanonicalReferenceScalarColumnIdentities.lean'
text = source.read_text()
assert not re.search(r'\b(sorry|admit|axiom)\b|set_option\s+(maxHeartbeats|maxRecDepth)', text)
names = re.findall(r'^(?:theorem|def) (\S+)', text, re.M)
for name in names:
    found = subprocess.run(['rg','-n',r'^(?:theorem|def)\s+'+re.escape(name)+r'\b',str(repo/'src')],capture_output=True,text=True)
    assert found.returncode == 1, (name,found.stdout)
providers = [
    'Analysis/N06LeftColumnPhysical.lean','Analysis/N06FiniteReferenceColumns.lean',
    'Analysis/N06ReferenceNuColumn.lean','Radial/ReferenceColumnSmooth.lean',
    'Radial/FourierModes.lean','Radial/R11bFourierTests.lean',
    'Statements/Nonlinear.lean','Statements/Analysis.lean','Statements/Radial.lean',
    'Analysis/LocalMixedProductBounds.lean']
manifest = {
    'kind':'same_actual_reference_left_and_nu_column_identities',
    'owner':'/root', 'status':'CANDIDATE_HELD_UNCOMPILED_PENDING_FULL_INDEPENDENT_REVIEW',
    'source':fp(source), 'public_names':names,
    'imports':re.findall(r'^import (.*)$', text,re.M),
    'actual_providers':[fp(repo/'src/ContinuousFlexibility'/p) for p in providers],
    'scalar_material_provider':fp(out/'FixedReferenceScalarSourceMaterialJets.lean'),
    'scalar_material_provider_owner':fp(out/'FixedReferenceScalarSourceMaterialJetsReviewedManifest.json'),
    'active_head_at_freeze':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),
    'checks':[
        'Read all104 selected lines and the actual N01/N03, canonicalSource/atom, physical cutoff and true-border contracts and callee statements.',
        'The left radial profile is the derivative of the original w*chiLeft derivative flux. Its global smoothness uses the actual physical cutoff and radial profile smoothness.',
        'The nu radial profile is the actual referenceColumn D; its global smooth extension at zero uses the existing true-border theorem. Its angular factor is the actual cosineMode2 with its proved pi period.',
        'The source pullback is factored algebraically through exactly the same stored inverse and sourceFactor atom. No Jacobian or height positivity is needed just for this identity.',
        'The reference corrected left column uses the actual N03 equality theorem; the nu column uses the N01 reference state and true positive radial core to discharge r nonzero.',
        'Only literal inverse/source-factor fields and a genuine radial-core range are assumptions. No canonical column estimate, alternate atlas or material witness is selected.'
    ],
    'scope_limits':[
        'This leaf proves identities and fixed physical-profile regularity. The subsequent numerical adapter must supply the actual source-factor and positive inverse jets at the original material samples.',
        'No final ReferenceJets or CurrentJets certificate is assumed or claimed. No compiler, resource override, active source/index/ref or CI action.'
    ],
    'compiled':False, 'created_at':datetime.now(timezone.utc).isoformat()}
path = out/'CanonicalReferenceScalarColumnIdentitiesCandidateManifest.json'
assert not path.exists()
path.write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'source':fp(source),'candidate':fp(path)}))
