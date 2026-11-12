from pathlib import Path
import subprocess, json, hashlib, difflib, re, datetime
W=Path('/workspace/scratch/bbbea77e4163'); REPO=W/'continuous-flexibility'; OUT=Path(__file__).resolve().parent
ACTIVE='34a496f78ec2c9f35f74d2eb3dfd48a1d4190909'
MAIN='c9cd90e7cbf7f1c8445477ec543c414c3cd06c42'
def read(name):
    return subprocess.check_output(['git','-C',str(REPO),'show',ACTIVE+':src/ContinuousFlexibility/Analysis/'+name+'.lean']).decode()
def once(s,a,b):
    assert s.count(a)==1,(a[:100],s.count(a))
    return s.replace(a,b)
def fp(p):
    b=p.read_bytes()
    return dict(path=str(p),blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(),sha256=hashlib.sha256(b).hexdigest(),lines=len(b.splitlines()))
def heads(t):
    out={}
    for m in re.finditer(r'^(?:private\s+)?(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev)\s+([^\s(:]+)',t,re.M):
        e=t.index(':=',m.end());out[m.group(1)]=t[m.start():e]
    return out
sources=[]
for name in ['CanonicalVariationBounds','N01OrdinaryFlowClosedJets','OrdinaryFlowJacobianBounds','N01ReturnInverseJets']:
    old=read(name);s=old
    if name=='CanonicalVariationBounds':
        s=once(s,
'''    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ N01FlowDisplacementBoundAtOrder T S C base loss ε s B := by
  obtain ⟨B, hB, hbound⟩ := (n01FlowJetBounds_of_properties hN) 1 s
  refine ⟨B, hB, ?_⟩''',
'''    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε) :
    ∃ parameterLoss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      N01FlowDisplacementBoundAtOrder T S C base (loss + parameterLoss) ε s B := by
  obtain ⟨parameterLoss, horders⟩ := (n01FlowJetBounds_of_properties hN) 1
  refine ⟨parameterLoss, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := horders s
  refine ⟨B, hB, ?_⟩''')
        start=s.index('theorem ordinaryFlowFamily_le_displacement_of_n01')
        end=s.index('/-- The angular flow difference',start)
        piece=s[start:end]
        piece=once(piece,'base (s + loss)\n','base (s + (loss + parameterLoss))\n')
        piece=once(piece,'simpa only [pow_zero, one_mul] using','simpa only [pow_zero, one_mul, Nat.add_assoc] using')
        s=s[:start]+piece+s[end:]
        s=once(s,
'''    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ N01FlowLinearHighBoundAtOrder T S C base loss ε s B := by
  obtain ⟨B, hB, hbound⟩ := ordinaryFlowFamily_le_displacement_of_n01 hT hN s
  refine ⟨B, hB, ?_⟩''',
'''    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε) :
    ∃ parameterLoss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      N01FlowLinearHighBoundAtOrder T S C base (loss + parameterLoss) ε s B := by
  obtain ⟨parameterLoss, horders⟩ := ordinaryFlowFamily_le_displacement_of_n01 hT hN
  refine ⟨parameterLoss, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := horders s
  refine ⟨B, hB, ?_⟩''')
        start=s.index('theorem ordinaryFlowFamily_le_linear_high_of_n01')
        piece=once(s[start:],'hgrade base (s + loss)','hgrade base (s + (loss + parameterLoss))')
        s=s[:start]+piece
        s=once(s,'variations control every fixed angular order by the state displacement. -/',
            'variations control all angular orders by the state displacement, with one\nparameter-order loss chosen before the angular order. -/')
    elif name=='N01OrdinaryFlowClosedJets':
        s=once(s,'passes to both endpoints with exactly the same material constant, grading,\nbase, and loss.',
            'passes to both endpoints with exactly the same material constant, grading,\nbase, and first-parameter loss, chosen before every angular order.')
        start=s.index('private theorem n01_closedFlow_bound_of_open_bound');end=s.index('/-- N01\'s actual angular variation bound',start)
        piece=once(s[start:end],'{base loss s : ℕ}','{base loss flowLoss s : ℕ}')
        piece=once(piece,'N01FlowLinearHighBoundAtOrder T S C base loss ε s B','N01FlowLinearHighBoundAtOrder T S C base flowLoss ε s B')
        piece=once(piece,'N01ClosedFlowLinearHighBoundAtOrder T S C base loss ε s B','N01ClosedFlowLinearHighBoundAtOrder T S C base flowLoss ε s B')
        s=s[:start]+piece+s[end:]
        s=once(s,'without changing its fixed loss or its state-independent constant. -/',
            'with one first-parameter loss fixed before every angular order and without\nchanging its state-independent constants. -/')
        s=once(s,
'''    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ N01ClosedFlowLinearHighBoundAtOrder T S C base loss ε s B := by
  obtain ⟨B, hB, hbound⟩ := ordinaryFlowFamily_le_linear_high_of_n01 hT hN s
  exact ⟨B, hB, n01_closedFlow_bound_of_open_bound hS hT hN hbound⟩''',
'''    (hN : N01Properties D T S C base loss ε) :
    ∃ parameterLoss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      N01ClosedFlowLinearHighBoundAtOrder T S C base (loss + parameterLoss) ε s B := by
  obtain ⟨parameterLoss, horders⟩ := ordinaryFlowFamily_le_linear_high_of_n01 hT hN
  refine ⟨parameterLoss, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := horders s
  exact ⟨B, hB, n01_closedFlow_bound_of_open_bound hS hT hN hbound⟩''')
    elif name=='OrdinaryFlowJacobianBounds':
        s=once(s,'  obtain ⟨B, hB, hbound⟩ := ordinaryFlowFamily_le_linear_high_of_n01 hT hN 1',
            '  obtain ⟨parameterLoss, horders⟩ := ordinaryFlowFamily_le_linear_high_of_n01 hT hN\n  obtain ⟨B, hB, hbound⟩ := horders 1')
        s=once(s,'(max base (1 + loss))','(max base (1 + (loss + parameterLoss)))')
    elif name=='N01ReturnInverseJets':
        start=s.index('private theorem n01_returnForwardJets_of_closed_bound');end=s.index('/-- The actual stored return inverse',start)
        piece=once(s[start:end],'{base loss : ℕ}','{base loss flowLoss : ℕ}')
        piece=once(piece,'N01ClosedFlowLinearHighBoundAtOrder T S C base loss ε n (B n)','N01ClosedFlowLinearHighBoundAtOrder T S C base flowLoss ε n (B n)')
        piece=once(piece,'N01ReturnForwardJetBound S C base (base + loss) ε m A','N01ReturnForwardJetBound S C base (base + flowLoss) ε m A')
        s=s[:start]+piece+s[end:]
        start=s.index('private theorem n01_returnInverse_bound_of_forward');end=s.index('/-- One low order',start)
        piece=once(s[start:end],'{base loss low outLoss : ℕ}','{base loss forwardLoss low outLoss : ℕ}')
        assert piece.count('(base + loss)')==2
        piece=piece.replace('(base + loss)','forwardLoss')
        s=s[:start]+piece+s[end:]
        s=once(s,
'''  obtain ⟨low, outLoss, htarget⟩ := scalarInverse_displacement_fixed_loss hp hI (base + loss)
  choose A hA hforward using
    (fun n => ordinaryFlowFamily_le_linear_high_on_closed_of_n01 hS hT hN n)''',
'''  obtain ⟨parameterLoss, horders⟩ :=
    ordinaryFlowFamily_le_linear_high_on_closed_of_n01 hS hT hN
  obtain ⟨low, outLoss, htarget⟩ :=
    scalarInverse_displacement_fixed_loss hp hI (base + (loss + parameterLoss))
  choose A hA hforward using horders''')
        s=once(s,'common low order and loss are selected before the component.',
            'common low order and loss are selected before the component. The first\nparameter-order loss is chosen once before every angular order.')
    p=OUT/(name+'.lean');assert not p.exists(),p;p.write_text(s)
    bp=OUT/(name+'.active34a496-base.lean.txt');bp.write_text(old)
    dp=OUT/(name+'.diff');dp.write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile=str(bp),tofile=str(p))))
    hb,ha=heads(old),heads(s);assert hb.keys()==ha.keys()
    changed=[n for n in hb if hb[n]!=ha[n]]
    sources.append(dict(module='ContinuousFlexibility.Analysis.'+name,target_path='src/ContinuousFlexibility/Analysis/'+name+'.lean',
        source=fp(p),base=fp(bp),diff=fp(dp),public_and_private_headers_changed=changed,other_header_count_preserved=len(hb)-len(changed)))
m=dict(kind='actual_active_flow_value_closed_jacobian_inverse_parameter_order_port',
    status='HELD_UNCOMPILED_PEER_PENDING_REQUIRES_NEW_MAIN_CONTRACT_AND_QUANT_ALIAS_PORTS',
    active_preimage=ACTIVE,selected_contract_ref=MAIN,selected_contract_blob='1f7afd5657e10ab0fd830323d7c4e6c701a99cd8',sources=sources,
    new_public_numeric_contracts=[
        'ordinaryFlowFamily_le_displacement_of_n01: exists parameterLoss before all spatial orders, with effective loss + parameterLoss.',
        'ordinaryFlowFamily_le_linear_high_of_n01: same ordering and same sampled material weights.',
        'ordinaryFlowFamily_le_linear_high_on_closed_of_n01: same single parameterLoss retained at genuine closed endpoints.'],
    qualitative_terminal_contracts_preserved=['exists_ordinaryFlowJacobianBounds_of_n01','exists_restricted_canonicalStage_with_ordinaryFlowJacobianBounds','n01_minusReturnInverse_displacement_fixed_loss'],
    provider_protocol=dict(owner='quantitative_route',N01FlowJetBoundAtOrder='base loss parameterLoss; high = s + loss + parameterLoss',
        N01FlowJetBounds='forall k, exists parameterLoss, forall s, exists B > 0, same AtOrder bound',
        quant_sources=['N01JetBounds','CanonicalNeighborhoodRestriction','MaterialEnvelopeNormalization']),
    checks=['All unchanged bodies, imports, options and declaration heads are retained verbatim except the listed explicit numeric and private separation of original loss from forward loss.',
        'The true first variation chooses parameterLoss only at k=1, before all spatial orders, components, states and directions.',
        'The forward inverse estimate retains one parameterLoss before selecting the common inverse low order and outLoss; no dependence is hidden in a material constant.',
        'No source/index/ref/CI/compiler changes outside this owner scratch directory.'],compiled=False,
    created_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
p=OUT/'CanonicalFlowValuesParameterOrderCandidateManifest.json';p.write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps(dict(manifest=fp(p),sources=sources),indent=2))
