"""Static full-tree namespace/declaration collision inventory. No Lean execution."""
from pathlib import Path
import collections, datetime, hashlib, json, re, subprocess
W=Path('/workspace/scratch/bbbea77e4163'); REPO=W/'continuous-flexibility'; OUT=Path(__file__).resolve().parent
tables=json.loads((OUT/'MainC9SourceTables.json').read_text())
selected=tables['selected']; active=tables['active']
rebound_active='bd249b94d15dd2242e189bcd91c7e378ea7875d9'
old_active=tables['exact_refs']['active']
delta=subprocess.check_output(['git','-C',str(REPO),'diff','--name-status',old_active,rebound_active,'--','src'],text=True)
for line in delta.splitlines():
    status,path=line.split('\t')
    if not path.endswith('.lean') or path=='src/ContinuousFlexibility.lean':continue
    assert status in ('M','A')
    m=path[4:-5].replace('/','.')
    oldrow=active.get(m)
    b=subprocess.check_output(['git','-C',str(REPO),'show',rebound_active+':'+path])
    bid=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    row=dict(module=m,target_path=path,source_ref=rebound_active,blob=bid,sha256=hashlib.sha256(b).hexdigest(),lines=len(b.splitlines()),imports=re.findall(r'^import\s+(\S+)',b.decode(),re.M))
    active[m]=row
    if m not in selected or (oldrow and selected[m]['blob']==oldrow['blob']):selected[m]=row
for m,r in active.items():
    r['source_ref']=rebound_active
    if m in selected and selected[m]['blob']==r['blob']:selected[m]['source_ref']=rebound_active
def blob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def fp(p):
    b=Path(p).read_bytes();return dict(path=str(p),blob=blob(b),sha256=hashlib.sha256(b).hexdigest(),lines=len(b.splitlines()))
extra={}
for directory,names in [
    ('positive/compatibility/main-c9-flow-values',['CanonicalVariationBounds','N01OrdinaryFlowClosedJets','OrdinaryFlowJacobianBounds','N01ReturnInverseJets']),
    ('quantitative/compatibility/main-n01c-parameter-order',['N01JetBounds','CanonicalNeighborhoodRestriction','MaterialEnvelopeNormalization']),
    ('positive/compatibility/main-c9-neighborhood-provider',['N01NeighborhoodRestriction']),
    ('positive/compatibility/main-c9-mixed-provider',['LocalMixedProductBounds'])]:
    for name in names:
        p=W/'n04-drafts'/directory/(name+'.lean');m='ContinuousFlexibility.Analysis.'+name
        row=fp(p);row.update(module=m,target_path='src/'+m.replace('.','/')+'.lean',source_path=str(p),source_ref='LOCAL_HELD_MAIN_CONTRACT_COMPATIBILITY',imports=re.findall(r'^import\s+(\S+)',p.read_text(),re.M))
        extra[m]=row
selected.update(extra)
ids=sorted({r['blob'] for r in selected.values() if not r['source_ref'].startswith('LOCAL')}|
    {r['blob'] for r in active.values()})
p=subprocess.run(['git','-C',str(REPO),'cat-file','--batch'],input=('\n'.join(ids)+'\n').encode(),stdout=subprocess.PIPE,check=True)
raw={};pos=0
for bid in ids:
    end=p.stdout.index(b'\n',pos);h=p.stdout[pos:end].decode().split();assert h[:2]==[bid,'blob']
    size=int(h[2]);raw[bid]=p.stdout[end+1:end+1+size];pos=end+size+2
assert pos==len(p.stdout)
for r in selected.values():
    if r['source_ref'].startswith('LOCAL'):
        b=Path(r['source_path']).read_bytes();assert blob(b)==r['blob'];raw[r['blob']]=b

def uncomment(s):
    out=[];i=0;depth=0;tokens=re.compile(r'/\-|-\/|--')
    while i<len(s):
        q=tokens.search(s,i)
        if q is None:out.append(s[i:] if not depth else '\n'*s[i:].count('\n'));break
        out.append(s[i:q.start()] if not depth else '\n'*s[i:q.start()].count('\n'))
        token=q.group()
        if depth:
            if token=='/-':depth+=1
            elif token=='-/':depth-=1
            out.append(' ');i=q.end()
        elif token=='--':
            end=s.find('\n',q.end())
            if end<0:break
            out.append('\n');i=end+1
        elif token=='/-':depth=1;out.append(' ');i=q.end()
        else:out.append(token);i=q.end()
    return ''.join(out)

def declarations(b):
    text=uncomment(b.decode());stack=[];ns='';result=[];warnings=[]
    for i,line in enumerate(text.splitlines(),1):
        if line.startswith('namespace '):
            name=line.split()[1];stack.append(('namespace',name,ns))
            ns=name[7:] if name.startswith('_root_.') else '.'.join(x for x in (ns,name) if x)
        elif re.match(r'^(?:noncomputable\s+)?section(?:\s|$)',line):
            tail=line.split('section',1)[1].strip();stack.append(('section',tail,ns))
        elif re.match(r'^end(?:\s|$)',line):
            if not stack:warnings.append(dict(line=i,kind='unmatched_end',text=line));continue
            _,name,oldns=stack.pop();ns=oldns
        clean=re.sub(r'^(?:@\[[^\n]*?\][ \t]*)+','',line)
        q=re.match(r'^(?:(noncomputable|protected|private|nonrec)\s+)*(def|theorem|lemma|abbrev|structure|class|inductive|opaque)\s+([^\s(:{]+)',clean)
        if q and not re.search(r'\bprivate\b',clean[:q.start(2)]):
            kind=q.group(2);name=q.group(3)
            fullname=name[7:] if name.startswith('_root_.') else '.'.join(x for x in (ns,name) if x)
            result.append(dict(name=fullname,short=name.split('.')[-1],kind=kind,line=i))
        q=re.match(r'^(?:(?:noncomputable|scoped)\s+)?instance\s+([^\s(:{]+)',clean)
        if q:
            name=q.group(1)
            if name not in ('where',':='):
                fullname=name[7:] if name.startswith('_root_.') else '.'.join(x for x in (ns,name) if x)
                result.append(dict(name=fullname,short=name.split('.')[-1],kind='named_instance',line=i))
        if re.match(r'^export\s+',line):warnings.append(dict(line=i,kind='export_alias_not_expanded',text=line))
    if any(k=='namespace' for k,n,o in stack):warnings.append(dict(kind='unclosed_namespace',stack=stack))
    return result,warnings

cache={bid:declarations(b) for bid,b in raw.items()}
def public_index(rows):
    index=collections.defaultdict(list);warnings=[]
    for m,r in rows.items():
        ds,ws=cache[r['blob']]
        for decl in ds:index[decl['name']].append(dict(decl,module=m,blob=r['blob']))
        warnings.extend(dict(x,module=m) for x in ws)
    return index,warnings
oldindex,oldwarnings=public_index(active);index,warnings=public_index(selected)
oldcollisions={n for n,v in oldindex.items() if len(v)>1}
collisions={n:v for n,v in index.items() if len(v)>1}
introduced={n:v for n,v in collisions.items() if n not in oldcollisions or
    {(x['module'],x['blob']) for x in v}!={(x['module'],x['blob']) for x in oldindex[n]}}
updates={m:r for m,r in selected.items() if m not in active or active[m]['blob']!=r['blob']}
missing=[[m,i] for m,r in selected.items() for i in r['imports'] if i.startswith('ContinuousFlexibility.') and i not in selected]
visiting=set();seen=set();order=[];cycles=[]
def walk(m):
    if m in seen:return
    if m in visiting:cycles.append(m);return
    visiting.add(m)
    for dep in selected[m]['imports']:
        if dep in selected:walk(dep)
    visiting.remove(m);seen.add(m);order.append(m)
for m in selected:walk(m)
report=dict(kind='main_c9_full_active_tree_selected_public_collision_and_import_inventory',
    status='STATIC_SCAN_HELD_NOT_LEAN_COMPILATION',active_reference=rebound_active,active_rebind_delta=delta.splitlines(),source_tables=fp(OUT/'MainC9SourceTables.json'),
    selected_module_count=len(selected),updated_modules=len(updates),public_names=len(index),
    preexisting_scan_collisions={n:oldindex[n] for n in sorted(oldcollisions)},
    newly_introduced_collisions=introduced,parser_warnings=warnings,
    missing_imports=missing,cycles=cycles,
    selected_sources=[selected[m] for m in sorted(selected)],active_sources=[active[m] for m in sorted(active)],topological_order=order,
    scope='Namespace-aware explicit declaration and named-instance scan. Structure-generated declarations and export aliases are not automatically expanded. No typechecking or active mutation.',
    created_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
dest=OUT/'MainC9SelectedFullTreePublicScanCI155Draft.json';dest.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(dict(report=fp(dest),selected_modules=len(selected),updates=len(updates),
    public_names=len(index),introduced_collisions=introduced,preexisting_count=len(oldcollisions),
    warning_count=len(warnings),warnings=warnings,missing=missing,cycles=cycles),indent=2,ensure_ascii=False))
