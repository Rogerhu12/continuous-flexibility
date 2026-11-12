"""Verify the frozen 25-source group; activate only after complete current-head CI."""
from pathlib import Path
import argparse, hashlib, json, re, subprocess, datetime
ROOT=Path('/workspace/scratch/bbbea77e4163'); REPO=ROOT/'continuous-flexibility'
def git(*a): return subprocess.check_output(['git',*a],cwd=REPO,text=True).strip()
def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def blob(raw): return hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
def imports(txt): return re.findall(r'^import\s+(\S+)',txt,re.M)
def names(txt): return re.findall(r'^(?:(?:noncomputable|protected)\s+)?(?:theorem|def|structure|abbrev|class|inductive|opaque)\s+([^\s(:{]+)',txt,re.M)
parser=argparse.ArgumentParser();parser.add_argument('--stage-label',type=int);args=parser.parse_args()
proposal=ROOT/'n04-next-whole-atlas-group-held.json'; m=json.loads(proposal.read_text()); assert digest(proposal)=='c7da090b6977ce0391b34b490acd94552a56b1dcc59546105a1d56d5d781b56f'
cp_path=ROOT/'n04-active-checkpoint.json';cp_raw=cp_path.read_bytes();cp=json.loads(cp_raw);assert not git('status','--porcelain');assert git('rev-parse','HEAD')==cp['head'];assert git('rev-parse','HEAD^{tree}')==cp['tree'];assert git('merge-base','HEAD','origin/main')==git('rev-parse','origin/main')
files=m['files']; assert len(files)==25; chosen={x['module']:x for x in files};text_by={};newnames=[];reviews=[]
for f in files:
 p=Path(f['source']);raw=p.read_bytes();assert digest(p)==f['sha256'] and blob(raw)==f['blob'];assert len(p.read_text().splitlines())==f['lines'];assert not (REPO/f['file']).exists();assert imports(p.read_text())==f['imports'];assert not re.search(r'^\s*(?:axiom|unsafe\b|native_decide\b|sorry\b)',p.read_text(),re.M);text_by[f['module']]=p.read_text();newnames+=names(p.read_text())
 for k,v in f.items():
  if isinstance(v,dict) and 'review' in k and 'path' in v:
   assert digest(v['path'])==v['sha256'];reviews.append(v)
assert len(newnames)==m['public_name_count']==71 and len(newnames)==len(set(newnames))
installed={}; allnames=set()
for p in subprocess.check_output(['rg','--files','src/ContinuousFlexibility','-g','*.lean'],cwd=REPO,text=True).splitlines():
 path=REPO/p;mod=p[4:-5].replace('/','.');txt=path.read_text();installed[mod]=(path,txt);allnames.update(names(txt))
assert not (set(newnames)&allnames),sorted(set(newnames)&allnames)
reviews_by={
 'ContinuousFlexibility.Statements.Nonlinear':('97aa466ceee79bd9e21887d8948042478820ca79','7a05b947965738dcb91957059e102f9ea813e52b',ROOT/'n04-drafts/root/reviews/HeldWholeAtlasMain40242ProviderRebindingReview.json','c94645483e3e0a87c70fb0a443f0847337054c7a6485ead4cca61deeaffa90bd'),
 'ContinuousFlexibility.Blueprint.Statements':('8652b4ea403cea588d932c7504b385828cfb04c0','af5ba9dacc2c7b026d6535f09e886ce22ca2e673',ROOT/'n04-drafts/root/reviews/HeldWholeAtlasMain40242ProviderRebindingReview.json','c94645483e3e0a87c70fb0a443f0847337054c7a6485ead4cca61deeaffa90bd'),
 'ContinuousFlexibility.Analysis.OneSidedWholeComponentTransport':('5dce3683121cbe14c1668fe8af8a29ee5efdb23d','59c088961e44cc8c2f265831f64c71700c8f9dcb',ROOT/'n04-drafts/root/repair134/OneSidedWholeComponentTransportCI134RootReview.json','6a8e5e1f254e254e23e9107322a208e417e0d4c0a6c747954b803ef3470e25d2'),
 'ContinuousFlexibility.Analysis.WholeComponentReferenceIdentity':('9ec6ff71dd12429ac90af05b1ad52bb2bb774dc3','2ee9d541738dddf81c5e1c40288850ae337ee0c2',ROOT/'n04-drafts/root/repair135/WholeComponentReferenceIdentityCI135RootReview.json','0a7e9ab983d585f00701daf827046b250ea9ee77046aadf2ef1231639e58bc36'),
 'ContinuousFlexibility.Analysis.WholePositiveTransportAssembly':('c48c9514699ff3ee2d292eb0aa0e32b2c70bc39c','50a48bb4413593159f910338e52055459f07cc04',ROOT/'n04-drafts/root/repair136/WholePositiveTransportAssemblyCI136RootReview.json','3e38fd2554a098b4bebc2a8e078906fb57ca2f3e1aa019de952733572b152c72')}
changes=[]
for mod,old in m['installed_transitive_module_blobs'].items():
 path,txt=installed[mod];new=blob(path.read_bytes())
 if new!=old:
  before,after,r,h=reviews_by[mod];assert old==before and new==after and digest(r)==h;changes.append({'module':mod,'before':old,'after':new,'review':{'path':str(r),'sha256':h}})
assert len(changes)==5
seen=set();visiting=set();order=[]
def walk(mod):
 if not mod.startswith('ContinuousFlexibility.'):return
 if mod in seen:return
 assert mod not in visiting,mod;visiting.add(mod)
 if mod in chosen:txt=text_by[mod]
 else:assert mod in installed,mod;txt=installed[mod][1]
 for dep in imports(txt):walk(dep)
 visiting.remove(mod);seen.add(mod)
 if mod in chosen:order.append(mod)
for mod in m['topological_order']:walk(mod)
assert order==m['topological_order'];assert len(seen)==568;assert len(seen-set(chosen))==543
report={'kind':'frozen_group_current_provider_rebinding','status':'HELD_STATIC_PREFLIGHT_ONLY','checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'proposal':str(proposal),'proposal_sha256':digest(proposal),'head':cp['head'],'tree':cp['tree'],'files':25,'source_lines':sum(f['lines'] for f in files),'project_closure':len(seen),'installed_closure':len(seen-set(chosen)),'public_names':len(newnames),'collisions':[],'exact_review_count':len(reviews),'rebound_anchors':changes,'current_ci':cp['current_ci']}
pre=ROOT/'n04-next-whole-atlas-ci138-preflight.json';pre.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
if args.stage_label is not None:
 assert cp['current_ci']['status']=='success' and cp['last_full_green']['sha']==cp['head'];assert args.stage_label==cp['current_ci']['label']+1
 payload_path=ROOT/f'n04-ci{args.stage_label}-tree-payload.json';plan_path=ROOT/f'n04-ci{args.stage_label}-plan.json';assert not payload_path.exists() and not plan_path.exists()
 for f in files:(REPO/f['file']).write_bytes(Path(f['source']).read_bytes())
 subprocess.run(['python3','scripts/gen_root.py'],cwd=REPO,check=True)
 paths=[f['file'] for f in files]+['src/ContinuousFlexibility.lean'];subprocess.run(['git','add','--',*paths],cwd=REPO,check=True);subprocess.run(['git','diff','--cached','--check'],cwd=REPO,check=True)
 assert set(git('diff','--cached','--name-only').splitlines())==set(paths);assert not git('diff','--name-only')
 stats=git('diff','--cached','--numstat',cp['last_full_green']['sha'],'--','*.lean').splitlines();added=sum(int(x.split('\t')[0]) for x in stats);deleted=sum(int(x.split('\t')[1]) for x in stats);assert added<=20000;assert added==2807 and deleted==0
 payload={'repository_full_name':'Rogerhu12/continuous-flexibility','base_tree_sha':cp['tree'],'tree_elements':[{'path':p,'mode':'100644','type':'blob','content':(REPO/p).read_text()} for p in paths]};payload_path.write_text(json.dumps(payload,ensure_ascii=False))
 plan={'label':args.stage_label,'parent':cp['head'],'tree':git('write-tree'),'added':added,'deleted':deleted,'changed_lean_files':len(paths),'payload':str(payload_path),'held_group':str(proposal),'held_group_sha256':digest(proposal),'preflight':str(pre),'preflight_sha256':digest(pre),'current_main':git('rev-parse','origin/main'),'source_modules':len(installed)+len(files),'generated_root_imports':len(imports((REPO/'src/ContinuousFlexibility.lean').read_text()))};plan_path.write_text(json.dumps(plan,indent=2)+'\n');print(json.dumps(plan))
else:print(json.dumps({k:v for k,v in report.items() if k not in ('current_ci','rebound_anchors')},ensure_ascii=False))
assert cp_path.read_bytes()==cp_raw
