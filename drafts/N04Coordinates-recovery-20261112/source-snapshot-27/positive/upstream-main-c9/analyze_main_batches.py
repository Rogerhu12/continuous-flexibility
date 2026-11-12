#!/usr/bin/env python3
"""Read-only repository source analysis; writes reports only beside this file."""
import collections
import datetime
import hashlib
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path('/workspace/scratch/bbbea77e4163')
REPO = ROOT / 'continuous-flexibility'
OUT = pathlib.Path(__file__).resolve().parent
ACTIVE = '34a496f78ec2c9f35f74d2eb3dfd48a1d4190909'
MAIN = 'c9cd90e7cbf7f1c8445477ec543c414c3cd06c42'
BASE = '89e539ccf7e9c558467cf875f44dcff9490ce271'
C5 = 'c5c48d262157a11a76604113c40d2438d480433f'

def git(*args):
    return subprocess.check_output(['git', '-C', str(REPO), *args])

def tree(ref):
    result = {}
    for record in git('ls-tree', '-rz', ref).split(b'\0'):
        if not record:
            continue
        head, path = record.split(b'\t', 1)
        mode, kind, blob = head.decode().split()
        if kind == 'blob':
            result[path.decode()] = (mode, blob)
    return result

TREES = {ref: tree(ref) for ref in (ACTIVE, MAIN, BASE, C5)}
BLOBS = {}
blob_ids = sorted({blob for t in TREES.values() for p, (_, blob) in t.items()
                   if p.endswith('.lean')})
raw = git('cat-file', '--batch', *[]) if False else None
proc = subprocess.run(['git', '-C', str(REPO), 'cat-file', '--batch'],
    input=('\n'.join(blob_ids) + '\n').encode(), stdout=subprocess.PIPE, check=True)
pos = 0
for blob in blob_ids:
    end = proc.stdout.index(b'\n', pos)
    header = proc.stdout[pos:end].decode().split()
    assert header[0] == blob and header[1] == 'blob', header
    size = int(header[2])
    BLOBS[blob] = proc.stdout[end+1:end+1+size]
    pos = end+size+2
assert pos == len(proc.stdout)

def content(ref, path):
    return BLOBS[TREES[ref][path][1]]

def sha(b):
    return hashlib.sha256(b).hexdigest()

def git_blob(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()

def module(path):
    assert path.startswith('src/') and path.endswith('.lean'), path
    return path[4:-5].replace('/', '.')

def path_for(m):
    return 'src/' + m.replace('.', '/') + '.lean'

def uncomment(s):
    # Source imports occur outside comments; preserve line layout.
    out = []; i = 0; depth = 0; line_comment = False; quoted = False
    while i < len(s):
        if line_comment:
            if s[i] == '\n': line_comment = False; out.append('\n')
            else: out.append(' ')
            i += 1; continue
        if depth:
            if s.startswith('/-', i): depth += 1; out.extend('  '); i += 2
            elif s.startswith('-/', i): depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
            continue
        if s.startswith('--', i): line_comment = True; out.extend('  '); i += 2
        elif s.startswith('/-', i): depth = 1; out.extend('  '); i += 2
        else: out.append(s[i]); i += 1
    return ''.join(out)

def imports(b):
    s = uncomment(b.decode())
    result = []
    for match in re.finditer(r'^\s*(?:public\s+)?import\s+([^\n]+)', s, re.M):
        for token in match.group(1).split():
            if re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*(?:«[^»]+»)?', token):
                result.append(token)
            else:
                raise ValueError(('unexpected import token', token))
    return result

def source_row(ref, p):
    b = content(ref, p)
    return dict(module=module(p), target_path=p, source_ref=ref,
        blob=git_blob(b), sha256=sha(b), lines=len(b.splitlines()),
        imports=imports(b))

def local_row(m, p):
    b = pathlib.Path(p).read_bytes()
    return dict(module=m, target_path=path_for(m), source_path=str(p),
        source_ref='LOCAL_HELD_REVIEWED_OR_PEER_PENDING',
        blob=git_blob(b), sha256=sha(b), lines=len(b.splitlines()),
        imports=imports(b))

def write(name, data):
    b = (json.dumps(data, indent=2, ensure_ascii=False) + '\n').encode()
    (OUT / name).write_bytes(b)
    return dict(path=str(OUT/name), blob=git_blob(b), sha256=sha(b), lines=len(b.splitlines()))

graph_file = ROOT/'n04-drafts/positive/gateway/n01c-n02-compat/N02N03AndCorrectedFlowParameterOrderSelectedInventory.json'
gateway = json.loads(graph_file.read_text())
local_ports = [x for x in gateway['modules'] if x['selected_ref'].startswith('LOCAL')]
ports = {}
comparisons = []
for x in local_ports:
    m = x['module']; p = path_for(m); row = local_row(m, x['path'])
    assert row['blob'] == x['blob'] and row['sha256'] == x['sha256']
    ports[m] = row
    item = dict(module=m, target_path=p, selected=row)
    for label, ref in [('active',ACTIVE), ('main',MAIN), ('c5',C5)]:
        item[label] = source_row(ref,p) if p in TREES[ref] else None
    item['active_relation'] = ('ABSENT' if item['active'] is None else
        'ALREADY_SELECTED' if item['active']['blob']==row['blob'] else
        'EXACT_C5_PREIMAGE' if item['c5'] and item['active']['blob']==item['c5']['blob'] else
        'DIFFERENT_ACTIVE_PREIMAGE_REVIEW_REQUIRED')
    comparisons.append(item)

for name in ['N04bSingletonType','N04bStateProfileType']:
    m='ContinuousFlexibility.Analysis.'+name
    p=ROOT/'n04-drafts/positive/compatibility/main-c9-flow-contract'/f'{name}.lean'
    ports[m]=local_row(m,p)

active = {module(p):source_row(ACTIVE,p) for p in TREES[ACTIVE]
    if p.startswith('src/') and p.endswith('.lean') and p!='src/ContinuousFlexibility.lean'}
main = {module(p):source_row(MAIN,p) for p in TREES[MAIN]
    if p.startswith('src/') and p.endswith('.lean') and p!='src/ContinuousFlexibility.lean'}
base = {module(p):source_row(BASE,p) for p in TREES[BASE]
    if p.startswith('src/') and p.endswith('.lean') and p!='src/ContinuousFlexibility.lean'}
upstream = {m:r for m,r in main.items() if m not in base or r['blob']!=base[m]['blob']}
effective = {m:r for m,r in upstream.items() if m not in active or r['blob']!=active[m]['blob']}

# Only ports already present on active are required by the upstream contract update.
# New direct/transitive imports of these selected ports are subsequently expanded.
selected = dict(active)
selected.update(effective)
selected_ports = {m:r for m,r in ports.items() if m in active}
selected.update(selected_ports)
gw = {x['module']:x for x in gateway['modules']}
new_port_dependencies = []
todo = list(selected_ports)
seen = set()
while todo:
    m=todo.pop()
    if m in seen: continue
    seen.add(m)
    for dep in selected[m]['imports']:
        if not dep.startswith('ContinuousFlexibility.'): continue
        if dep not in selected:
            assert dep in gw, ('missing local dependency',m,dep)
            x=gw[dep]
            if dep in ports:
                row=ports[dep]
            else:
                row=source_row(x['selected_ref'],x['path'])
            selected[dep]=row
            new_port_dependencies.append(dep)
            todo.append(dep)
        elif dep in selected_ports:
            todo.append(dep)

missing=[]
for m,row in selected.items():
    for dep in row['imports']:
        if dep.startswith('ContinuousFlexibility.') and dep not in selected:
            missing.append([m,dep])

def closure(roots, graph):
    seen=set(); todo=list(roots)
    while todo:
        m=todo.pop()
        if m in seen or m not in graph: continue
        seen.add(m); todo.extend(d for d in graph[m]['imports'] if d.startswith('ContinuousFlexibility.'))
    return seen

updates={m:r for m,r in selected.items() if m not in active or active[m]['blob']!=r['blob']}
def stats(mods):
    new=[m for m in mods if m not in active]
    modified=[m for m in mods if m in active]
    return dict(modules=len(mods),new=len(new),modified=len(modified),
        new_source_lines=sum(selected[m]['lines'] for m in new),
        modified_source_lines=sum(selected[m]['lines'] for m in modified))

groups={
 'nonlinear_contract': ['ContinuousFlexibility.Statements.Nonlinear'],
 'primitive_contract': ['ContinuousFlexibility.Blueprint.Statements'],
 'n01a_factory': ['ContinuousFlexibility.Analysis.N01aFinalAssembly','ContinuousFlexibility.Blueprint.N01a'],
 'n01c_factory': ['ContinuousFlexibility.Blueprint.N01c'],
 'n05': ['ContinuousFlexibility.Blueprint.N05'],
 'all_modified_main': [m for m in effective if m in active],
 'active_ports': list(selected_ports),
}
group_rows={}
for name, roots in groups.items():
    cl=closure(roots,selected); changed=cl&updates.keys()
    group_rows[name]=dict(roots=roots,closure_count=len(cl),updates=sorted(changed),stats=stats(changed))

report=dict(kind='READ_ONLY_MAIN_C9_TO_ACTIVE_BATCH_ANALYSIS_DRAFT',
    status='HELD_SOURCE_SELECTION_AND_ATOMIC_COHORT_ANALYSIS_NOT_COMPILATION',
    active=ACTIVE,main=MAIN,base=BASE,
    source_counts=dict(active=len(active),main=len(main),upstream_changed=len(upstream),
        effective_upstream_changed=len(effective),active_ports=len(selected_ports),
        newly_required_port_dependencies=len(new_port_dependencies),selected=len(selected)),
    local_port_preimages=comparisons,
    exact_active_port_selection=[selected_ports[m] for m in sorted(selected_ports)],
    new_port_dependencies=sorted(new_port_dependencies),
    update_rows=[dict(selected[m],active_preimage=active.get(m),base_preimage=base.get(m)) for m in sorted(updates)],
    missing_imports=missing,groups=group_rows,
    root_policy='Root is not selected or written. Parent alone runs scripts/gen_root.py at each actual activation.',
    note='The import-closed union has not been typechecked. Semantic compatibility, costs and batch ordering remain to be analysed.',
    generated_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
fp=write('MainC9ActiveSourceAnalysisDraft.json',report)
print(json.dumps(dict(report=fp,counts=report['source_counts'],port_relations=dict(collections.Counter(x['active_relation'] for x in comparisons)),new_port_dependencies=report['new_port_dependencies'],missing=missing,groups={k:v['stats'] for k,v in group_rows.items()}),indent=2))
