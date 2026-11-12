"""Read-only Git dependency inventory for the fixed-witness gateway review."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

REPO = Path('/workspace/scratch/bbbea77e4163/continuous-flexibility')
OUT = Path('/workspace/scratch/bbbea77e4163/n04-drafts/positive/gateway')
MAIN = 'ebfd528f2dd0c690799187be45b7c5a5c4c6b26a'
HEAD = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip()
SPECS = {
    'n01c': ('bb419aa4e85af1b01a3edb0f6113e5f0a242f6d7', [
        'ContinuousFlexibility.Analysis.N01cActualReferenceWith',
        'ContinuousFlexibility.Blueprint.N01c.Coefficients',
        'ContinuousFlexibility.Blueprint.N01c.Speeds',
        'ContinuousFlexibility.Blueprint.N01c.Flows']),
    'n02n03': ('c5c48d262157a11a76604113c40d2438d480433f', [
        'ContinuousFlexibility.Analysis.N01CorrectionCoefficientMaterialTame',
        'ContinuousFlexibility.Analysis.N01ResidualSmoothTame',
        'ContinuousFlexibility.Analysis.N03CorrectionAssembly',
        'ContinuousFlexibility.Analysis.N03SourceFromActualCoefficientJets',
        'ContinuousFlexibility.Analysis.ReturnCorrectionUniformNeighborhood'])}

def tree(ref):
    raw = subprocess.check_output(['git', 'ls-tree', '-rz', ref, 'src'], cwd=REPO)
    result = {}
    for row in raw.split(b'\0'):
        if not row:
            continue
        meta, path = row.split(b'\t', 1)
        mode, kind, sha = meta.decode().split()
        result[path.decode()] = {'mode': mode, 'kind': kind, 'blob': sha}
    return result

def strip_comments(text):
    # Preserve newlines for review locations; support nested Lean block comments.
    out, depth, i = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            out.extend('  ')
            i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1
            out.extend('  ')
            i += 2
        elif depth:
            out.append('\n' if text[i] == '\n' else ' ')
            i += 1
        elif text[i:i+2] == '--':
            j = text.find('\n', i)
            if j == -1:
                j = len(text)
            out.extend(' ' * (j-i))
            i = j
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)

main_tree, head_tree = tree(MAIN), tree(HEAD)
proc = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=REPO,
                        stdin=subprocess.PIPE, stdout=subprocess.PIPE)
cache = {}
def read_blob(sha):
    if sha not in cache:
        proc.stdin.write((sha+'\n').encode())
        proc.stdin.flush()
        header = proc.stdout.readline().decode().split()
        assert header[1] == 'blob', header
        data = proc.stdout.read(int(header[2]))
        assert proc.stdout.read(1) == b'\n'
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() == sha
        cache[sha] = data
    return cache[sha]

summary = {}
for label, (ref, seeds) in SPECS.items():
    tt, visited, missing = tree(ref), {}, []
    pending = list(seeds)
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        path = 'src/' + module.replace('.', '/') + '.lean'
        if path not in tt:
            missing.append({'module': module, 'path': path})
            continue
        data = read_blob(tt[path]['blob'])
        source = data.decode()
        clean = strip_comments(source)
        imports = re.findall(r'^import\s+(\S+)', clean, re.M)
        owned_imports = [s for s in imports if s.startswith('ContinuousFlexibility.')]
        row = {
            'module': module, 'path': path, **tt[path],
            'sha256': hashlib.sha256(data).hexdigest(),
            'line_count': len(source.splitlines()),
            'imports': imports,
            'main_blob': main_tree.get(path, {}).get('blob'),
            'installed_blob': head_tree.get(path, {}).get('blob'),
            'sorry_or_axiom_tokens': [
                {'line': clean[:m.start()].count('\n')+1, 'token': m.group()}
                for m in re.finditer(r'\b(?:sorry|sorryAx|axiom|native_decide|unsafe)\b', clean)]}
        row['differs_from_main'] = row['blob'] != row['main_blob']
        row['differs_from_installed'] = row['blob'] != row['installed_blob']
        visited[module] = row
        pending.extend(owned_imports)
    rows = sorted(visited.values(), key=lambda r:r['path'])
    report = {
        'kind': 'read_only_git_import_closure_inventory',
        'source_ref': ref, 'main_ref': MAIN, 'installed_ref': HEAD,
        'seed_modules': seeds, 'module_count': len(rows),
        'missing': missing, 'modules': rows,
        'unmerged_modules': [r for r in rows if r['differs_from_main']],
        'installed_source_differences': [r for r in rows if r['differs_from_installed']],
        'blueprint_modules': [r for r in rows if '.Blueprint.' in r['module']],
        'token_findings': [r for r in rows if r['sorry_or_axiom_tokens']],
        'limits': ['Textual import/declaration-token inventory, not Lean elaboration or theorem axiom inspection.',
                   'No source checkout, index, refs, or CI state was changed.']}
    dst = OUT / (label + '-closure.json')
    with dst.open('x') as f:
        json.dump(report, f, ensure_ascii=False, indent=2)
        f.write('\n')
    summary[label] = {'path': str(dst), 'sha256': hashlib.sha256(dst.read_bytes()).hexdigest(),
                      'modules': len(rows), 'unmerged': len(report['unmerged_modules']),
                      'installed_differences': len(report['installed_source_differences']),
                      'missing': missing,
                      'blueprint': [r['module'] for r in report['blueprint_modules']],
                      'tokens': [{'module': r['module'], 'findings': r['sorry_or_axiom_tokens']}
                                 for r in report['token_findings']]}
proc.stdin.close()
proc.wait()
print(json.dumps(summary, ensure_ascii=False, indent=2))
