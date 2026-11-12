import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
repo = root / 'continuous-flexibility'
old_path = root / 'n04-reviewed-provider-rebindings-ci154.json'
audit_path = root / 'n04-drafts/audit/reviews/ReferenceGroupProjectedMainProviderMigrationCI163ReadOnly.json'
proposal_path = root / 'n04-next-reference-group-held.json'

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=repo)

assert sha(old_path) == 'cd182acade817706cc4ccfce1bef581ef977580e0b7c98505d48c33d573e97b9'
assert sha(audit_path) == 'aae17c62ec1956b8ffe5d2037e3f2d8450eb56fdfbb9b45df93d252c361cb070'
assert sha(proposal_path) == 'e3df495b387d253732915923b113924c74fef74b8dd51310d20bcdbe68408f50'
old = json.loads(old_path.read_text())
audit = json.loads(audit_path.read_text())
proposal = json.loads(proposal_path.read_text())
assert git('rev-parse', 'HEAD').decode().strip() == audit['active_head']
assert not git('status', '--porcelain')
for record in audit['inputs'] + [audit['exact_projection_scan']] + list(audit['receipt_registry'].values()):
    raw = Path(record['path']).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == record['sha256']
    assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == record['blob']

def object_record(blob):
    raw = git('cat-file', 'blob', blob)
    assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == blob
    return {'git_blob': blob, 'blob': blob, 'sha256': hashlib.sha256(raw).hexdigest(),
            'lines': len(raw.decode().splitlines())}

ledger = dict(old)
ledger['transitions'] = {name: list(edges) for name, edges in old['transitions'].items()}
new_edges = []
rows = audit['required_current_provider_rebindings'] + audit['required_future_provider_rebindings']
assert len(rows) == 15
for row in rows + audit['additional_prerequisite_gate_rebindings']:
    chain = row.get('exact_chain') or [row['old'], row['projected']]
    for before, after in zip(chain, chain[1:]):
        refs = [audit['receipt_registry'][key] for key in row.get('receipt_keys', [])]
        edge = {'before': before, 'after': after,
                'before_source': object_record(before), 'after_source': object_record(after),
                'review': str(audit_path), 'review_sha256': sha(audit_path),
                'additional_review_records': refs,
                'scope': row.get('semantic_scope', 'Exact prerequisite-only reviewed repair chain; see linked owner and independent-review records.'),
                'projected_batch': row.get('batch')}
        edges = ledger['transitions'].setdefault(row['module'], [])
        assert not any(e['before'] == before and e['after'] == after for e in edges)
        edges.append(edge)
        new_edges.append({'module': row['module'], 'before': before, 'after': after})

old_nodes = set(proposal['provider_blobs']) | {row['module'] for row in proposal['files']}
assert len(old_nodes) == 865
added_nodes = {row['module']: row for row in audit['new_graph_nodes']}
assert len(added_nodes) == 2 and not old_nodes.intersection(added_nodes)
for row in added_nodes.values():
    assert git('rev-parse', audit['active_head'] + ':' + row['path']).decode().strip() == row['blob']
    row['source_object'] = object_record(row['blob'])
ledger['reviews'] = list(old['reviews']) + [{'path': str(audit_path), 'sha256': sha(audit_path)}]
ledger.update(kind='reviewed_provider_extension_for_exact_main_reference_cohort',
    status='PREPARED_NOT_ACTIVATED_REQUIRES_CURRENT_MAIN_ANCESTRY_AND_EXACT_FULL_GREEN',
    derived_from={'path': str(old_path), 'sha256': sha(old_path)},
    migration_review={'path': str(audit_path), 'sha256': sha(audit_path)},
    provider_graph_delta={'original_count': 865, 'projected_count': 867, 'added_nodes': added_nodes},
    new_edges=new_edges, prepared_at=datetime.now(timezone.utc).isoformat(),
    note='Git blob records preserve exact provider bytes without making additional source copies. Existing review records and source choices are unchanged. This extension permits only the explicitly reviewed version paths and the exact two-node graph delta. It does not stage sources, waive the main-ancestry requirement or assert compilation of held modules.')
out = root / 'n04-reviewed-provider-rebindings-current-main.json'
assert not out.exists()
out.write_text(json.dumps(ledger, ensure_ascii=False, indent=2) + '\n')

source = (root / 'n04-preflight-reference-family-ci154.py').read_text()
source = source.replace("'n04-reviewed-provider-rebindings-ci154.json'", "'n04-reviewed-provider-rebindings-current-main.json'")
source = source.replace("ledger_sha = 'cd182acade817706cc4ccfce1bef581ef977580e0b7c98505d48c33d573e97b9'", "ledger_sha = '" + sha(out) + "'")
needle = """            assert digest(source['path']) == source['sha256']
            assert blob(source['path']) == source['blob'] == edge[side]"""
replacement = """            if 'git_blob' in source:
                raw = subprocess.check_output(['git', 'cat-file', 'blob', source['git_blob']], cwd=REPO)
                assert hashlib.sha256(raw).hexdigest() == source['sha256']
                assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\\0' + raw).hexdigest() == source['blob'] == edge[side]
            else:
                assert digest(source['path']) == source['sha256']
                assert blob(source['path']) == source['blob'] == edge[side]"""
assert needle in source
source = source.replace(needle, replacement)
needle = "assert len(seen) == proposal['project_closure_count'] == 865"
replacement = """original_nodes = set(proposal['provider_blobs']) | set(selected)
delta = ledger['provider_graph_delta']
assert len(original_nodes) == proposal['project_closure_count'] == delta['original_count'] == 865
assert len(delta['added_nodes']) == 2
assert not original_nodes.intersection(delta['added_nodes'])
for mod, record in delta['added_nodes'].items():
    assert mod in providers and blob(providers[mod]) == record['blob']
assert seen == original_nodes | set(delta['added_nodes'])
assert len(seen) == delta['projected_count'] == 867"""
assert needle in source
source = source.replace(needle, replacement)
source = source.replace("'project_closure': 865, 'providers': 824", "'project_closure': 867, 'providers': 826")
source = source.replace("'n04-next-reference-current-preflight.json'", "'n04-next-reference-main-preflight.json'")
gate_path = root / 'n04-preflight-reference-family-main.py'
assert not gate_path.exists()
gate_path.write_text(source)
import ast
ast.parse(source)
assert "assert git('merge-base', 'HEAD', 'origin/main') == git('rev-parse', 'origin/main')" in source
assert "assert cp['current_ci']['status'] == 'success'" in source
assert "assert cp['last_full_green']['sha'] == cp['head']" in source
assert not git('status', '--porcelain')
print(json.dumps({'ledger': str(out), 'ledger_sha256': sha(out), 'new_edges': len(new_edges),
                  'gate': str(gate_path), 'gate_sha256': sha(gate_path),
                  'prepared_not_executed': True, 'exact_graph_delta': '865+2=867'}))
