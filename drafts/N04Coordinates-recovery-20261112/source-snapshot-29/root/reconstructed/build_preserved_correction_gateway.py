import difflib
import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
repo = root / 'continuous-flexibility'
drafts = root / 'n04-drafts'
folder = drafts / 'root/compatibility/n03-preserved-fields'
folder.mkdir(parents=True, exist_ok=True)
ref = 'c5c48d262157a11a76604113c40d2438d480433f'
target = 'src/ContinuousFlexibility/Analysis/N03CorrectionAssembly.lean'
old = subprocess.check_output(['git', 'show', ref + ':' + target], cwd=repo).decode()
assert hashlib.sha256(old.encode()).hexdigest() == 'f9b89f4fdcfba29776b065b0094bc2f95403653894a6232922e359df175781ad'
old_path = folder / 'N03CorrectionAssembly.base.lean.txt'
old_path.write_text(old)
start = old.index('theorem N01Properties.exists_returnCorrection_of_smoothTame_source')
end = old.index('\nend ContinuousFlexibility.Statements', start)
original = old[start:end]
header, body = original.split(' := by\n', 1)
strong_header = header.replace('theorem N01Properties.exists_returnCorrection_of_smoothTame_source',
                              'theorem N01Properties.n04_exists_returnCorrection_preserving_fields')
old_result = '    ∃ L : ReturnCorrectionData S, L.error = E ∧ N03Properties D T S C R L base ε'
new_result = '''    ∃ L : ReturnCorrectionData S,
      L.coefficients = returnCorrectedCoefficients D S C χ ∧
      L.minusFlow = returnCorrectedMinusFlow S C χ ∧
      L.error = E ∧ N03Properties D T S C R L base ε'''
assert old_result in strong_header
strong_header = strong_header.replace(old_result, new_result)
assert '  refine ⟨L, rfl, ?_⟩' in body
strong_body = body.replace('  refine ⟨L, rfl, ?_⟩', '  refine ⟨L, rfl, rfl, rfl, ?_⟩')
wrapper = '''  obtain ⟨L, _hcoefficients, _hminusFlow, herror, hL⟩ :=
    hN.n04_exists_returnCorrection_preserving_fields hR hS hT χ
      hχ hχrange hsupp hend hdisc hflow E hE htame
  exact ⟨L, herror, hL⟩
'''
new = old[:start] + strong_header + ' := by\n' + strong_body + '\n' + header + ' := by\n' + wrapper + old[end:]
source = folder / 'N03CorrectionAssembly.lean'
assert not source.exists()
source.write_text(new)
diff = folder / 'N03CorrectionAssembly.diff'
diff.write_text(''.join(difflib.unified_diff(old.splitlines(True), new.splitlines(True),
                                          fromfile=str(old_path), tofile=str(source))))
assert new[:start] == old[:start]
assert strong_body.replace('  refine ⟨L, rfl, rfl, rfl, ?_⟩', '  refine ⟨L, rfl, ?_⟩') == body

gateway_old_path = drafts / 'positive/gateway/n02n03-c5c48/N02N03FixedWitnessConstruction.lean'
gateway_old = gateway_old_path.read_text()
assert hashlib.sha256(gateway_old.encode()).hexdigest() == '932d95fa60bd0030099cf3c2d638f467040783e3c05fa1a60fa3f5558188cbb0'
gateway = gateway_old.replace('theorem N01Properties.exists_through03_fixedWitness',
                              'theorem N01Properties.n04_exists_through03_preserving_correction')
gateway = gateway.replace('local instance n02n03FixedWitnessStateSMul',
                          'local instance n04FixedCorrectionStateSMul')
a = gateway.index('/-!')
b = gateway.index('-/', a) + 2
gateway = gateway[:a] + '''/-!
# Retain the actual correction in the fixed N01 construction

The same N02/N03 construction retains its selected cutoff family, its
actual corrected coefficients and minus flow, and the true cutoff support
and material derivative data. These identities connect the constructed
return record to the directional towers of its actual corrected flow.
The reference, material data, physical spaces and control geometry stay fixed.
-/''' + gateway[b:]
old_result = '''    ∃ R : ReturnEquationData S, ∃ L : ReturnCorrectionData S,
      ∃ base' : ℕ, ∃ ε' : ℝ,
        base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
          NonlinearPropertiesThrough03 D T S C R L base' loss ε' '''
# Preserve the exact original header before replacing its result.
result_start = gateway.index('    ∃ R : ReturnEquationData S, ∃ L : ReturnCorrectionData S,')
result_end = gateway.index(' := by\n', result_start)
gateway = gateway[:result_start] + '''    ∃ R : ReturnEquationData S, ∃ L : ReturnCorrectionData S,
      ∃ χ : ℕ → ℝ → ℝ, ∃ cell : ℕ → ℕ, ∃ base' : ℕ, ∃ ε' : ℝ,
        base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
          NonlinearPropertiesThrough03 D T S C R L base' loss ε' ∧
          L.coefficients = returnCorrectedCoefficients D S C χ ∧
          L.minusFlow = returnCorrectedMinusFlow S C χ ∧
          (∀ m, ContDiff ℝ ∞ (χ m)) ∧
          (∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1) ∧
          (∀ m, Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m)) ∧
          (∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
            χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1)) ∧
          (∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (cell m)) ∧
          (∀ k : ℕ, ∃ B Q : ℝ, 0 ≤ B ∧ 0 ≤ Q ∧ ∀ m r,
            |iteratedDeriv k (χ m) r| ≤ B * radialE (D.cellIndex (cell m)) ^ Q)''' + gateway[result_end:]
old_tail = '''  obtain ⟨L, _, hL⟩ := hN'.exists_returnCorrection_of_smoothTame_source hR hS hT
    χ hχ hχrange hsupp hend hdiscFull hcorrected E hE' htame
  exact ⟨R, L, base', ε', hbase, hε', hε'ε, ⟨⟨hN', hR⟩, hL⟩⟩'''
new_tail = '''  obtain ⟨L, hLcoefficients, hLminusFlow, _hLerror, hL⟩ :=
    hN'.n04_exists_returnCorrection_preserving_fields hR hS hT
      χ hχ hχrange hsupp hend hdiscFull hcorrected E hE' htame
  exact ⟨R, L, χ, j, base', ε', hbase, hε', hε'ε, ⟨⟨hN', hR⟩, hL⟩,
    hLcoefficients, hLminusFlow, hχ, hχrange, hsupp, hend, hcell, hcutoff⟩'''
assert old_tail in gateway
gateway = gateway.replace(old_tail, new_tail)
gateway_path = folder / 'N04FixedCorrectionWitness.lean'
assert not gateway_path.exists()
gateway_path.write_text(gateway)
gateway_diff = folder / 'N04FixedCorrectionWitness.diff'
gateway_diff.write_text(''.join(difflib.unified_diff(gateway_old.splitlines(True), gateway.splitlines(True),
                                                  fromfile=str(gateway_old_path), tofile=str(gateway_path))))
assert gateway_old.split(' := by\n', 1)[1].split(old_tail)[0] == gateway.split(' := by\n', 1)[1].split(new_tail)[0]

def ident(p):
    p = Path(p)
    raw = p.read_bytes()
    return {'path': str(p), 'sha256': hashlib.sha256(raw).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
            'lines': len(raw.decode().splitlines())}

mf = folder / 'N04PreservedCorrectionWitnessCandidateManifest.json'
manifest = {
    'kind': 'actual_N03_record_fields_and_cutoff_preserved_fixed_witness_gateway',
    'owner': '/root', 'status': 'CANDIDATE_HELD_UNCOMPILED_PENDING_INDEPENDENT_FULL_REVIEW',
    'sources': [dict(ident(source), target_path=target),
                dict(ident(gateway_path), target_path='src/ContinuousFlexibility/Analysis/N04FixedCorrectionWitness.lean')],
    'upstream_reference': ref, 'upstream_N03_base': ident(old_path),
    'original_gateway': ident(gateway_old_path),
    'original_gateway_manifest': ident(drafts / 'positive/gateway/n02n03-c5c48/N02N03FixedWitnessConstructionCandidateManifest.json'),
    'exact_diffs': [ident(diff), ident(gateway_diff)],
    'public_contract_preservation': [
        'Original N03 exists_returnCorrection_of_smoothTame_source full header remains byte-identical; its wrapper discards only the two newly retained literal field equalities.',
        'The private spatial proof and all original N03 construction clauses are byte-identical. The same local record is returned with coefficients and minusFlow equalities proved by rfl.',
        'The fixed-witness proof before its terminal N03 constructor application is byte-identical to the original108 gateway. It keeps the same R, E, chi, cell, base and radius choices.',
        'The new gateway returns the actual corrected record identities and genuine cutoff smoothness/range/support/endpoint germs/cell/material derivative data, with no new mathematical hypotheses.'
    ],
    'selected_contract_requirement': 'Select the reviewed main parameter-order compatibility graph for the N02/N03 consumers; no original c5 uniform-parameter-loss contract is restored.',
    'scope_limits': [
        'This is a fixed-witness constructive gateway. It does not identify an arbitrary existential N03 witness with the explicit corrected record.',
        'No final CurrentJets, primitive estimate, reference-family bound or raw optical certificate is inserted as an assumption.',
        'No local compiler/CI or active source/index/ref mutation. The new N03 source is a selected-provider extension that needs exact graph rebinding and peer review before activation.'
    ],
    'compiled': False, 'created_at': datetime.now(timezone.utc).isoformat()
}
mf.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'sources': manifest['sources'], 'manifest': ident(mf), 'full_original_proof_bodies_preserved': True}))
print(gateway_diff.read_text())
