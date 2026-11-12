import difflib
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

root = Path('/workspace/scratch/bbbea77e4163')
folder = root / 'n04-drafts/root/reconstructed'
old_path = folder / 'CanonicalActualReferenceGeometry.lean'
old = old_path.read_text()
new = old.replace('theorem n04Coordinates_exists_actual_reference_geometry',
                  'theorem n04Coordinates_actual_reference_geometry_of_prescribed_family')
start = new.index('/-!')
end = new.index('-/', start) + 2
new = new[:start] + '''/-!
# Actual geometry on the supplied fixed reference family

The caller supplies the same coordinate and height already constructed
with their material estimates. Only the relative transport controls and
common neighborhood are selected here. Geometry, source pairing, radiality,
transmission and global transport all refer to the resulting same record.
-/''' + new[end:]
old_input = '''    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) (tsupport D.chi)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    ∃ Y H₀ : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ,
      N04PositiveReferenceFamily K j 4 Y H₀ ∧
      ∃ newBase : ℕ, ∃ ε' : ℝ,'''
new_input = '''    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) (tsupport D.chi))
    (Y H₀ : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ)
    (hreference : N04PositiveReferenceFamily
      (n04bActualTypedAtlas hT hS hN hfield e₀) j 4 Y H₀) :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    ∃ newBase : ℕ, ∃ ε' : ℝ,'''
assert old_input in new
new = new.replace(old_input, new_input)
old_choice = '''  obtain ⟨Y, H₀, hreference⟩ :=
    n04Coordinates_exists_positive_reference_family hT hS hN hfield e₀ j
      (show 1 ≤ (4 : ℕ) by decide)
'''
assert old_choice in new
new = new.replace(old_choice, '')
old_refine = '''  refine ⟨Y, H₀, hreference, newBase, ε', hb, hε', hε'ε,'''
new_refine = '''  refine ⟨newBase, ε', hb, hε', hε'ε,'''
assert old_refine in new
new = new.replace(old_refine, new_refine)
path = folder / 'CanonicalActualPrescribedReferenceGeometry.lean'
assert not path.exists()
path.write_text(new)
diff = ''.join(difflib.unified_diff(old.splitlines(True), new.splitlines(True),
                                  fromfile=str(old_path), tofile=str(path)))
diff_path = folder / 'CanonicalActualPrescribedReferenceGeometry.diff'
diff_path.write_text(diff)

def ident(p):
    p = Path(p)
    b = p.read_bytes()
    return {'path': str(p), 'sha256': hashlib.sha256(b).hexdigest(),
            'blob': hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest(),
            'lines': len(b.decode().splitlines())}

body_old = old.split(old_choice, 1)[1].replace(old_refine, new_refine)
body_new = new.split(' := by\n', 1)[1]
assert body_old == body_new
manifest = {
    'kind': 'actual_geometry_on_same_prescribed_reference_family',
    'status': 'CANDIDATE_HELD_UNCOMPILED_PENDING_INDEPENDENT_FULL_REVIEW',
    'owner': '/root', 'source': ident(path), 'exact_diff': ident(diff_path),
    'public_names': ['n04Coordinates_actual_reference_geometry_of_prescribed_family'],
    'original_reviewed_source': ident(old_path),
    'original_reviewed_manifest': ident(folder / 'CanonicalActualReferenceGeometryReviewedManifest.json'),
    'same_family_provider': ident(folder / 'CanonicalPositiveReferenceFamily.lean'),
    'constructive_family_provider': ident(root / 'n04-drafts/quantitative/primitive-route/reconstructed/ActualPositiveReferencePrescribedFamily.lean'),
    'constructive_family_peer': ident(root / 'n04-drafts/root/recovery/reviews/ActualPositiveReferencePrescribedFamilyIndependentReview.json'),
    'checks': [
        'The entire original geometry proof after its qualitative Y/H choice is byte-identical except for removing Y/H/hreference from the returned existential tuple.',
        'The input is exactly N04PositiveReferenceFamily for the actual typed atlas, original sources and order4. The supplied Y/H determine every occurrence of psi/chi/h0/V.',
        'Only actual relative transport controls and the common neighborhood are chosen. No reference family, material data, endpoint source or negative atlas is replaced.',
        'All seven original outputs, including genuine forward transmission and global relative transport, are retained for the same V.',
        'The original137 source and its independent review remain unchanged. This is a new reusable input-family adapter, not a claimed proof of the final target.'
    ],
    'scope_limits': ['The same-family reference numerical jets and current parameter towers remain separate obligations.',
                     'Static construction only, no compiler/CI/active/index/ref action.'],
    'compiled': False, 'created_at': datetime.now(timezone.utc).isoformat()
}
mf = folder / 'CanonicalActualPrescribedReferenceGeometryCandidateManifest.json'
mf.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'source': ident(path), 'manifest': ident(mf), 'proof_body_preserved': True}))
print(diff)
