module

public import ContinuousFlexibility.Analysis.N07aGeometryJetBounds
public import ContinuousFlexibility.Analysis.N07aSampleEnvelopes
public import ContinuousFlexibility.Analysis.N07aCurrentPrincipalBounds

/-!
# Actual interval lengths as sampled subpower envelopes

These bounds come from the reference raw geometric jets. In particular
no lower bound E0 ≥ 1 or independent interval-size hypothesis is added.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

theorem n07a_referenceAtom_center_subpower
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K) (a : CanonicalGeometry.Atom) :
    N07aSampleSubpower T K
      (fun m => CanonicalGeometry.atom D T S C L K (C.referenceState, 0) m a (1 / 2, 0)) := by
  let B : ℝ := (href.2 0).choose
  have hB : 0 < B := (href.2 0).choose_spec.1
  have hb := (href.2 0).choose_spec.2
  have he := N07aSampleSubpower.mul hD hT
    (N07aSampleSubpower.const hD hT (K := K) B)
    (N07aSampleSubpower.e0_rpow hD hT (K := K) B)
  apply he.mono
  intro m
  have hp : ((1 / 2, 0) : ℝ × ℝ) ∈ CanonicalGeometry.unitStrip := by
    constructor <;> norm_num
  have h := hb m a (1 / 2, 0) hp 0 0 (by omega)
  rw [spaces_mixedDerivative_zero] at h
  have hE := (hT.2.1 _
    (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))).2.2.1
  simpa only [abs_of_pos (mul_pos hB (Real.rpow_pos_of_pos hE B))] using h

theorem n07a_canonicalLength_subpower
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K) :
    N07aSampleSubpower T K (fun m => K.right m - K.left m) := by
  simpa only [CanonicalGeometry.atom] using
    n07a_referenceAtom_center_subpower hD hT href .canonicalLength

theorem n07a_canonicalLengthInverse_subpower
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K) :
    N07aSampleSubpower T K (fun m => (K.right m - K.left m)⁻¹) := by
  simpa only [CanonicalGeometry.atom] using
    n07a_referenceAtom_center_subpower hD hT href .canonicalLengthInverse

theorem n07a_physicalLength_subpower
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K) :
    N07aSampleSubpower T K (fun m => K.physicalRight m - K.physicalLeft m) := by
  simpa only [CanonicalGeometry.atom] using
    n07a_referenceAtom_center_subpower hD hT href .physicalLength

theorem n07a_physicalLengthInverse_subpower
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K) :
    N07aSampleSubpower T K (fun m => (K.physicalRight m - K.physicalLeft m)⁻¹) := by
  simpa only [CanonicalGeometry.atom] using
    n07a_referenceAtom_center_subpower hD hT href .physicalLengthInverse

theorem n07aCanonicalUnit_jet_inverse (m : ℕ) (hm : K.left m < K.right m)
    (f : PolarPoint → ℝ) (a b : ℕ) (y : PolarPoint) :
    mixedDerivative a b f y = (K.right m - K.left m)⁻¹ ^ a *
      mixedDerivative a b (f ∘ CanonicalGeometry.canonicalUnitPoint K m)
        (n07aCanonicalUnitInversePoint K m y) := by
  have hL : K.right m - K.left m ≠ 0 := (sub_pos.mpr hm).ne'
  let p := n07aCanonicalUnitInversePoint K m y
  have he := n07a_mixedDerivative_radialAffine f (K.left m)
    (K.right m - K.left m) a b p
  change mixedDerivative a b (f ∘ CanonicalGeometry.canonicalUnitPoint K m) p =
    (K.right m - K.left m) ^ a *
      mixedDerivative a b f (CanonicalGeometry.canonicalUnitPoint K m p) at he
  rw [n07aCanonicalUnitPoint_inverse hm y] at he
  calc
    _ = (K.right m - K.left m)⁻¹ ^ a *
        ((K.right m - K.left m) ^ a * mixedDerivative a b f y) := by
      rw [← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hL), one_mul]
    _ = _ := by rw [← he]

end ContinuousFlexibility.Analysis
