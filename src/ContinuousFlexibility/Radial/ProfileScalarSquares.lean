import ContinuousFlexibility.Analysis.IntervalFluxEnergy
import ContinuousFlexibility.Radial.ProfileLayerGeometry
import ContinuousFlexibility.Radial.ProfilePartitionBounds
import ContinuousFlexibility.Radial.R11bWeightedSquareDensity

/-!
# Scalar profile squares and localized first derivatives

A fixed cell lies away from both endpoints by the actual profile distance
bound. Consequently a continuous derivative on the open core becomes an
actual L2 function after multiplication by its localizer. These are
membership proofs for the original representatives.
-/

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

namespace ContinuousFlexibility.Analysis

theorem memLp_mul_test_of_continuousOn_Ioo {a b : ℝ} {d χ : ℝ → ℝ}
    (hd : ContinuousOn d (Ioo a b)) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ioo a b) :
    MemLp (fun x => χ x * d x) 2 (volume.restrict (Ioo a b)) := by
  have hm : AEStronglyMeasurable (fun x => χ x * d x)
      (volume.restrict (Ioo a b)) :=
    (hχ.continuousOn.mul hd).aestronglyMeasurable measurableSet_Ioo
  have hcont : ContinuousOn (fun x => χ x * d x ^ 2) (Ioo a b) :=
    hχ.continuousOn.mul (hd.pow 2)
  have hi := integrable_mul_test_of_locallyIntegrableOn_Ioo
    (hcont.locallyIntegrableOn (μ := volume) measurableSet_Ioo) hχ hχc hχs
  have hsq : Integrable (fun x => (χ x * d x) ^ 2) volume :=
    hi.congr (Eventually.of_forall fun x => by ring)
  exact (memLp_two_iff_integrable_sq hm).mpr hsq.integrableOn

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Radial

noncomputable section

def profileScalarCellSquare (D : ReferenceData) (f : ℝ → ℝ) (m : ℕ) : ℝ :=
  ∫ r in radialCore D, (D.localizer m r * f r) ^ 2

theorem profileScalarCellSquare_nonneg (D : ReferenceData) (f : ℝ → ℝ) (m : ℕ) :
    0 ≤ profileScalarCellSquare D f m :=
  integral_nonneg (fun r => sq_nonneg _)

theorem profile_memLp_localizer_mul {D : ReferenceData} (h : RadialPartition D)
    {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (radialCore D))) (m : ℕ) :
    MemLp (fun r => D.localizer m r * f r) 2 (volume.restrict (radialCore D)) := by
  apply hf.mono ((h.1 m).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  apply Eventually.of_forall
  intro r
  change ‖D.localizer m r * f r‖ ≤ ‖f r‖
  rw [norm_mul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (profile_localizer_abs_le_one h m r)
    (norm_nonneg (f r))).trans_eq (one_mul _)

theorem profile_localizer_tsupport_subset_layer {D : ReferenceData} {C : ℕ → ℝ}
    (h : AccumulatingProfileBounds D C) (m : ℕ) :
    tsupport (D.localizer m) ⊆ profileEndpointLayer D (C 0) (D.cellIndex m) := by
  have hs : Function.support (D.localizer m) ⊆
      tsupport (profileLayerCutoff D (C 0) (D.cellIndex m)) := by
    intro r hr
    apply subset_closure
    change profileLayerCutoff D (C 0) (D.cellIndex m) r ≠ 0
    rw [profileLayerCutoff_one_on_cell h (h.2.1.2.2.1 m hr)]
    exact one_ne_zero
  exact (closure_minimal hs (isClosed_tsupport _)).trans
    (tsupport_profileLayerCutoff_subset (h.2.2.1 0) _)

theorem profile_localizer_hasCompactSupport {D : ReferenceData} {C : ℕ → ℝ}
    (h : AccumulatingProfileBounds D C) (m : ℕ) :
    HasCompactSupport (D.localizer m) := by
  have hs : tsupport (D.localizer m) ⊆ radialCore D :=
    (profile_localizer_tsupport_subset_layer h m).trans
      (profileEndpointLayer_subset_core (h.2.2.1 0) _)
  exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
    (fun r hr => ⟨(hs hr).1.le, (hs hr).2.le⟩)

theorem profile_memLp_localizer_deriv {D : ReferenceData} {C : ℕ → ℝ}
    (h : AccumulatingProfileBounds D C) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (radialCore D)) (m : ℕ) :
    MemLp (fun r => D.localizer m r * deriv u r) 2
      (volume.restrict (radialCore D)) :=
  memLp_mul_test_of_continuousOn_Ioo
    (continuousOn_deriv_of_contDiffOn_one_Ioo hu) (h.2.1.1 m).continuous
    (profile_localizer_hasCompactSupport h m)
    ((profile_localizer_tsupport_subset_layer h m).trans
      (profileEndpointLayer_subset_core (h.2.2.1 0) _))

theorem profile_memLp_layerCutoff_deriv {D : ReferenceData} {C : ℝ}
    (hC : 0 < C) {u : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u (radialCore D)) (n : ℕ) :
    MemLp (fun r => profileLayerCutoff D C n r * deriv u r) 2
      (volume.restrict (radialCore D)) :=
  memLp_mul_test_of_continuousOn_Ioo
    (continuousOn_deriv_of_contDiffOn_one_Ioo hu)
    (contDiff_intervalLayerCutoff _ _ _ _).continuous
    (hasCompactSupport_intervalLayerCutoff
      (profileLayerLower_pos hC n) (profileLayerUpper_pos hC n))
    ((tsupport_profileLayerCutoff_subset hC n).trans
      (profileEndpointLayer_subset_core hC n))

end

end ContinuousFlexibility.Radial
