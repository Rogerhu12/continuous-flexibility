module

public import ContinuousFlexibility.Radial.MatchedModeDomainEmbedding
public import ContinuousFlexibility.Radial.ModeCoreSource
public import ContinuousFlexibility.Radial.ReferenceWeakAlgebra

/-!
# The actual bordered row is linear on the weighted output domain

The row products are genuinely integrable: the positive attenuation
places the second coefficient in the modal Hilbert space, where the true
normalized border is an L² test. Angular additivity uses the actual
local L² sections. No rule for adding undefined integrals is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal

theorem cosineMode_memLp_angular (j : ℕ) :
    MemLp (Radial.cosineMode j) 2
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
  have hc : Continuous (Radial.cosineMode j) := by
    unfold Radial.cosineMode
    fun_prop
  apply MemLp.of_bound hc.aestronglyMeasurable (Real.sqrt 2)
  filter_upwards with θ
  change ‖Real.sqrt 2 * Real.cos ((j : ℝ) * θ)‖ ≤ Real.sqrt 2
  rw [norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg 2), Real.norm_eq_abs]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_cos_le_one ((j : ℝ) * θ)) (Real.sqrt_nonneg 2)

theorem referenceMode_add_ae {D : ReferenceData} (hP : RadialPartition D)
    {f g : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hg : RadialCellIntegrable D g) (j : ℕ) :
    referenceMode (fun x => f x + g x) j =ᵐ[volume.restrict (radialCore D)]
      (fun r => referenceMode f j r + referenceMode g j r) := by
  filter_upwards [hf.ae_angular_memLp hP, hg.ae_angular_memLp hP] with r hfr hgr
  have hc := cosineMode_memLp_angular j
  have hfi : IntervalIntegrable (fun θ => f (r, θ) * Radial.cosineMode j θ)
      volume 0 (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).mpr (hfr.integrable_mul hc)
  have hgi : IntervalIntegrable (fun θ => g (r, θ) * Radial.cosineMode j θ)
      volume 0 (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).mpr (hgr.integrable_mul hc)
  simp only [referenceMode, radialAngularMean, add_mul]
  rw [intervalIntegral.integral_add hfi hgi]
  ring

theorem referenceMode_const_mul (f : PolarPoint → ℝ) (c : ℝ) (j : ℕ) (r : ℝ) :
    referenceMode (fun x => c * f x) j r = c * referenceMode f j r := by
  simp only [referenceMode, mul_assoc, radialAngularMean_const_mul]

theorem referenceRow_const_mul (D : ReferenceData) (f : PolarPoint → ℝ) (c : ℝ) :
    referenceRow D (fun x => c * f x) = c * referenceRow D f := by
  unfold referenceRow
  simp only [referenceMode_const_mul]
  have he : (fun r => referenceColumn D r * (c * referenceMode f 2 r)) =
      (fun r => c * (referenceColumn D r * referenceMode f 2 r)) := by
    funext r
    ring
  rw [he, intervalIntegral.integral_const_mul]

theorem OutputMember.row_intervalIntegrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M : ℝ} (hγ : 0 < γ) {U : RadialUnknown}
    (hU : OutputMember D γ M U) :
    IntervalIntegrable (fun r => referenceColumn D r * referenceMode U.1 2 r)
      volume D.a D.b := by
  have hm : MemLp (referenceMode U.1 2) 2 (radialHilbertMeasure D) := by
    simpa only [Nat.zero_add, Nat.mul_one] using
      hU.referenceMode_even_memLp_hilbert hD hB hγ 0
  have hi := Radial.matchingColumn_mode_intervalIntegrable hD hB
    (hm.toLp (referenceMode U.1 2))
  apply hi.congr_ae
  rw [uIoc_of_le (Radial.matchingProfileGeometry hD).2.1.le,
    ← restrict_Ioo_eq_restrict_Ioc]
  apply (Radial.radialHilbertMeasure_ae_iff hD).mp
  filter_upwards [hm.coeFn_toLp] with r hr
  exact congrArg (fun t => referenceColumn D r * t) hr

theorem referenceRow_add {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M : ℝ} (hγ : 0 < γ) {U V : RadialUnknown}
    (hU : OutputMember D γ M U) (hV : OutputMember D γ M V) :
    referenceRow D (fun x => U.1 x + V.1 x) =
      referenceRow D U.1 + referenceRow D V.1 := by
  have he :
      (fun r => referenceColumn D r * referenceMode (fun x => U.1 x + V.1 x) 2 r)
        =ᵐ[volume.restrict (uIoc D.a D.b)]
      (fun r => referenceColumn D r * referenceMode U.1 2 r +
        referenceColumn D r * referenceMode V.1 2 r) := by
    rw [uIoc_of_le (Radial.matchingProfileGeometry hD).2.1.le,
      ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [referenceMode_add_ae hD.choose_spec.2.1
      (hU.radialCellIntegrable hD hB) (hV.radialCellIntegrable hD hB) 2] with r hr
    change referenceColumn D r * referenceMode (fun x => U.1 x + V.1 x) 2 r =
      referenceColumn D r * referenceMode U.1 2 r +
        referenceColumn D r * referenceMode V.1 2 r
    rw [hr, mul_add]
  unfold referenceRow
  rw [intervalIntegral.integral_congr_ae_restrict he,
    intervalIntegral.integral_add
      (hU.row_intervalIntegrable hD hB hγ) (hV.row_intervalIntegrable hD hB hγ)]

end ContinuousFlexibility.Statements
