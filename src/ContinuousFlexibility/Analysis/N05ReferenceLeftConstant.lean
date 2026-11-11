import ContinuousFlexibility.Analysis.EndpointResistance
import ContinuousFlexibility.Radial.R11bInverseDensity
import ContinuousFlexibility.Radial.R11bAngularL2Bridge
import ContinuousFlexibility.Radial.R11bZeroMode

/-!
# The physical left constant is independent of the output exponent

A positive C¹ coefficient vanishing at either endpoint has nonintegrable
reciprocal. The left cutoff is one near the left endpoint, so its product
with the inverse square root of the coefficient is not in L². Subtracting
two attenuated output realizations therefore identifies their left constants,
even when their attenuation and coefficient exponents differ.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

/-- The same reciprocal-resistance argument applies to a zero at either
endpoint, without choosing an orientation for the interval. -/
theorem n05_not_integrableOn_inverse_of_zero {a b c : ℝ} (hab : a < b)
    (hc : c ∈ Icc a b) {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w)
    (hwpos : ∀ r ∈ Ioo a b, 0 < w r) (hwc : w c = 0) :
    ¬IntegrableOn (fun r => (w r)⁻¹) (Ioo a b) volume := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image
    (hw.continuous_deriv le_rfl).norm.continuousOn
  let K : ℝ := |M| + 1
  have hbound (r : ℝ) (hr : r ∈ Icc a b) : ‖deriv w r‖ ≤ K :=
    (hM ⟨r, hr, rfl⟩).trans (by dsimp [K]; linarith [le_abs_self M])
  have hlinear (r : ℝ) (hr : r ∈ Icc a b) : |w r| ≤ K * |r - c| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x (_ : x ∈ Icc a b) => hw.differentiable (by simp) x)
      hbound (convex_Icc a b) hc hr
    simpa only [hwc, sub_zero, Real.norm_eq_abs] using h
  intro hi
  have hmajor : IntegrableOn (fun r => K * (w r)⁻¹) (Ioo a b) volume :=
    hi.const_mul K
  have hsmall : IntegrableOn (fun r => (r - c)⁻¹) (Ioo a b) volume := by
    apply hmajor.mono' ((measurable_id.sub_const c).inv.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hwr : 0 < w r := hwpos r hr
    have hrc : r ≠ c := by
      intro hrc
      apply hwr.ne'
      simpa only [hrc] using hwc
    have hdist : 0 < |r - c| := abs_pos.mpr (sub_ne_zero.mpr hrc)
    have hwbnd : w r ≤ K * |r - c| := by
      simpa only [abs_of_pos hwr] using hlinear r ⟨hr.1.le, hr.2.le⟩
    change ‖(r - c)⁻¹‖ ≤ K * (w r)⁻¹
    rw [Real.norm_eq_abs, abs_inv, ← div_eq_mul_inv]
    apply (le_div_iff₀ hwr).mpr
    have hh : w r / |r - c| ≤ K := (div_le_iff₀ hdist).mpr hwbnd
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have hinterval : IntervalIntegrable (fun r => (r - c)⁻¹) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mpr hsmall
  rcases intervalIntegrable_sub_inv_iff.mp hinterval with heq | hnot
  · exact hab.ne heq
  · exact hnot (by simpa only [uIcc_of_le hab.le] using hc)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem n05_not_memLp_leftCutoff_inverse_sqrt {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D) :
    ¬MemLp (fun r => Real.sqrt ((D.w r)⁻¹) * D.chiLeft r) 2
      (volume.restrict (radialCore D)) := by
  intro hLp
  obtain ⟨ε, hε, hχ, _⟩ := hborder.2.2.2.2.2
  obtain ⟨x₀, hx₀l, hx₀r⟩ := exists_between
    (lt_min hgeom.2.1 (by linarith : D.a < D.a + ε))
  have hx₀b : x₀ < D.b := hx₀r.trans_le (min_le_left _ _)
  have hx₀ε : x₀ < D.a + ε := hx₀r.trans_le (min_le_right _ _)
  have hsub : Ioo D.a x₀ ⊆ radialCore D :=
    Ioo_subset_Ioo le_rfl hx₀b.le
  have hχtail (r : ℝ) (hr : r ∈ Ioo D.a x₀) : D.chiLeft r = 1 :=
    hχ r ⟨hr.1, hr.2.trans hx₀ε⟩
  have ht := MemLp.mono_measure (Measure.restrict_mono hsub le_rfl) hLp
  have hinv : IntegrableOn (fun r => (D.w r)⁻¹) (Ioo D.a x₀) volume := by
    apply ht.integrable_sq.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    change (Real.sqrt ((D.w r)⁻¹) * D.chiLeft r) ^ 2 = (D.w r)⁻¹
    rw [hχtail r hr, mul_one,
      Real.sq_sqrt (inv_nonneg.mpr (hgeom.2.2.2.2.1 r (hsub hr)).le)]
  exact n05_not_integrableOn_inverse_of_zero (c := D.a) hx₀l
    ⟨le_rfl, hx₀l.le⟩ (hgeom.2.2.1.1.of_le (by simp))
    (fun r hr => hgeom.2.2.2.2.1 r (hsub hr))
    (hgeom.2.2.1.2 D.a (Or.inl le_rfl)) hinv

/-- Positive attenuation determines the same physical left constant at all
coefficient and attenuation exponents. -/
theorem n05_outputRealization_leftConstant_unique {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ₁ γ₂ M₁ M₂ a b : ℝ} (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    {U : RadialUnknown} (ha : OutputRealization D γ₁ M₁ a U)
    (hb : OutputRealization D γ₂ M₂ b U) : a = b := by
  by_contra hab
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have haLp := r11b_outputRemainder_inverse_sqrt_memLp hD hγ₁ ha
  have hbLp := r11b_outputRemainder_inverse_sqrt_memLp hD hγ₂ hb
  have hscaled := (haLp.sub hbLp).const_mul ((b - a)⁻¹)
  have hχ : MemLp (fun p : PolarPoint =>
      Real.sqrt ((D.w p.1)⁻¹) * D.chiLeft p.1) 2 (radialPhysicalMeasure D) := by
    apply MemLp.ae_eq _ hscaled
    exact Eventually.of_forall fun p => by
      change (b - a)⁻¹ *
        (Real.sqrt ((D.w p.1)⁻¹) * outputRemainder D a U p -
          Real.sqrt ((D.w p.1)⁻¹) * outputRemainder D b U p) =
        Real.sqrt ((D.w p.1)⁻¹) * D.chiLeft p.1
      have hd : Real.sqrt ((D.w p.1)⁻¹) * outputRemainder D a U p -
          Real.sqrt ((D.w p.1)⁻¹) * outputRemainder D b U p =
          (b - a) * (Real.sqrt ((D.w p.1)⁻¹) * D.chiLeft p.1) := by
        dsimp only [outputRemainder]
        ring
      rw [hd, ← mul_assoc, inv_mul_cancel₀ hba, one_mul]
  apply n05_not_memLp_leftCutoff_inverse_sqrt hD.choose_spec.1 hborder
  simpa only [r11b_radialAngularMean_const] using
    (r11b_radialAngularMean_L2_bound hχ).1

end ContinuousFlexibility.Radial
