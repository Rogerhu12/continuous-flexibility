import ContinuousFlexibility.Analysis.OpticalTravelSecondVariation

/-!
# Curvature of the actual compactly supported optical control

The log-profile perturbation has an affine radicand.  Outside the support
of the control the travel integrand is independent of the parameter, so
the full travel has the same second derivative as one compact interior
integral.  The resulting lower bound connects actual normalization with
an actual second-derivative bound and a control-derivative bound.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem sqrtAffine_integral_eq_interior_add_tails
    {q u : ℝ → ℝ} {l a b h : ℝ}
    (hla : l < a) (hab : a < b) (hbh : b < h)
    (hq : ContinuousOn q (Icc l h)) (hu : ContinuousOn u (Icc l h))
    (hu0 : ∀ r, r ∉ Ioo a b → u r = 0) :
    (fun t : ℝ => ∫ r in l..h, Real.sqrt (q r + t * u r)) =
      fun t => (∫ r in l..a, Real.sqrt (q r)) +
        (∫ r in a..b, Real.sqrt (q r + t * u r)) +
        (∫ r in b..h, Real.sqrt (q r)) := by
  funext t
  let F (r : ℝ) := Real.sqrt (q r + t * u r)
  have hFc : ContinuousOn F (Icc l h) :=
    Real.continuous_sqrt.comp_continuousOn (hq.add (continuousOn_const.mul hu))
  have hiL : IntervalIntegrable F volume l a :=
    (hFc.mono (fun r hr => ⟨hr.1, hr.2.trans (hab.trans hbh).le⟩)).intervalIntegrable_of_Icc hla.le
  have hiM : IntervalIntegrable F volume a b :=
    (hFc.mono (fun r hr => ⟨hla.le.trans hr.1, hr.2.trans hbh.le⟩)).intervalIntegrable_of_Icc hab.le
  have hiR : IntervalIntegrable F volume b h :=
    (hFc.mono (fun r hr => ⟨(hla.trans hab).le.trans hr.1, hr.2⟩)).intervalIntegrable_of_Icc hbh.le
  have hL : (∫ r in l..a, F r) = ∫ r in l..a, Real.sqrt (q r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hla.le] at hr
    have hr0 := hu0 r (fun hs => (not_lt_of_ge hr.2) hs.1)
    simp only [F, hr0, mul_zero, add_zero]
  have hR : (∫ r in b..h, F r) = ∫ r in b..h, Real.sqrt (q r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hbh.le] at hr
    have hr0 := hu0 r (fun hs => (not_lt_of_ge hr.1) hs.2)
    simp only [F, hr0, mul_zero, add_zero]
  change (∫ r in l..h, F r) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hiL.trans hiM) hiR,
    ← intervalIntegral.integral_add_adjacent_intervals hiL hiM, hL, hR]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory Analysis
open scoped Topology ContDiff

/-- The exact affine-radicand identity for the actual logarithmic
profile perturbation. -/
theorem opticalSpeed_logPerturbation_affine {w χ : ℝ → ℝ} {t r : ℝ}
    (hw : DifferentiableAt ℝ w r) (hχ : DifferentiableAt ℝ χ r)
    (hr : r ≠ 0) (hwr : w r ≠ 0) :
    opticalSpeed (opticalLogPerturbation w χ t) r =
      Real.sqrt (-deriv w r / (r * w r) + t * (-deriv χ r / r)) := by
  have hp := (hw.hasDerivAt.mul ((hχ.hasDerivAt.const_mul t).exp)).deriv
  change deriv (fun s => w s * Real.exp (t * χ s)) r = _ at hp
  unfold opticalSpeed
  change Real.sqrt (-deriv (fun s => w s * Real.exp (t * χ s)) r /
    (r * (w r * Real.exp (t * χ r)))) = _
  rw [hp]
  congr 1
  field_simp [hr, hwr, (Real.exp_pos (t * χ r)).ne']
  ring

/-- The positive integral whose negative is the actual second optical
travel variation. -/
def opticalControlCurvature (w χ : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ r in a..b, (-deriv χ r / r) ^ 2 / (4 * opticalSpeed w r ^ 3)

/-- First and second derivatives of the full, actual travel angle under
a compactly supported log-profile perturbation. -/
theorem hasDerivAt_opticalTravel_logPerturbation_twice
    {w χ : ℝ → ℝ} {l a b h : ℝ}
    (hl : 0 < l) (hla : l < a) (hab : a < b) (hbh : b < h)
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ)
    (hpos : ∀ r ∈ Icc l h, 0 < w r) (hneg : ∀ r ∈ Ioo l h, deriv w r < 0)
    (hsupp : tsupport χ ⊆ Ioo a b) :
    HasDerivAt (fun t : ℝ => opticalTravel (opticalLogPerturbation w χ t) l h)
      (∫ r in a..b, (-deriv χ r / r) / (2 * opticalSpeed w r)) 0 ∧
    HasDerivAt (deriv (fun t : ℝ => opticalTravel (opticalLogPerturbation w χ t) l h))
      (-opticalControlCurvature w χ a b) 0 := by
  let Q (r : ℝ) := -deriv w r / (r * w r)
  let B (r : ℝ) := -deriv χ r / r
  have hwd := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hχd := (contDiff_infty_iff_deriv.mp hχ).2.continuous
  have hQc : ContinuousOn Q (Icc l h) :=
    hwd.neg.continuousOn.div (continuous_id.mul hw.continuous).continuousOn
      (fun r hr => (mul_pos (hl.trans_le hr.1) (hpos r hr)).ne')
  have hBc : ContinuousOn B (Icc l h) :=
    hχd.neg.continuousOn.div continuous_id.continuousOn
      (fun r hr => (hl.trans_le hr.1).ne')
  have hsub : Icc a b ⊆ Icc l h :=
    fun r hr => ⟨hla.le.trans hr.1, hr.2.trans hbh.le⟩
  have hQpos (r : ℝ) (hr : r ∈ Icc a b) : 0 < Q r :=
    div_pos (neg_pos.mpr (hneg r ⟨hla.trans_le hr.1, hr.2.trans_lt hbh⟩))
      (mul_pos ((hl.trans hla).trans_le hr.1) (hpos r (hsub hr)))
  have hBzero (r : ℝ) (hr : r ∉ Ioo a b) : B r = 0 := by
    have ht : r ∉ tsupport χ := fun hs => hr (hsupp hs)
    simp only [B, deriv_of_notMem_tsupport ht, neg_zero, zero_div]
  have hFull : (fun t : ℝ => opticalTravel (opticalLogPerturbation w χ t) l h) =
      fun t => ∫ r in l..h, Real.sqrt (Q r + t * B r) := by
    funext t
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le (hla.trans (hab.trans hbh)).le] at hr
    exact opticalSpeed_logPerturbation_affine (hw.differentiable (by simp) r)
      (hχ.differentiable (by simp) r) (hl.trans_le hr.1).ne' (hpos r hr).ne'
  have hSplit := sqrtAffine_integral_eq_interior_add_tails hla hab hbh hQc hBc hBzero
  obtain ⟨hFirst, hSecond⟩ := hasDerivAt_sqrtAffine_integral_twice hab
    (hQc.mono hsub) (hBc.mono hsub) hQpos
  constructor
  · rw [hFull, hSplit]
    simpa only [Q, B, opticalSpeed] using
      (hFirst.const_add (∫ r in l..a, Real.sqrt (Q r))).add_const
        (∫ r in b..h, Real.sqrt (Q r))
  · rw [hFull, hSplit, deriv_add_const', deriv_const_add']
    simpa only [Q, B, opticalSpeed, opticalControlCurvature] using hSecond

/-- A unit normalized optical control cannot have both a tiny first
spatial derivative and a small second parameter derivative of the actual
travel.  The spatial collar is explicit and lies away from radius zero. -/
theorem normalized_opticalControl_curvature_bound
    {w χ : ℝ → ℝ} {l a b h B D : ℝ}
    (hl : 0 < l) (hla : l < a) (hab : a < b) (hbh : b < h)
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ)
    (hpos : ∀ r ∈ Icc l h, 0 < w r) (hneg : ∀ r ∈ Ioo l h, deriv w r < 0)
    (hsupp : tsupport χ ⊆ Ioo a b)
    (hunit : HasDerivAt (fun t : ℝ => opticalTravel (opticalLogPerturbation w χ t) l h) 1 0)
    (hB : ∀ r ∈ Icc a b, |deriv χ r| ≤ B)
    (hD : |deriv (deriv (fun t : ℝ => opticalTravel (opticalLogPerturbation w χ t) l h)) 0| ≤ D) :
    2 * a ≤ (b - a) ^ 2 * B * D := by
  let Q (r : ℝ) := -deriv w r / (r * w r)
  let U (r : ℝ) := -deriv χ r / r
  have ha : 0 < a := hl.trans hla
  have hsub : Icc a b ⊆ Icc l h :=
    fun r hr => ⟨hla.le.trans hr.1, hr.2.trans hbh.le⟩
  have hQc : ContinuousOn Q (Icc a b) :=
    ((contDiff_infty_iff_deriv.mp hw).2.continuous.neg.continuousOn).div
      (continuous_id.mul hw.continuous).continuousOn
      (fun r hr => (mul_pos (ha.trans_le hr.1) (hpos r (hsub hr))).ne')
  have hUc : ContinuousOn U (Icc a b) :=
    ((contDiff_infty_iff_deriv.mp hχ).2.continuous.neg.continuousOn).div
      continuous_id.continuousOn (fun r hr => (ha.trans_le hr.1).ne')
  have hQpos (r : ℝ) (hr : r ∈ Icc a b) : 0 < Q r :=
    div_pos (neg_pos.mpr (hneg r ⟨hla.trans_le hr.1, hr.2.trans_lt hbh⟩))
      (mul_pos (ha.trans_le hr.1) (hpos r (hsub hr)))
  have hBnonneg : 0 ≤ B := (abs_nonneg _).trans (hB a ⟨le_rfl, hab.le⟩)
  have hUB (r : ℝ) (hr : r ∈ Icc a b) : |U r| ≤ B / a := by
    dsimp only [U]
    rw [abs_div, abs_neg, abs_of_pos (ha.trans_le hr.1)]
    exact (div_le_div_of_nonneg_right (hB r hr) (ha.trans_le hr.1).le).trans
      (div_le_div_of_nonneg_left hBnonneg ha hr.1)
  obtain ⟨hFirst, hSecond⟩ := hasDerivAt_opticalTravel_logPerturbation_twice
    hl hla hab hbh hw hχ hpos hneg hsupp
  have hunitInt : (∫ r in a..b, U r / (2 * Real.sqrt (Q r))) = 1 := by
    exact hFirst.unique hunit
  have hcurv : (∫ r in a..b, U r ^ 2 / (4 * Real.sqrt (Q r) ^ 3)) ≤ D := by
    change opticalControlCurvature w χ a b ≤ D
    calc
      _ = -deriv (deriv (fun t : ℝ => opticalTravel (opticalLogPerturbation w χ t) l h)) 0 := by
        rw [hSecond.deriv, neg_neg]
      _ ≤ _ := (neg_le_abs _).trans hD
  have hbound := sqrtAffine_normalized_control_lower_bound hab hQc hUc hQpos hUB hunitInt hcurv
  calc
    2 * a = a * 2 := by ring
    _ ≤ a * ((b - a) ^ 2 * (B / a) * D) := mul_le_mul_of_nonneg_left hbound ha.le
    _ = _ := by field_simp [ha.ne'] <;> ring

end ContinuousFlexibility.Statements
