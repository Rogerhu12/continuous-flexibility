import ContinuousFlexibility.Analysis.N01aOpticalSupport

/-!
# The signed variation of the actual interior control

The term containing the derivative of the optical radicand is the
derivative of the fixed step along that radicand. Its endpoint difference
is zero. The remaining integral is nonnegative and will be bounded below
using a quantitative interval around a maximum of the radicand.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

def n01aOpticalStepField (w : ℝ → ℝ) (δ r : ℝ) : ℝ :=
  n01aOpticalStep (n01aOpticalRadicand w r / δ)

def n01aOpticalKernel (w : ℝ → ℝ) (δ r : ℝ) : ℝ :=
  n01aOpticalCutoff (n01aOpticalRadicand w r / δ) /
    (r * Real.sqrt (n01aOpticalRadicand w r))

theorem contDiffAt_n01aOpticalStepField {w : ℝ → ℝ} (δ : ℝ)
    (hw : ContDiff ℝ ∞ w) {r : ℝ} (hr : r ≠ 0) (hwr : w r ≠ 0) :
    ContDiffAt ℝ ∞ (n01aOpticalStepField w δ) r :=
  contDiff_n01aOpticalStep.contDiffAt.comp r
    ((contDiffAt_n01aOpticalRadicand hw hr hwr).div_const δ)

theorem deriv_n01aOpticalStepField {w : ℝ → ℝ} (δ : ℝ)
    (hw : ContDiff ℝ ∞ w) {r : ℝ} (hr : r ≠ 0) (hwr : w r ≠ 0) :
    deriv (n01aOpticalStepField w δ) r =
      deriv n01aOpticalStep (n01aOpticalRadicand w r / δ) *
        (deriv (n01aOpticalRadicand w) r / δ) := by
  have hq := (contDiffAt_n01aOpticalRadicand hw hr hwr).differentiableAt (by simp)
  have hstep := (contDiff_n01aOpticalStep.differentiable (by simp)
    (n01aOpticalRadicand w r / δ)).hasDerivAt
  exact (hstep.comp r (hq.hasDerivAt.div_const δ)).deriv

theorem contDiffAt_n01aOpticalKernel {w : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hw : ContDiff ℝ ∞ w) {r : ℝ} (hr : r ≠ 0) (hwr : w r ≠ 0) :
    ContDiffAt ℝ ∞ (n01aOpticalKernel w δ) r := by
  have hq := contDiffAt_n01aOpticalRadicand hw hr hwr
  by_cases hqpos : 0 < n01aOpticalRadicand w r
  · exact (contDiff_n01aOpticalCutoff.contDiffAt.comp r (hq.div_const δ)).div
      (contDiffAt_id.mul (hq.sqrt hqpos.ne'))
      (mul_ne_zero hr (Real.sqrt_pos.mpr hqpos).ne')
  · have hsmall : ∀ᶠ x in 𝓝 r, n01aOpticalRadicand w x / δ < 1 :=
      (hq.continuousAt.div_const δ).eventually_lt continuousAt_const
        ((div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hqpos) hδ.le).trans_lt zero_lt_one)
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) r).congr_of_eventuallyEq
    filter_upwards [hsmall] with x hx
    simp only [n01aOpticalKernel, n01aOpticalCutoff_zero hx.le, zero_div]

theorem n01aOpticalKernel_nonneg {w : ℝ → ℝ} (δ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ n01aOpticalKernel w δ r :=
  div_nonneg (n01aOpticalCutoff_nonneg _)
    (mul_nonneg hr (Real.sqrt_nonneg _))

theorem deriv_n01aOpticalRawControl {w : ℝ → ℝ} {l h δ r : ℝ}
    (hw : ContDiff ℝ ∞ w) (hr : r ∈ Ioo l h) (hr0 : r ≠ 0) (hwr : w r ≠ 0) :
    deriv (n01aOpticalRawControl w l h δ) r =
      n01aOpticalCutoff (n01aOpticalRadicand w r / δ) +
        r * (Real.sqrt (n01aOpticalRadicand w r / δ) *
          deriv n01aOpticalStep (n01aOpticalRadicand w r / δ) *
            (deriv (n01aOpticalRadicand w) r / δ)) := by
  have hq := (contDiffAt_n01aOpticalRadicand hw hr0 hwr).differentiableAt (by simp)
  have hk := (hasDerivAt_n01aOpticalCutoff (n01aOpticalRadicand w r / δ)).comp r
    (hq.hasDerivAt.div_const δ)
  rw [(n01aOpticalRawControl_eventuallyEq hr).deriv_eq]
  simpa only [n01aOpticalCutoffDensity, one_mul] using ((hasDerivAt_id r).mul hk).deriv

private theorem n01a_optical_variation_algebra {r q δ : ℝ}
    (hr : 0 < r) (hq : 0 < q) (hδ : 0 < δ) (K D z : ℝ) :
    -(K + r * (Real.sqrt (q / δ) * D * (z / δ))) / (2 * r * Real.sqrt q) =
      -(1 / 2 : ℝ) * (K / (r * Real.sqrt q)) -
        (1 / (2 * Real.sqrt δ)) * (D * (z / δ)) := by
  rw [Real.sqrt_div hq.le δ]
  field_simp [hr.ne', hδ.ne', (Real.sqrt_pos.mpr hq).ne', (Real.sqrt_pos.mpr hδ).ne']
  <;> ring

theorem n01aOpticalRawControl_variation_pointwise {w : ℝ → ℝ} {l h δ r : ℝ}
    (hl : 0 < l) (hδ : 0 < δ) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ x ∈ Icc l h, 0 < w x) (hneg : ∀ x ∈ Ioo l h, deriv w x < 0)
    (hrootL : deriv w l = 0) (hrootR : deriv w h = 0) (hr : r ∈ Icc l h) :
    -deriv (n01aOpticalRawControl w l h δ) r / (2 * r * opticalSpeed w r) =
      -(1 / 2 : ℝ) * n01aOpticalKernel w δ r -
        (1 / (2 * Real.sqrt δ)) * deriv (n01aOpticalStepField w δ) r := by
  have hr0 : 0 < r := hl.trans_le hr.1
  by_cases hri : r ∈ Ioo l h
  · have hq : 0 < n01aOpticalRadicand w r :=
      n01aOpticalRadicand_pos hr0 (hpos r hr) (hneg r hri)
    rw [deriv_n01aOpticalRawControl hw hri hr0.ne' (hpos r hr).ne',
      deriv_n01aOpticalStepField δ hw hr0.ne' (hpos r hr).ne']
    exact n01a_optical_variation_algebra hr0 hq hδ _ _ _
  · have hqzero : n01aOpticalRadicand w r = 0 := by
      rcases eq_or_lt_of_le hr.1 with hrl | hlr
      · rw [← hrl]
        exact n01aOpticalRadicand_zero hrootL
      · have hrh : r = h := le_antisymm hr.2 (le_of_not_gt fun hh => hri ⟨hlr, hh⟩)
        rw [hrh]
        exact n01aOpticalRadicand_zero hrootR
    have hrawzero : deriv (n01aOpticalRawControl w l h δ) r = 0 :=
      (HasDerivAt.of_notMem_tsupport (notMem_tsupport_iff_eventuallyEq.mpr
        (n01aOpticalRawControl_eventually_zero hl hδ hw hpos hrootL hrootR hri))).deriv
    rw [hrawzero, deriv_n01aOpticalStepField δ hw hr0.ne' (hpos r hr).ne']
    simp only [n01aOpticalKernel, hqzero, zero_div,
      n01aOpticalCutoff_zero (by norm_num : (0 : ℝ) ≤ 1),
      deriv_n01aOpticalStep_zero_left (by norm_num : (0 : ℝ) ≤ 1),
      zero_mul, mul_zero, neg_zero, sub_zero]

theorem continuousOn_n01aOpticalKernel {w : ℝ → ℝ} {l h δ : ℝ}
    (hl : 0 < l) (hδ : 0 < δ) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Icc l h, 0 < w r) :
    ContinuousOn (n01aOpticalKernel w δ) (Icc l h) :=
  fun r hr => (contDiffAt_n01aOpticalKernel hδ hw (hl.trans_le hr.1).ne'
    (hpos r hr).ne').continuousAt.continuousWithinAt

theorem continuousOn_deriv_n01aOpticalStepField {w : ℝ → ℝ} {l h : ℝ}
    (δ : ℝ) (hl : 0 < l) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Icc l h, 0 < w r) :
    ContinuousOn (deriv (n01aOpticalStepField w δ)) (Icc l h) := by
  intro r hr
  have hs := contDiffAt_n01aOpticalStepField δ hw (hl.trans_le hr.1).ne' (hpos r hr).ne'
  exact ((hs.derivWithin (m := 0) (by simp)).continuousAt).continuousWithinAt

theorem integral_deriv_n01aOpticalStepField {w : ℝ → ℝ} {l h : ℝ}
    (δ : ℝ) (hl : 0 < l) (hlh : l < h) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Icc l h, 0 < w r)
    (hrootL : deriv w l = 0) (hrootR : deriv w h = 0) :
    (∫ r in l..h, deriv (n01aOpticalStepField w δ) r) = 0 := by
  have hd (r : ℝ) (hr : r ∈ uIcc l h) :
      HasDerivAt (n01aOpticalStepField w δ) (deriv (n01aOpticalStepField w δ) r) r := by
    rw [uIcc_of_le hlh.le] at hr
    exact ((contDiffAt_n01aOpticalStepField δ hw (hl.trans_le hr.1).ne'
      (hpos r hr).ne').differentiableAt (by simp)).hasDerivAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuousOn_deriv_n01aOpticalStepField δ hl hw hpos).intervalIntegrable_of_Icc hlh.le)]
  simp only [n01aOpticalStepField, n01aOpticalRadicand_zero hrootL,
    n01aOpticalRadicand_zero hrootR, zero_div, sub_self]

theorem n01aOpticalRawControl_variation_eq {w : ℝ → ℝ} {l h δ : ℝ}
    (hl : 0 < l) (hlh : l < h) (hδ : 0 < δ) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Icc l h, 0 < w r) (hneg : ∀ r ∈ Ioo l h, deriv w r < 0)
    (hrootL : deriv w l = 0) (hrootR : deriv w h = 0) :
    (∫ r in l..h, -deriv (n01aOpticalRawControl w l h δ) r /
      (2 * r * opticalSpeed w r)) =
      -(1 / 2 : ℝ) * ∫ r in l..h, n01aOpticalKernel w δ r := by
  have hk := (continuousOn_n01aOpticalKernel hl hδ hw hpos).intervalIntegrable_of_Icc hlh.le
  have hs := (continuousOn_deriv_n01aOpticalStepField δ hl hw hpos).intervalIntegrable_of_Icc hlh.le
  have he : EqOn
      (fun r => -deriv (n01aOpticalRawControl w l h δ) r / (2 * r * opticalSpeed w r))
      (fun r => -(1 / 2 : ℝ) * n01aOpticalKernel w δ r -
        (1 / (2 * Real.sqrt δ)) * deriv (n01aOpticalStepField w δ) r) (uIcc l h) := by
    intro r hr
    rw [uIcc_of_le hlh.le] at hr
    exact n01aOpticalRawControl_variation_pointwise hl hδ hw hpos hneg hrootL hrootR hr
  rw [intervalIntegral.integral_congr he,
    intervalIntegral.integral_sub (hk.const_mul _) (hs.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_deriv_n01aOpticalStepField δ hl hlh hw hpos hrootL hrootR, mul_zero, sub_zero]

/-- The exact first variation of the actual logarithmically perturbed
profile, with the signed integral that will be quantitatively normalized. -/
theorem hasDerivAt_n01aOpticalRawControl_travel {w : ℝ → ℝ} {l h δ : ℝ}
    (hl : 0 < l) (hlh : l < h) (hδ : 0 < δ) (hw : ContDiff ℝ ∞ w)
    (hpos : ∀ r ∈ Icc l h, 0 < w r) (hneg : ∀ r ∈ Ioo l h, deriv w r < 0)
    (hrootL : deriv w l = 0) (hrootR : deriv w h = 0) :
    HasDerivAt (fun t => opticalTravel
        (opticalLogPerturbation w (n01aOpticalRawControl w l h δ) t) l h)
      (-(1 / 2 : ℝ) * ∫ r in l..h, n01aOpticalKernel w δ r) 0 := by
  have hfirst := hasDerivAt_opticalTravel_of_compactInteriorSupport hl hlh hw
    (contDiff_n01aOpticalRawControl hl hδ hw hpos hrootL hrootR)
    (hasCompactSupport_n01aOpticalRawControl hl hδ hw hpos hrootL hrootR)
    hpos hneg (tsupport_n01aOpticalRawControl_subset hl hδ hw hpos hrootL hrootR)
  rwa [n01aOpticalRawControl_variation_eq hl hlh hδ hw hpos hneg hrootL hrootR] at hfirst

end ContinuousFlexibility.Statements
