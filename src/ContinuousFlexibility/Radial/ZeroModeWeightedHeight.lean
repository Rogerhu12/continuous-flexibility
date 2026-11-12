import ContinuousFlexibility.Radial.ZeroModeWeightedFlux
import ContinuousFlexibility.Radial.ReferenceRadialCellBound

/-!
# Actual weighted zero-mode height bounds

On each side of the midpoint, the height is normalized at that side's
endpoint. The weighted flux estimate controls its actual integral.
The true partition then turns the cellwise bounds into weighted L2
membership and one uniform energy estimate, including the left height.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real Filter MeasureTheory
open scoped ENNReal
open ContinuousFlexibility.Statements

theorem zeroMode_integral_sq_le_of_pointwise
    {a b A : ℝ} (hab : a ≤ b) (hA : 0 ≤ A) {q : ℝ → ℝ}
    (hq : ∀ s ∈ Ioo a b, (q s) ^ 2 ≤ A) :
    (∫ s in a..b, q s) ^ 2 ≤ (b - a) ^ 2 * A := by
  have hb : ‖∫ s in a..b, q s‖ ≤ sqrt A * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
    filter_upwards [Measure.ae_ne volume b] with s hne hs
    rw [uIoc_of_le hab] at hs
    have hsi : s ∈ Ioo a b := ⟨hs.1, lt_of_le_of_ne hs.2 hne⟩
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
    rw [sq_abs, sq_sqrt hA]
    exact hq s hsi
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) (abs_nonneg _))).mpr hb
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow, sq_sqrt hA, mul_comm] using hsq

theorem zeroModeHeight_sub_left_of_integrable
    {a b r : ℝ} {w f : ℝ → ℝ}
    (hq : IntervalIntegrable (fun s => zeroModeFlux a f s / w s) volume a b)
    (hr : r ∈ Icc a b) :
    zeroModeHeight a b w f r - zeroModeHeight a b w f a =
      ∫ s in a..r, zeroModeFlux a f s / w s := by
  have har : IntervalIntegrable (fun s => zeroModeFlux a f s / w s) volume a r :=
    hq.mono_set (by
      rw [uIcc_of_le hr.1, uIcc_of_le (hr.1.trans hr.2)]
      exact Icc_subset_Icc le_rfl hr.2)
  have hsum := intervalIntegral.integral_add_adjacent_intervals hq.symm har
  rw [zeroModeHeight_eq_integral, zeroModeHeight_eq_integral]
  linarith only [hsum]

/-- The integral field normalized separately at the two endpoints belongs
to the actual output measure. The same estimate retains its actual left
endpoint value for the subsequent true-cutoff correction. -/
theorem zeroMode_weighted_endpoint_height
    {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C) :
    ∃ Mstar K : ℝ, 0 < Mstar ∧ 0 < K ∧
      ∀ M₀ M₁ γ : ℝ, Mstar ≤ M₀ → 0 ≤ M₁ → γ ∈ Icc (0 : ℝ) 1 →
      ∀ f : ℝ → ℝ,
      MemLp f 2 (referenceRadialWeightedMeasure D γ M₀) →
      IntervalIntegrable f volume D.a D.b → (∫ t in D.a..D.b, f t) = 0 →
      IntervalIntegrable (fun s => zeroModeFlux D.a f s / D.w s) volume D.a D.b ∧
      MemLp (fun r => zeroModeHeight D.a D.b D.w f r -
        zeroModeHeight D.a D.b D.w f D.a *
          (if r ≤ (D.a + D.b) / 2 then 1 else 0)) 2
        (referenceRadialWeightedMeasure D γ (-M₁)) ∧
      (zeroModeHeight D.a D.b D.w f D.a) ^ 2 +
        (∫ r, (zeroModeHeight D.a D.b D.w f r -
          zeroModeHeight D.a D.b D.w f D.a *
            (if r ≤ (D.a + D.b) / 2 then 1 else 0)) ^ 2
          ∂referenceRadialWeightedMeasure D γ (-M₁)) ≤
      K * ∫ t, f t ^ 2 ∂referenceRadialWeightedMeasure D γ M₀ := by
  obtain ⟨Mf, Af, hMf, hAf, hflux⟩ := zeroMode_weighted_sameSide_flux_bound hD
  obtain ⟨Mq, Aq, hMq, hAq, hquot⟩ := zeroMode_quotient_integrable_of_weighted_source hD
  have hab : D.a < D.b := hD.1.2.1
  let L : ℝ := D.b - D.a
  have hL : 0 < L := sub_pos.mpr hab
  refine ⟨max Mf Mq, L ^ 2 * Aq + L ^ 3 * Af,
    lt_of_lt_of_le hMf (le_max_left _ _), by positivity, ?_⟩
  intro M₀ M₁ γ hM₀ hM₁ hγ f hf hfi hmean
  have hMf₀ : Mf ≤ M₀ := (le_max_left _ _).trans hM₀
  have hMq₀ : Mq ≤ M₀ := (le_max_right _ _).trans hM₀
  obtain ⟨hqi, hqb, haL⟩ := hquot M₀ γ hMq₀ hγ f hf hfi hmean
  let U : ℝ → ℝ := zeroModeHeight D.a D.b D.w f
  let q : ℝ → ℝ := fun s => zeroModeFlux D.a f s / D.w s
  let H : ℝ → ℝ := fun r => U r - U D.a * (if r ≤ (D.a + D.b) / 2 then 1 else 0)
  let E : ℝ := ∫ t, f t ^ 2 ∂referenceRadialWeightedMeasure D γ M₀
  have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  have hpoint (k : ℕ) (r : ℝ) (hr : r ∈ D.cells k) :
      exp (2 * (-M₁) * radialQ (D.cellIndex k) + 2 * γ * radialS (D.cellIndex k)) *
        (H r) ^ 2 ≤ (L ^ 2 * Af) * E := by
    have hrCore : r ∈ radialCore D := hD.2.1.2.2.2.1 k hr
    let W : ℝ := exp (-M₁ * radialQ (D.cellIndex k) + γ * radialS (D.cellIndex k))
    have hWsq : W ^ 2 =
        exp (2 * (-M₁) * radialQ (D.cellIndex k) + 2 * γ * radialS (D.cellIndex k)) := by
      dsimp only [W]
      rw [pow_two, ← exp_add]
      congr 1 <;> ring
    rw [← hWsq, ← mul_pow]
    by_cases hleft : r ≤ (D.a + D.b) / 2
    · have hb : (∫ s in D.a..r, W * q s) ^ 2 ≤ (r - D.a) ^ 2 * (Af * E) :=
        zeroMode_integral_sq_le_of_pointwise hrCore.1.le (mul_nonneg hAf.le hE) (by
          intro s hs
          exact hflux M₀ M₁ γ hMf₀ hM₁ hγ f hf hfi hmean k r s hr
            ⟨hs.1, hs.2.trans hrCore.2⟩ (Or.inl ⟨hleft, hs.2.le⟩))
      have hwidth : (r - D.a) ^ 2 ≤ L ^ 2 :=
        (sq_le_sq₀ (sub_nonneg.mpr hrCore.1.le) hL.le).mpr
          (sub_le_sub_right hrCore.2.le D.a)
      have hH : W * H r = ∫ s in D.a..r, W * q s := by
        dsimp only [H]
        rw [if_pos hleft, mul_one]
        rw [zeroModeHeight_sub_left_of_integrable hqi ⟨hrCore.1.le, hrCore.2.le⟩]
        exact (intervalIntegral.integral_const_mul W q).symm
      rw [hH]
      exact hb.trans (by
        calc
          (r - D.a) ^ 2 * (Af * E) ≤ L ^ 2 * (Af * E) :=
            mul_le_mul_of_nonneg_right hwidth (mul_nonneg hAf.le hE)
          _ = (L ^ 2 * Af) * E := by ring)
    · have hright : (D.a + D.b) / 2 ≤ r := (lt_of_not_ge hleft).le
      have hb : (∫ s in r..D.b, W * q s) ^ 2 ≤ (D.b - r) ^ 2 * (Af * E) :=
        zeroMode_integral_sq_le_of_pointwise hrCore.2.le (mul_nonneg hAf.le hE) (by
          intro s hs
          exact hflux M₀ M₁ γ hMf₀ hM₁ hγ f hf hfi hmean k r s hr
            ⟨hrCore.1.trans hs.1, hs.2⟩ (Or.inr ⟨hright, hs.1.le⟩))
      have hwidth : (D.b - r) ^ 2 ≤ L ^ 2 :=
        (sq_le_sq₀ (sub_nonneg.mpr hrCore.2.le) hL.le).mpr
          (sub_le_sub_left hrCore.1.le D.b)
      have hH : (W * H r) ^ 2 = (∫ s in r..D.b, W * q s) ^ 2 := by
        dsimp only [H]
        rw [if_neg hleft, mul_zero, sub_zero]
        dsimp only [U, zeroModeHeight]
        rw [intervalIntegral.integral_const_mul]
        dsimp only [q]
        ring
      rw [hH]
      exact hb.trans (by
        calc
          (D.b - r) ^ 2 * (Af * E) ≤ L ^ 2 * (Af * E) :=
            mul_le_mul_of_nonneg_right hwidth (mul_nonneg hAf.le hE)
          _ = (L ^ 2 * Af) * E := by ring)
  have hUcont : ContinuousOn U (radialCore D) :=
    (zeroModeHeight_continuousOn_of_integrable hqi).mono
      (Ioo_subset_Icc_self.trans Icc_subset_uIcc)
  have hstep : Measurable (fun r : ℝ => if r ≤ (D.a + D.b) / 2 then (1 : ℝ) else 0) := by
    change Measurable ((Iic ((D.a + D.b) / 2)).indicator (fun _ : ℝ => (1 : ℝ)))
    exact measurable_const.indicator measurableSet_Iic
  have hHm : AEStronglyMeasurable H (volume.restrict (radialCore D)) :=
    (hUcont.aestronglyMeasurable measurableSet_Ioo).sub
      (aestronglyMeasurable_const.mul hstep.aestronglyMeasurable)
  obtain ⟨hHmem, hHbound⟩ := referenceRadial_memLp_of_cellwise_sq_bound hab hD.2.1
    (mul_nonneg (mul_nonneg (sq_nonneg L) hAf.le) hE) hHm hpoint
  refine ⟨hqi, hHmem, ?_⟩
  have ha : (U D.a) ^ 2 ≤ (L ^ 2 * Aq) * E := haL
  change (U D.a) ^ 2 +
    (∫ r, (H r) ^ 2 ∂referenceRadialWeightedMeasure D γ (-M₁)) ≤
      (L ^ 2 * Aq + L ^ 3 * Af) * E
  dsimp only [L] at ha hHbound ⊢
  nlinarith only [ha, hHbound]

end ContinuousFlexibility.Radial
