import ContinuousFlexibility.Radial.MatchedTailTestDensity

/-!
# From the actual tail kernel to an all-source localized operator bound

A bounded kernel block controls each weighted L² row by Cauchy--Schwarz.
Multiplication by the output localizer then gives the norm of the localized
operator. Compact smooth tests are dense in the actual tail space, so the
bound holds for every input to the existing continuous inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
open ContinuousFlexibility.Statements

/-- A bounded row on the support of an actual L² localizer defines a
bounded pairing against every actual L² source. -/
theorem matchedTail_kernel_row_pairing_bound {μ : Measure ℝ}
    {κ ψ : ℝ → ℝ} (hκ : Measurable κ) (hψ : MemLp ψ 2 μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y, ψ y ≠ 0 → |κ y| ≤ C)
    (f : Lp ℝ 2 μ) :
    |∫ y, κ y * ψ y * f y ∂μ| ≤ C * ‖hψ.toLp ψ‖ * ‖f‖ := by
  have hpoint (y : ℝ) : ‖κ y * ψ y‖ ≤ ‖C * ψ y‖ := by
    by_cases hy : ψ y = 0
    · simp only [hy, mul_zero, norm_zero, le_refl]
    · simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC] using
        mul_le_mul_of_nonneg_right (hbound y hy) (abs_nonneg (ψ y))
  have hr : MemLp (fun y => κ y * ψ y) 2 μ :=
    (hψ.const_mul C).of_le (hκ.aestronglyMeasurable.mul hψ.aestronglyMeasurable)
      (Eventually.of_forall hpoint)
  have hnorm : ‖hr.toLp (fun y => κ y * ψ y)‖ ≤ C * ‖hψ.toLp ψ‖ := by
    calc
      _ ≤ ‖C • hψ.toLp ψ‖ := by
        apply Lp.norm_le_norm_of_ae_le
        filter_upwards [MemLp.coeFn_toLp hr, MemLp.coeFn_toLp hψ,
          Lp.coeFn_smul C (hψ.toLp ψ)] with y hry hψy hCy
        rw [hry, hCy]
        simpa only [Pi.smul_apply, smul_eq_mul, hψy] using hpoint y
      _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
  have hinner : ⟪hr.toLp (fun y => κ y * ψ y), f⟫_ℝ =
      ∫ y, κ y * ψ y * f y ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hr] with y hy
    simp only [hy, Real.inner_apply]
  calc
    _ = ‖⟪hr.toLp (fun y => κ y * ψ y), f⟫_ℝ‖ := by
      rw [hinner, Real.norm_eq_abs]
    _ ≤ ‖hr.toLp (fun y => κ y * ψ y)‖ * ‖f‖ := norm_inner_le_norm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg f)

/-- The L² norm of a genuine integral representative is controlled by
the two actual localizer norms. The measure need not have finite mass. -/
theorem matchedTail_kernel_output_norm_le {μ : Measure ℝ}
    (u f : Lp ℝ 2 μ) (κ : ℝ → ℝ → ℝ)
    (hκ : Measurable (fun z : ℝ × ℝ => κ z.1 z.2))
    {χ ψ : ℝ → ℝ} (hχ : MemLp χ 2 μ) (hψ : MemLp ψ 2 μ)
    (hu : (u : ℝ → ℝ) =ᵐ[μ]
      fun x => χ x * ∫ y, κ x y * ψ y * f y ∂μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, χ x ≠ 0 → ∀ y, ψ y ≠ 0 → |κ x y| ≤ C) :
    ‖u‖ ≤ (C * ‖hχ.toLp χ‖ * ‖hψ.toLp ψ‖) * ‖f‖ := by
  let B : ℝ := C * ‖hψ.toLp ψ‖ * ‖f‖
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hnorm : ‖u‖ ≤ ‖B • hχ.toLp χ‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hu, MemLp.coeFn_toLp hχ,
      Lp.coeFn_smul B (hχ.toLp χ)] with x hux hχx hBx
    rw [hux, hBx]
    simp only [Pi.smul_apply, smul_eq_mul, hχx]
    by_cases hx : χ x = 0
    · simp only [hx, zero_mul, mul_zero, norm_zero, le_refl]
    · have hrow : Measurable (κ x) :=
        hκ.comp (measurable_const.prodMk measurable_id)
      have hrowBound := matchedTail_kernel_row_pairing_bound hrow hψ hC (hbound x hx) f
      have hb : |χ x| * |∫ y, κ x y * ψ y * f y ∂μ| ≤
          B * |χ x| :=
        (mul_le_mul_of_nonneg_left hrowBound (abs_nonneg (χ x))).trans_eq (mul_comm _ _)
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hB] using hb
  exact hnorm.trans_eq (by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hB]
    dsimp only [B]
    ring)

/-- A bound for one actual kernel block bounds the localized actual
operator on its entire Hilbert domain. The multiplier identities are
almost-everywhere identities of the supplied maps, not surrogate norms. -/
theorem matchedTail_localized_opNorm_le_kernel
    {T : DeepTailData}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (G P Q : DeepTailL2 T →L[ℝ] DeepTailL2 T)
    (κ : ℝ → ℝ → ℝ)
    (hκ : Measurable (fun z : ℝ × ℝ => κ z.1 z.2))
    (hG : ∀ (f : DeepTailL2 T) (φ : ℝ → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo T.entrance T.endpoint →
      (f : ℝ → ℝ) =ᵐ[deepTailMeasure T] φ →
      (G f : ℝ → ℝ) =ᵐ[deepTailMeasure T]
        fun x => ∫ y, κ x y * φ y ∂deepTailMeasure T)
    {χ ψ : ℝ → ℝ}
    (hχ : MemLp χ 2 (deepTailMeasure T))
    (hψ : MemLp ψ 2 (deepTailMeasure T))
    (hψsmooth : ContDiff ℝ ∞ ψ)
    (hP : ∀ f, (P f : ℝ → ℝ) =ᵐ[deepTailMeasure T] fun x => χ x * f x)
    (hQ : ∀ f, (Q f : ℝ → ℝ) =ᵐ[deepTailMeasure T] fun x => ψ x * f x)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, χ x ≠ 0 → ∀ y, ψ y ≠ 0 → |κ x y| ≤ C) :
    ‖P ∘L G ∘L Q‖ ≤ C * ‖hχ.toLp χ‖ * ‖hψ.toLp ψ‖ := by
  apply matchedTail_opNorm_le_of_compactTests hp hpos
    (P ∘L G ∘L Q) (by positivity)
  intro f φ hφ hc hs hf
  change ‖P (G (Q f))‖ ≤ (C * ‖hχ.toLp χ‖ * ‖hψ.toLp ψ‖) * ‖f‖
  have hQφ : (Q f : ℝ → ℝ) =ᵐ[deepTailMeasure T] fun y => ψ y * φ y := by
    filter_upwards [hQ f, hf] with y hQy hfy
    rw [hQy, hfy]
  have hGφ := hG (Q f) (fun y => ψ y * φ y) (hψsmooth.mul hφ)
    hc.mul_left (tsupport_mul_subset_right.trans hs) hQφ
  apply matchedTail_kernel_output_norm_le (P (G (Q f))) f κ hκ hχ hψ _ hC hbound
  filter_upwards [hP (G (Q f)), hGφ] with x hPx hGx
  rw [hPx, hGx]
  congr 1
  apply integral_congr_ae
  filter_upwards [hf] with y hfy
  rw [hfy]
  ring

end ContinuousFlexibility.Radial
