import ContinuousFlexibility.Analysis.OneHighCircleFlowBasic

/-!
# Integral Gronwall with the actual time-dependent coefficients

The constants in the circle-flow estimates depend on integrals of speed
norms. Replacing these norms by time suprema would give a different
estimate. The integrating factor below keeps the integral dependence.
This is a general intermediate inequality; its applications derive the
integral premise from the genuine trajectory or jet equation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory

set_option backward.isDefEq.respectTransparency false

private theorem integral_gronwall_of_continuous {u A B : ℝ → ℝ} {a b δ : ℝ}
    (hab : a ≤ b) (hu : Continuous u) (hA : Continuous A) (hB : Continuous B)
    (hApos : ∀ t ∈ Icc a b, 0 ≤ A t) (hBpos : ∀ t ∈ Icc a b, 0 ≤ B t)
    (hbound : ∀ t ∈ Icc a b, u t ≤ δ + ∫ r in a..t, A r * u r + B r) :
    u b ≤ (δ + ∫ r in a..b, B r) * Real.exp (∫ r in a..b, A r) := by
  let K : ℝ → ℝ := fun t => ∫ r in a..t, A r
  let J : ℝ → ℝ := fun t => δ + ∫ r in a..t, A r * u r + B r
  have hKderiv (t : ℝ) : HasDerivAt K (A t) t :=
    (hA.integral_hasStrictDerivAt a t).hasDerivAt
  have hJderiv (t : ℝ) : HasDerivAt J (A t * u t + B t) t :=
    (((hA.mul hu).add hB).integral_hasStrictDerivAt a t).hasDerivAt.const_add δ
  have hK : Continuous K := continuous_iff_continuousAt.mpr fun t => (hKderiv t).continuousAt
  have hJ : Continuous J := continuous_iff_continuousAt.mpr fun t => (hJderiv t).continuousAt
  let W : ℝ → ℝ := fun t => J t * Real.exp (-K t)
  let D : ℝ → ℝ := fun t => Real.exp (-K t) * (A t * u t + B t - A t * J t)
  have hW : Continuous W := hJ.mul (Real.continuous_exp.comp hK.neg)
  have hD : Continuous D :=
    (Real.continuous_exp.comp hK.neg).mul (((hA.mul hu).add hB).sub (hA.mul hJ))
  have hWderiv (t : ℝ) : HasDerivAt W (D t) t := by
    apply ((hJderiv t).mul (hKderiv t).neg.exp).congr_deriv
    dsimp only [D]
    ring
  have hDle (t : ℝ) (ht : t ∈ Icc a b) : D t ≤ B t := by
    have hJbound : u t ≤ J t := hbound t ht
    have hcoeff := mul_le_mul_of_nonneg_left hJbound (hApos t ht)
    have hsource : A t * u t + B t - A t * J t ≤ B t := by linarith
    have hKpos : 0 ≤ K t :=
      intervalIntegral.integral_nonneg ht.1 (fun r hr => hApos r ⟨hr.1, hr.2.trans ht.2⟩)
    have hexp : Real.exp (-K t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hKpos)
    calc
      D t ≤ Real.exp (-K t) * B t :=
        mul_le_mul_of_nonneg_left hsource (Real.exp_pos _).le
      _ ≤ B t := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hexp (hBpos t ht)
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab
    (hD.intervalIntegrable a b) (hB.intervalIntegrable a b) hDle
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hW.continuousOn (fun t _ => hWderiv t) (hD.intervalIntegrable a b)
  have hWa : W a = δ := by
    simp only [W, J, K, intervalIntegral.integral_same, add_zero, neg_zero,
      Real.exp_zero, mul_one]
  have hfactor : J b * Real.exp (-K b) ≤ δ + ∫ r in a..b, B r := by
    rw [hFTC, hWa] at hmono
    dsimp only [W] at hmono
    linarith
  calc
    u b ≤ J b := hbound b ⟨hab, le_rfl⟩
    _ = (J b * Real.exp (-K b)) * Real.exp (K b) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ (δ + ∫ r in a..b, B r) * Real.exp (K b) :=
      mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le

/-- The nonautonomous integral inequality on a closed interval, requiring
continuity only on that interval and retaining the integrals of both
coefficients in its conclusion. -/
theorem integral_gronwall_of_continuousOn {u A B : ℝ → ℝ} {a b δ : ℝ}
    (hab : a ≤ b) (hu : ContinuousOn u (Icc a b))
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hApos : ∀ t ∈ Icc a b, 0 ≤ A t) (hBpos : ∀ t ∈ Icc a b, 0 ≤ B t)
    (hbound : ∀ t ∈ Icc a b, u t ≤ δ + ∫ r in a..t, A r * u r + B r) :
    u b ≤ (δ + ∫ r in a..b, B r) * Real.exp (∫ r in a..b, A r) := by
  let clamp : ℝ → ℝ := fun t => max a (min t b)
  have hc : Continuous clamp := continuous_const.max (continuous_id.min continuous_const)
  have hmem (t : ℝ) : clamp t ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have heq (t : ℝ) (ht : t ∈ Icc a b) : clamp t = t := by
    dsimp only [clamp]
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have hIntegral (f : ℝ → ℝ) (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ r in a..t, f (clamp r)) = ∫ r in a..t, f r := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc a b := by
      have hh : r ∈ Icc a t := by simpa only [uIcc_of_le ht.1] using hr
      exact ⟨hh.1, hh.2.trans ht.2⟩
    rw [heq r hr']
  have hresult := integral_gronwall_of_continuous hab
    (hu.comp_continuous hc hmem) (hA.comp_continuous hc hmem) (hB.comp_continuous hc hmem)
    (fun t _ => hApos (clamp t) (hmem t))
    (fun t _ => hBpos (clamp t) (hmem t))
    (δ := δ) (by
      intro t ht
      simpa only [heq t ht, hIntegral (fun r => A r * u r + B r) t ht] using hbound t ht)
  simpa only [heq b ⟨hab, le_rfl⟩, hIntegral A b ⟨hab, le_rfl⟩,
    hIntegral B b ⟨hab, le_rfl⟩] using hresult

end ContinuousFlexibility.Analysis
