import ContinuousFlexibility.Analysis.OpticalCurvatureInequality

/-!
# Actual second variation of an optical travel integral

On a compact interior collar, the radicand has a positive uniform lower
bound.  Both derivatives below are derivatives of the actual parameter
integral.  Compactness supplies the domination needed for differentiation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- A convenient compact-rectangle form of differentiation under a real
interval integral. -/
theorem hasDerivAt_intervalIntegral_of_compact_rectangle
    {F G : ℝ → ℝ → ℝ} {a b l h t : ℝ} (hab : a < b) (ht : t ∈ Ioo l h)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc l h ×ˢ Icc a b))
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (Icc l h ×ˢ Icc a b))
    (hderiv : ∀ s ∈ Ioo l h, ∀ r ∈ Icc a b,
      HasDerivAt (fun z => F z r) (G s r) s) :
    HasDerivAt (fun s => ∫ r in a..b, F s r) (∫ r in a..b, G t r) t := by
  obtain ⟨N, hN⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hG
  have hFi (s : ℝ) (hs : s ∈ Icc l h) : IntervalIntegrable (F s) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc _ hab.le
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun r hr => ⟨hs, hr⟩)
  have hGi (s : ℝ) (hs : s ∈ Icc l h) : IntervalIntegrable (G s) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc _ hab.le
    exact hG.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun r hr => ⟨hs, hr⟩)
  let μ := volume.restrict (Ioc a b)
  let : IsFiniteMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
  have hmem : ∀ᵐ r ∂μ, r ∈ Icc a b :=
    (ae_restrict_mem measurableSet_Ioc).mono fun r hr => Ioc_subset_Icc_self hr
  have hU : Ioo l h ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
  have hInt := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := G) (bound := fun _ => N) hU
    (hU.mono fun s hs => (hFi s (Ioo_subset_Icc_self hs)).1.aestronglyMeasurable)
    (hFi t (Ioo_subset_Icc_self ht)).1
    (hGi t (Ioo_subset_Icc_self ht)).1.aestronglyMeasurable
    (hmem.mono fun r hr s hs => hN (s, r) ⟨Ioo_subset_Icc_self hs, hr⟩)
    (integrable_const N)
    (hmem.mono fun r hr s hs => hderiv s hs r hr)).2
  change HasDerivAt (fun s => ∫ r in Ioc a b, F s r) (∫ r in Ioc a b, G t r) t at hInt
  simpa only [← intervalIntegral.integral_of_le hab.le] using hInt

/-- Positivity of a continuous affine radicand persists on one common
parameter interval for the whole compact spatial collar. -/
theorem sqrtAffine_positive_parameter_interval {q u : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hq : ContinuousOn q (Icc a b)) (hu : ContinuousOn u (Icc a b))
    (hqpos : ∀ r ∈ Icc a b, 0 < q r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc (-δ) δ, ∀ r ∈ Icc a b, 0 < q r + t * u r := by
  have hne : (Icc a b).Nonempty := nonempty_Icc.mpr hab.le
  obtain ⟨rmin, hrmin, hmin⟩ := isCompact_Icc.exists_isMinOn hne hq
  obtain ⟨rmax, hrmax, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hu.abs
  let q0 := q rmin
  let M := |u rmax|
  let δ := q0 / (2 * (M + 1))
  have hq0 : 0 < q0 := hqpos rmin hrmin
  have hM : 0 ≤ M := abs_nonneg _
  have hδ : 0 < δ := div_pos hq0 (by positivity)
  have hδM : δ * M ≤ q0 / 2 := by
    have heq : δ * (M + 1) = q0 / 2 := by
      dsimp only [δ]
      rw [← div_div, div_mul_cancel₀ _ (show M + 1 ≠ 0 by positivity)]
    calc
      δ * M ≤ δ * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
      _ = _ := heq
  refine ⟨δ, hδ, fun t ht r hr => ?_⟩
  have hprod : |t * u r| ≤ q0 / 2 := by
    rw [abs_mul]
    exact (mul_le_mul (abs_le.mpr ht) (hmax hr) (abs_nonneg _) hδ.le).trans hδM
  have hbase : q0 ≤ q r := hmin hr
  linarith only [hprod, hbase, hq0, neg_abs_le (t * u r)]

/-- The two genuine derivatives of a compact affine-square-root integral.
The second derivative is nonpositive and has no cancellation in its
integrand. -/
theorem hasDerivAt_sqrtAffine_integral_twice {q u : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hq : ContinuousOn q (Icc a b)) (hu : ContinuousOn u (Icc a b))
    (hqpos : ∀ r ∈ Icc a b, 0 < q r) :
    HasDerivAt (fun t : ℝ => ∫ r in a..b, Real.sqrt (q r + t * u r))
      (∫ r in a..b, u r / (2 * Real.sqrt (q r))) 0 ∧
    HasDerivAt (deriv (fun t : ℝ => ∫ r in a..b, Real.sqrt (q r + t * u r)))
      (-(∫ r in a..b, u r ^ 2 / (4 * Real.sqrt (q r) ^ 3))) 0 := by
  obtain ⟨δ, hδ, hrad⟩ := sqrtAffine_positive_parameter_interval hab hq hu hqpos
  let K := Icc (-δ) δ ×ˢ Icc a b
  let U := Ioo (-δ) δ
  let F (t r : ℝ) := Real.sqrt (q r + t * u r)
  let G (t r : ℝ) := u r / (2 * F t r)
  let H (t r : ℝ) := -(u r ^ 2 / (4 * F t r ^ 3))
  have hqK : ContinuousOn (fun p : ℝ × ℝ => q p.2) K :=
    hq.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have huK : ContinuousOn (fun p : ℝ × ℝ => u p.2) K :=
    hu.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hFc : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) K :=
    Real.continuous_sqrt.comp_continuousOn (hqK.add (continuous_fst.continuousOn.mul huK))
  have hFpos (p : ℝ × ℝ) (hp : p ∈ K) : 0 < F p.1 p.2 :=
    Real.sqrt_pos.mpr (hrad p.1 hp.1 p.2 hp.2)
  have hGc : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) K :=
    huK.div (continuousOn_const.mul hFc)
      (fun p hp => (mul_pos zero_lt_two (hFpos p hp)).ne')
  have hHc : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) K :=
    ((huK.pow 2).div (continuousOn_const.mul (hFc.pow 3))
      (fun p hp => (mul_pos (by norm_num) (pow_pos (hFpos p hp) 3)).ne')).neg
  have hFd (t : ℝ) (ht : t ∈ U) (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivAt (fun s => F s r) (G t r) t := by
    have hlin : HasDerivAt (fun s : ℝ => q r + s * u r) (u r) t := by
      simpa only [id_eq, one_mul] using ((hasDerivAt_id t).mul_const (u r)).const_add (q r)
    exact hlin.sqrt (hrad t (Ioo_subset_Icc_self ht) r hr).ne'
  have hGd (t : ℝ) (ht : t ∈ U) (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivAt (fun s => G s r) (H t r) t := by
    have hp : 0 < F t r := hFpos (t, r) ⟨Ioo_subset_Icc_self ht, hr⟩
    have h := (hasDerivAt_const t (u r)).div ((hFd t ht r hr).const_mul 2)
      (mul_pos zero_lt_two hp).ne'
    convert h using 1
    dsimp only [G, H]
    field_simp [hp.ne'] <;> ring
  have h0 : (0 : ℝ) ∈ U := ⟨neg_neg_of_pos hδ, hδ⟩
  have hFi (t : ℝ) (ht : t ∈ U) :=
    hasDerivAt_intervalIntegral_of_compact_rectangle hab ht hFc hGc hFd
  have hGi := hasDerivAt_intervalIntegral_of_compact_rectangle hab h0 hGc hHc hGd
  have heq : deriv (fun t : ℝ => ∫ r in a..b, F t r) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => ∫ r in a..b, G t r) := by
    filter_upwards [Ioo_mem_nhds h0.1 h0.2] with t ht
    exact (hFi t ht).deriv
  constructor
  · simpa only [F, G, zero_mul, add_zero] using hFi 0 h0
  · simpa only [F, G, H, zero_mul, add_zero, intervalIntegral.integral_neg] using
      hGi.congr_of_eventuallyEq heq

/-- This form takes the normalization and curvature estimate as actual
derivative statements about the same integral, rather than as unrelated
numbers. -/
theorem sqrtAffine_normalized_secondDerivative_lower_bound
    {q u : ℝ → ℝ} {a b B D : ℝ}
    (hab : a < b) (hq : ContinuousOn q (Icc a b)) (hu : ContinuousOn u (Icc a b))
    (hqpos : ∀ r ∈ Icc a b, 0 < q r) (huB : ∀ r ∈ Icc a b, |u r| ≤ B)
    (hunit : HasDerivAt (fun t : ℝ => ∫ r in a..b, Real.sqrt (q r + t * u r)) 1 0)
    (hD : |deriv (deriv (fun t : ℝ => ∫ r in a..b, Real.sqrt (q r + t * u r))) 0| ≤ D) :
    2 ≤ (b - a) ^ 2 * B * D := by
  obtain ⟨hfirst, hsecond⟩ := hasDerivAt_sqrtAffine_integral_twice hab hq hu hqpos
  have hunitInt : (∫ r in a..b, u r / (2 * Real.sqrt (q r))) = 1 :=
    hfirst.unique hunit
  have hcurv : (∫ r in a..b, u r ^ 2 / (4 * Real.sqrt (q r) ^ 3)) ≤ D := by
    calc
      _ = -deriv (deriv (fun t : ℝ => ∫ r in a..b, Real.sqrt (q r + t * u r))) 0 := by
        rw [hsecond.deriv, neg_neg]
      _ ≤ _ := (neg_le_abs _).trans hD
  exact sqrtAffine_normalized_control_lower_bound hab hq hu hqpos huB hunitInt hcurv

end ContinuousFlexibility.Analysis
