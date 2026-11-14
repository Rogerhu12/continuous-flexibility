module

public import ContinuousFlexibility.Radial.InnerRadialEnergyDomain
public import ContinuousFlexibility.Radial.InnerDirichletDomain

/-!
# Smooth zero-endpoint fields in the physical H¹ closure

The existing endpoint cutoffs have a uniform derivative bound because
the field vanishes at each endpoint. Dominated convergence is applied
directly in μ_D to the value and the normalized derivative. In
particular no transfer of an unproved Sobolev domain between measures
is used, and endpoint derivatives need not vanish.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

theorem innerL2_norm_sq_sub_toLp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, (f x - g x) ^ 2 ∂μ := by
  rw [innerL2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g),
    MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with x hsub hx hy
  rw [hsub, Pi.sub_apply, hx, hy]

/-- Dominated convergence in real L² for the actual measure in use. -/
theorem innerL2_tendsto_toLp_of_dominated {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {F : ℕ → α → ℝ} {f B : α → ℝ}
    (hF : ∀ n, MemLp (F n) 2 μ) (hf : MemLp f 2 μ) (hB : MemLp B 2 μ)
    (hbound : ∀ n x, |F n x - f x| ≤ |B x|)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => (hF n).toLp (F n)) atTop (𝓝 (hf.toLp f)) := by
  have hBsq : Integrable (fun x => B x ^ 2) μ :=
    (memLp_two_iff_integrable_sq hB.aestronglyMeasurable).mp hB
  have hsq : Tendsto (fun n => ∫ x, (F n x - f x) ^ 2 ∂μ) atTop (𝓝 0) := by
    simpa only [Pi.sub_apply, sub_self, zero_pow (by decide : 2 ≠ 0), integral_zero] using
      (tendsto_integral_of_dominated_convergence (fun x => B x ^ 2)
        (fun n => (((hF n).sub hf).aestronglyMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable)
        hBsq
        (fun n => Eventually.of_forall (fun x => by
          simp only [Pi.sub_apply]
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (F n x - f x))]
          simpa only [sq_abs] using
            pow_le_pow_left₀ (abs_nonneg (F n x - f x)) (hbound n x) 2))
        (Eventually.of_forall (fun x => (hlim x |>.sub_const (f x)).pow 2)))
  have hnormsq : Tendsto (fun n => ‖(hF n).toLp (F n) - hf.toLp f‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [innerL2_norm_sq_sub_toLp] using hsq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hnorm := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hnormsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hnorm

/-- A compact-interval dominated-convergence interface for the same
physical zero-extended representatives used by all pieces. -/
theorem innerRadialIntervalToLp_tendsto_of_bound (D : ReferenceData)
    (hw : Continuous D.w) {a b : ℝ} (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hF : ∀ n, ContinuousOn (F n) (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n x, x ∈ Ioo a b → |F n x - f x| ≤ C)
    (hlim : ∀ x ∈ Ioo a b, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => innerRadialIntervalToLp D hw ha hcore hpos (F n) (hF n))
      atTop (𝓝 (innerRadialIntervalToLp D hw ha hcore hpos f hf)) := by
  apply innerL2_tendsto_toLp_of_dominated (radialHilbertMeasure D)
    (fun n => innerRadialInterval_memLp D hw ha hcore hpos (F n) (hF n))
    (innerRadialInterval_memLp D hw ha hcore hpos f hf)
    (innerRadialInterval_memLp D hw ha hcore hpos (fun _ => C) continuousOn_const)
  · intro n x
    by_cases hx : x ∈ Ioo a b
    · simpa only [indicator_of_mem hx, abs_of_nonneg hC] using hbound n x hx
    · simp only [indicator_of_notMem hx, sub_self, abs_zero, le_refl]
  · intro x
    by_cases hx : x ∈ Ioo a b
    · simpa only [indicator_of_mem hx] using hlim x hx
    · simpa only [indicator_of_notMem hx] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem innerDirichletApprox_tsupport {a b : ℝ} {u : ℝ → ℝ} (n : ℕ) :
    tsupport (innerDirichletApprox a b u n) ⊆ Ioo a b := by
  intro x hx
  by_contra hout
  exact (notMem_tsupport_iff_eventuallyEq.mpr
    (innerDirichletApprox_eventually_zero (u := u) n hout)) hx

theorem innerGapGradientField_continuousOn_of_contDiffAt {a b : ℝ} {u : ℝ → ℝ}
    (hu : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ u r) :
    ContinuousOn (innerGapGradientField u) (Icc a b) :=
  (continuous_id.div_const _).continuousOn.mul (innerDirichlet_deriv_continuousOn hu)

theorem innerRadialDirichletApprox_value_tendsto (D : ReferenceData)
    (hw : Continuous D.w) {a b : ℝ} (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    {u : ℝ → ℝ} (hu : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ u r) :
    Tendsto (fun n => innerRadialIntervalToLp D hw ha hcore hpos
      (innerDirichletApprox a b u n)
      (innerDirichletApprox_contDiff hu n).continuous.continuousOn) atTop
      (𝓝 (innerRadialIntervalToLp D hw ha hcore hpos u
        (fun r hr => (hu r hr).continuousAt.continuousWithinAt))) := by
  have hc : ContinuousOn u (Icc a b) :=
    fun r hr => (hu r hr).continuousAt.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hc
  let C : ℝ := max 0 C₀
  have hC : 0 ≤ C := le_max_left _ _
  have hb : ∀ r ∈ Icc a b, |u r| ≤ C := by
    intro r hr
    simpa only [Real.norm_eq_abs] using (hC₀ r hr).trans (le_max_right 0 C₀)
  apply innerRadialIntervalToLp_tendsto_of_bound D hw ha hcore hpos _ _
    (fun n => (innerDirichletApprox_contDiff hu n).continuous.continuousOn) hc (2 * C)
    (mul_nonneg (by norm_num) hC)
  · intro n r hr
    have hcut := innerDirichletApprox_abs_le a b u n r
    have huC := hb r (Ioo_subset_Icc_self hr)
    exact (abs_sub _ _).trans (by linarith)
  · intro r hr
    apply (tendsto_congr' (show (fun n => innerDirichletApprox a b u n r) =ᶠ[atTop]
      (fun _ => u r) from ?_)).2 tendsto_const_nhds
    filter_upwards [innerDirichletApprox_eventually_eq (u := u) hr] with n hn
    exact hn.eq_of_nhds

theorem innerRadialDirichletApprox_gradient_tendsto (D : ReferenceData)
    (hw : Continuous D.w) {a b : ℝ} (hab : a < b) (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    {u : ℝ → ℝ} (hu : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ u r)
    (hua : u a = 0) (hub : u b = 0) :
    Tendsto (fun n => innerRadialIntervalToLp D hw ha hcore hpos
      (innerGapGradientField (innerDirichletApprox a b u n))
      (innerGapGradientField_continuous (innerDirichletApprox_contDiff hu n)).continuousOn)
      atTop (𝓝 (innerRadialIntervalToLp D hw ha hcore hpos (innerGapGradientField u)
        (innerGapGradientField_continuousOn_of_contDiffAt hu))) := by
  obtain ⟨C, hC, htransition⟩ := innerTransition_deriv_bounded
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    (innerDirichlet_deriv_continuousOn hu)
  let M : ℝ := max 0 M₀
  have hM : 0 ≤ M := le_max_left _ _
  have hderiv : ∀ r ∈ Icc a b, |deriv u r| ≤ M := by
    intro r hr
    simpa only [Real.norm_eq_abs] using (hM₀ r hr).trans (le_max_right 0 M₀)
  have hdiff : ∀ r ∈ Icc a b, DifferentiableAt ℝ u r :=
    fun r hr => (hu r hr).differentiableAt (by simp)
  have hsqrt : 0 < Real.sqrt (12 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hb : 0 < b := ha.trans hab
  apply innerRadialIntervalToLp_tendsto_of_bound D hw ha hcore hpos _ _
    (fun n => (innerGapGradientField_continuous
      (innerDirichletApprox_contDiff hu n)).continuousOn)
    (innerGapGradientField_continuousOn_of_contDiffAt hu)
    ((b / Real.sqrt 12) * ((4 * C + 2) * M)) (by positivity)
  · intro n r hr
    have hF := innerDirichletApprox_deriv_bound hab hC hM htransition hdiff hderiv
      hua hub n (Ioo_subset_Icc_self hr)
    have hf := hderiv r (Ioo_subset_Icc_self hr)
    have hδ : |deriv (innerDirichletApprox a b u n) r - deriv u r| ≤ (4 * C + 2) * M :=
      (abs_sub _ _).trans (by linarith)
    have hrb : |r / Real.sqrt 12| ≤ b / Real.sqrt 12 := by
      rw [abs_div, abs_of_pos (ha.trans hr.1), abs_of_pos hsqrt]
      exact div_le_div_of_nonneg_right hr.2.le hsqrt.le
    simp only [innerGapGradientField, ← mul_sub, abs_mul]
    exact mul_le_mul hrb hδ (abs_nonneg _) (div_nonneg hb.le hsqrt.le)
  · intro r hr
    apply (tendsto_congr' (show
      (fun n => innerGapGradientField (innerDirichletApprox a b u n) r) =ᶠ[atTop]
        (fun _ => innerGapGradientField u r) from ?_)).2 tendsto_const_nhds
    filter_upwards [innerDirichletApprox_eventually_eq (u := u) hr] with n hn
    exact congrArg (fun x : ℝ => (r / Real.sqrt 12) * x) hn.deriv_eq

/-- A smooth field with zero endpoint values belongs to the actual
physical zero-endpoint closure, with its actual normalized derivative. -/
theorem innerRadialH1Zero_of_smooth_zero_endpoints (D : ReferenceData)
    (hw : Continuous D.w) {a b : ℝ} (hab : a < b) (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    {φ : ℝ → ℝ} (hφ : ∀ r ∈ Icc a b, ContDiffAt ℝ ∞ φ r)
    (hφa : φ a = 0) (hφb : φ b = 0) {u d : RadialModeL2 D}
    (hu : (u : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator φ)
    (hd : (d : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField φ)) :
    (u, d) ∈ innerRadialH1Zero D a b := by
  let U : ℕ → RadialModeL2 D := fun n =>
    innerRadialIntervalToLp D hw ha hcore hpos (innerDirichletApprox a b φ n)
      (innerDirichletApprox_contDiff hφ n).continuous.continuousOn
  let V : ℕ → RadialModeL2 D := fun n =>
    innerRadialIntervalToLp D hw ha hcore hpos
      (innerGapGradientField (innerDirichletApprox a b φ n))
      (innerGapGradientField_continuous (innerDirichletApprox_contDiff hφ n)).continuousOn
  have hU : Tendsto U atTop (𝓝 u) := by
    have he : innerRadialIntervalToLp D hw ha hcore hpos φ
        (fun r hr => (hφ r hr).continuousAt.continuousWithinAt) = u := by
      apply Lp.ext
      exact (innerRadialIntervalToLp_ae D hw ha hcore hpos φ _).trans hu.symm
    simpa only [he] using innerRadialDirichletApprox_value_tendsto D hw ha hcore hpos hφ
  have hV : Tendsto V atTop (𝓝 d) := by
    have he : innerRadialIntervalToLp D hw ha hcore hpos (innerGapGradientField φ)
        (innerGapGradientField_continuousOn_of_contDiffAt hφ) = d := by
      apply Lp.ext
      exact (innerRadialIntervalToLp_ae D hw ha hcore hpos (innerGapGradientField φ) _).trans hd.symm
    simpa only [he] using
      innerRadialDirichletApprox_gradient_tendsto D hw hab ha hcore hpos hφ hφa hφb
  apply (mem_innerRadialH1Zero D a b (u, d)).mpr
  apply mem_closure_of_tendsto (hU.prodMk_nhds hV)
  apply Eventually.of_forall
  intro n
  exact ⟨innerDirichletApprox a b φ n, innerDirichletApprox_contDiff hφ n,
    innerDirichletApprox_hasCompactSupport a b φ n, innerDirichletApprox_tsupport n,
    innerRadialIntervalToLp_ae D hw ha hcore hpos (innerDirichletApprox a b φ n)
      (innerDirichletApprox_contDiff hφ n).continuous.continuousOn,
    innerRadialIntervalToLp_ae D hw ha hcore hpos
      (innerGapGradientField (innerDirichletApprox a b φ n))
      (innerGapGradientField_continuous (innerDirichletApprox_contDiff hφ n)).continuousOn⟩

end ContinuousFlexibility.Radial
