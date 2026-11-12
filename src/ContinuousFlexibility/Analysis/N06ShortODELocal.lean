import ContinuousFlexibility.Analysis.N06ShortODEBounds
import ContinuousFlexibility.Analysis.OneHighCircleFlowLocalization

/-!
# The short ODE endpoint estimate for genuine closed-interval germs

Only two derivatives and positivity on the closed interval are needed.
A smooth time clamp gives a positive global C2 representative preserving
all germs on that interval.  Reduction of order then uses the already
proved normalized short-interval estimate.  No smoothness or positivity
of an arbitrarily totalized function outside the interval is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem n06_positive_closed_two_extension
    {W : ℝ → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hW : ∀ x ∈ Icc (0 : ℝ) ℓ, ContDiffAt ℝ 2 W x)
    (hpos : ∀ x ∈ Icc (0 : ℝ) ℓ, 0 < W x) :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ (∀ x, 0 < F x) ∧
      ∀ x ∈ Icc (0 : ℝ) ℓ, F =ᶠ[𝓝 x] W := by
  let P : ℝ → Prop := fun x => ContDiffAt ℝ 2 W x ∧ 0 < W x
  have hnear (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ℓ) : ∀ᶠ t in 𝓝 x, P t :=
    ((hW x hx).eventually (by simp)).and
      ((hW x hx).continuousAt.tendsto.eventually (isOpen_Ioi.mem_nhds (hpos x hx)))
  obtain ⟨δ0, hδ0, h0⟩ := Metric.mem_nhds_iff.mp (hnear 0 ⟨le_rfl, hℓ.le⟩)
  obtain ⟨δ1, hδ1, h1⟩ := Metric.mem_nhds_iff.mp (hnear ℓ ⟨hℓ.le, le_rfl⟩)
  let δ : ℝ := min δ0 δ1
  have hδ : 0 < δ := lt_min hδ0 hδ1
  have hmargin (x : ℝ) (hx : x ∈ Ioo (-δ) (ℓ + δ)) : P x := by
    by_cases hlo : x < 0
    · apply h0
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg hlo]
      have hle : δ ≤ δ0 := min_le_left _ _
      linarith [hx.1]
    by_cases hhi : ℓ < x
    · apply h1
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hhi)]
      have hle : δ ≤ δ1 := min_le_right _ _
      linarith [hx.2]
    exact ⟨hW x ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩,
      hpos x ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩⟩
  have hab : -δ / 4 ≤ ℓ + δ / 4 := by linarith
  have heps : 0 < δ / 4 := by positivity
  let κ : ℝ → ℝ := circleFlowSmoothTimeClamp (-δ / 4) (ℓ + δ / 4) (δ / 4) hab heps
  have hκ : ContDiff ℝ 2 κ := (contDiff_circleFlowSmoothTimeClamp hab heps).of_le (by simp)
  have hκrange (x : ℝ) : κ x ∈ Ioo (-δ) (ℓ + δ) := by
    have hk := circleFlowSmoothTimeClamp_mem hab heps x
    change -δ / 4 - δ / 4 < κ x ∧ κ x < ℓ + δ / 4 + δ / 4 at hk
    constructor <;> linarith [hk.1, hk.2]
  let F : ℝ → ℝ := fun x => W (κ x)
  have hF : ContDiff ℝ 2 F := contDiff_iff_contDiffAt.mpr fun x =>
    (hmargin (κ x) (hκrange x)).1.comp x hκ.contDiffAt
  refine ⟨F, hF, fun x => (hmargin (κ x) (hκrange x)).2, ?_⟩
  intro x hx
  filter_upwards [Ioo_mem_nhds (show -δ / 4 < x by linarith [hx.1])
    (show x < ℓ + δ / 4 by linarith [hx.2])] with t ht
  change W (κ t) = W t
  rw [show κ t = t from circleFlowSmoothTimeClamp_eq hab heps ⟨ht.1.le, ht.2.le⟩]

private theorem n06_positive_two_reciprocal_mass
    {W : ℝ → ℝ} {ℓ K : ℝ} (hW : ContDiff ℝ 2 W)
    (hpos : ∀ x, 0 < W x) (hℓ : 0 < ℓ) (hK : 0 ≤ K)
    (hsmall : K * ℓ ^ 2 ≤ (1 / 4 : ℝ))
    (hdd : ∀ x ∈ Icc (0 : ℝ) ℓ, |deriv (deriv W) x| ≤ K * W x) :
    ℓ / 2 ≤ W 0 * W ℓ * ∫ t in (0 : ℝ)..ℓ, (W t)⁻¹ ^ 2 := by
  let J : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, (W t)⁻¹ ^ 2
  let S : ℝ → ℝ := n06ReductionOfOrder W
  have hWd : Differentiable ℝ W := hW.differentiable (by simp)
  have hWdd : Differentiable ℝ (deriv W) := hW.differentiable_deriv_two
  have hIc : Continuous (fun x => (W x)⁻¹ ^ 2) :=
    ((hW.inv (fun x => (hpos x).ne')).pow 2).continuous
  have hJderiv (x : ℝ) : HasDerivAt J ((W x)⁻¹ ^ 2) x :=
    intervalIntegral.integral_hasDerivAt_right (hIc.intervalIntegrable 0 x)
      hIc.aestronglyMeasurable.stronglyMeasurableAtFilter hIc.continuousAt
  have hSfirst (x : ℝ) : HasDerivAt S
      (W 0 * (deriv W x * J x + (W x)⁻¹)) x := by
    have hd := ((hWd x).hasDerivAt.fun_mul (hJderiv x)).const_mul (W 0)
    have halg : W 0 * (deriv W x * J x + W x * (W x)⁻¹ ^ 2) =
        W 0 * (deriv W x * J x + (W x)⁻¹) := by
      field_simp [(hpos x).ne']
      <;> ring
    exact halg ▸ hd
  have hSformula : deriv S = fun x => W 0 * (deriv W x * J x + (W x)⁻¹) :=
    funext fun x => (hSfirst x).deriv
  have hSsecond (x : ℝ) : HasDerivAt (deriv S)
      (W 0 * deriv (deriv W) x * J x) x := by
    have hdInv := (hWd x).hasDerivAt.inv (hpos x).ne'
    have hd := (((hWdd x).hasDerivAt.fun_mul (hJderiv x)).add hdInv).const_mul (W 0)
    have halg : W 0 * ((deriv (deriv W) x * J x +
        deriv W x * (W x)⁻¹ ^ 2) + -deriv W x / (W x) ^ 2) =
        W 0 * deriv (deriv W) x * J x := by
      field_simp [(hpos x).ne']
      <;> ring
    rw [hSformula]
    simpa only [Pi.add_apply, Pi.inv_apply, halg] using hd
  have hS0 : S 0 = 0 := by
    simp only [S, n06ReductionOfOrder, intervalIntegral.integral_same, mul_zero]
  have hSd0 : deriv S 0 = 1 := by
    rw [hSformula]
    simp only [J, intervalIntegral.integral_same, mul_zero, zero_add,
      mul_inv_cancel₀ (hpos 0).ne']
  have hSbound (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ℓ) :
      |deriv (deriv S) x| ≤ K * |S x| := by
    rw [(hSsecond x).deriv]
    calc
      |W 0 * deriv (deriv W) x * J x| = W 0 * |deriv (deriv W) x| * |J x| := by
        rw [abs_mul, abs_mul, abs_of_pos (hpos 0)]
      _ ≤ W 0 * (K * W x) * |J x| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hdd x hx) (hpos 0).le)
          (abs_nonneg _)
      _ = K * |S x| := by
        simp only [S, n06ReductionOfOrder, abs_mul, abs_of_pos (hpos 0),
          abs_of_pos (hpos x)]
        ring
  have hh := n06_short_ode_normalized_lower hℓ hK hsmall
    (fun x _ => (hSfirst x).differentiableAt)
    (fun x _ => (hSsecond x).differentiableAt) hS0 hSd0 hSbound
  simpa only [S, n06ReductionOfOrder, mul_assoc] using hh

/-- The polynomial lower bound depends only on actual closed-interval
germs, the relative second derivative, and the genuine reciprocal mass. -/
theorem n06_positive_closed_endpoint_lower
    {W : ℝ → ℝ} {ℓ K B Q : ℝ}
    (hW : ∀ x ∈ Icc (0 : ℝ) ℓ, ContDiffAt ℝ 2 W x)
    (hpos : ∀ x ∈ Icc (0 : ℝ) ℓ, 0 < W x)
    (hℓ : 0 < ℓ) (hK : 0 ≤ K) (hsmall : K * ℓ ^ 2 ≤ (1 / 4 : ℝ))
    (hdd : ∀ x ∈ Icc (0 : ℝ) ℓ, |deriv (deriv W) x| ≤ K * W x)
    (hB : 0 < B) (hQ : 0 < Q) (hend : W ℓ ≤ B)
    (hmass : (∫ t in (0 : ℝ)..ℓ, (W t)⁻¹ ^ 2) ≤ Q) :
    ℓ / (2 * B * Q) ≤ W 0 := by
  obtain ⟨F, hF, hFpos, hFW⟩ := n06_positive_closed_two_extension hℓ hW hpos
  have hFdd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ℓ) :
      |deriv (deriv F) x| ≤ K * F x := by
    rw [(hFW x hx).deriv.deriv_eq, (hFW x hx).eq_of_nhds]
    exact hdd x hx
  have hmassEq : (∫ t in (0 : ℝ)..ℓ, (F t)⁻¹ ^ 2) =
      ∫ t in (0 : ℝ)..ℓ, (W t)⁻¹ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) ℓ := by simpa only [uIcc_of_le hℓ.le] using ht
    change (F t)⁻¹ ^ 2 = (W t)⁻¹ ^ 2
    rw [(hFW t ht').eq_of_nhds]
  have hlower := n06_positive_two_reciprocal_mass hF hFpos hℓ hK hsmall hFdd
  rw [(hFW 0 ⟨le_rfl, hℓ.le⟩).eq_of_nhds,
    (hFW ℓ ⟨hℓ.le, le_rfl⟩).eq_of_nhds, hmassEq] at hlower
  have hmass0 : 0 ≤ ∫ t in (0 : ℝ)..ℓ, (W t)⁻¹ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hℓ.le (fun _ => sq_nonneg _)
  have hW0 : 0 ≤ W 0 := (hpos 0 ⟨le_rfl, hℓ.le⟩).le
  have hupper : W 0 * W ℓ * (∫ t in (0 : ℝ)..ℓ, (W t)⁻¹ ^ 2) ≤ W 0 * B * Q :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hend hW0) hmass0).trans
      (mul_le_mul_of_nonneg_left hmass (mul_nonneg hW0 hB.le))
  apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) hB) hQ)).mpr
  nlinarith only [hlower, hupper]

end ContinuousFlexibility.Analysis
