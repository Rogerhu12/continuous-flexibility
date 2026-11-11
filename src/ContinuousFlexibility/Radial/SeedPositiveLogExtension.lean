import ContinuousFlexibility.Radial.SeedConnectorReconstruction
import ContinuousFlexibility.Radial.MorseJoinActualGerms

/-!
# A positive logarithmic profile extending one regular germ

Extend the logarithm of the positive derivative, then exponentiate.  The
derivative is positive everywhere and equals one off a compact interval.
Its primitive has the original full germ and exact affine ends.  This
prepares an inward cone without imposing any condition on the solution.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

structure SeedPositiveLogExtension (f : ℝ → ℝ) (y₀ : ℝ) where
  logProfile : ℝ → ℝ
  left : ℝ
  right : ℝ
  left_lt : left < y₀
  right_gt : y₀ < right
  smooth : ContDiff ℝ ∞ logProfile
  positive : ∀ y, 0 < deriv logProfile y
  germ : logProfile =ᶠ[𝓝 y₀] f
  left_cone : ∀ y, y ≤ left → deriv logProfile y = 1
  right_cone : ∀ y, right ≤ y → deriv logProfile y = 1

theorem exists_seedPositiveLogExtension_of_positive {f : ℝ → ℝ} {a b y₀ : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo a b)) (hy₀ : y₀ ∈ Ioo a b)
    (hp : ∀ y ∈ Ioo a b, 0 < deriv f y) :
    Nonempty (SeedPositiveLogExtension f y₀) := by
  have hlog : ContDiffOn ℝ ∞ (fun y => log (deriv f y)) (Ioo a b) :=
    (hf.deriv_of_isOpen isOpen_Ioo (by simp)).log
      (fun y hy => (hp y hy).ne')
  obtain ⟨F, hFs, hFc, hFg⟩ :=
    exists_contDiff_joinGerm_extension hy₀.1 le_rfl hy₀.2 hlog
  let q : ℝ → ℝ := fun y => exp (F y)
  have hqs : ContDiff ℝ ∞ q := hFs.exp
  let H : ℝ → ℝ := connectorLogHeight q y₀ (f y₀)
  have hHd (y : ℝ) : HasDerivAt H (q y) y :=
    hasDerivAt_connectorLogHeight hqs y₀ (f y₀) y
  have hqeq : q =ᶠ[𝓝 y₀] deriv f := by
    filter_upwards [hFg y₀ ⟨le_rfl, le_rfl⟩,
      Ioo_mem_nhds hy₀.1 hy₀.2] with y hy hyJ
    change exp (F y) = deriv f y
    rw [hy, exp_log (hp y hyJ)]
  have hnb : {y | q y = deriv f y ∧ y ∈ Ioo a b} ∈ 𝓝 y₀ :=
    hqeq.and (Ioo_mem_nhds hy₀.1 hy₀.2)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnb
  have hHf : H =ᶠ[𝓝 y₀] f := by
    have heq : EqOn H f (Metric.ball y₀ ε) :=
      isOpen_ball.eqOn_of_deriv_eq (convex_ball y₀ ε).isPreconnected
        (fun y _ => (hHd y).differentiableAt.differentiableWithinAt)
        (fun y hy => (hf.contDiffAt
          (isOpen_Ioo.mem_nhds (hεsub hy).2)).differentiableAt
          (by simp) |>.differentiableWithinAt)
        (fun y hy => by rw [(hHd y).deriv]; exact (hεsub hy).1)
        (Metric.mem_ball_self hε) (connectorLogHeight_self q y₀ (f y₀))
    exact Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds y₀ hε) heq
  have hcompact : IsCompact (tsupport F) := hFc
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun y : ℝ => y) (tsupport F))
  have hzero (y : ℝ) (hy : M < |y|) : F y = 0 := by
    by_contra hne
    have hm := hM y (subset_tsupport F (Function.mem_support.mpr hne))
    exact (not_le_of_gt hy) (by simpa only [Real.norm_eq_abs] using hm)
  let L := min (y₀ - 1) (-M - 1)
  let R := max (y₀ + 1) (M + 1)
  refine ⟨⟨H, L, R, ?_, ?_, connectorLogHeight_contDiff hqs _ _, ?_, hHf, ?_, ?_⟩⟩
  · exact (min_le_left _ _).trans_lt (by linarith)
  · exact (show y₀ < y₀ + 1 by linarith).trans_le (le_max_left _ _)
  · intro y
    rw [(hHd y).deriv]
    exact exp_pos _
  · intro y hy
    rw [(hHd y).deriv]
    change exp (F y) = 1
    rw [hzero y (by
      have hL := min_le_right (y₀ - 1) (-M - 1)
      have ha := neg_le_abs y
      change y ≤ min (y₀ - 1) (-M - 1) at hy
      linarith), exp_zero]
  · intro y hy
    rw [(hHd y).deriv]
    change exp (F y) = 1
    rw [hzero y (by
      have hR := le_max_right (y₀ + 1) (M + 1)
      have ha := le_abs_self y
      change max (y₀ + 1) (M + 1) ≤ y at hy
      linarith), exp_zero]

theorem exists_seedPositiveLogExtension {f : ℝ → ℝ} {a b y₀ : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo a b)) (hy₀ : y₀ ∈ Ioo a b)
    (hp : 0 < deriv f y₀) : Nonempty (SeedPositiveLogExtension f y₀) := by
  have hd : ContinuousAt (deriv f) y₀ :=
    (hf.deriv_of_isOpen isOpen_Ioo (by simp)).continuousOn.continuousAt
      (Ioo_mem_nhds hy₀.1 hy₀.2)
  have he : {y | 0 < deriv f y ∧ y ∈ Ioo a b} ∈ 𝓝 y₀ :=
    (hd.eventually (Ioi_mem_nhds hp)).and (Ioo_mem_nhds hy₀.1 hy₀.2)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp he
  rw [Real.ball_eq_Ioo] at hsub
  exact exists_seedPositiveLogExtension_of_positive
    (hf.mono (fun y hy => (hsub hy).2))
    ⟨by linarith, by linarith⟩ (fun y hy => (hsub hy).1)

namespace SeedPositiveLogExtension

theorem affine_ends {f : ℝ → ℝ} {y₀ : ℝ} (E : SeedPositiveLogExtension f y₀) :
    ∃ cL cR : ℝ,
      (∀ y, y < E.left → E.logProfile y = y + cL) ∧
      (∀ y, E.right < y → E.logProfile y = y + cR) := by
  refine ⟨E.logProfile (E.left - 1) - (E.left - 1),
    E.logProfile (E.right + 1) - (E.right + 1), ?_, ?_⟩
  · have heq := isOpen_Iio.eqOn_of_deriv_eq (convex_Iio E.left).isPreconnected
      (fun y _ => (E.smooth.differentiable (by simp) y).differentiableWithinAt)
      (fun y _ => ((hasDerivAt_id' y).add_const
        (E.logProfile (E.left - 1) - (E.left - 1))).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        rw [E.left_cone y hy.le]
        exact (((hasDerivAt_id' y).add_const
          (E.logProfile (E.left - 1) - (E.left - 1))).deriv).symm)
      (show E.left - 1 ∈ Iio E.left by change E.left - 1 < E.left; linarith)
      (show E.logProfile (E.left - 1) =
        (E.left - 1) + (E.logProfile (E.left - 1) - (E.left - 1)) by ring)
    exact fun y hy => heq hy
  · have heq := isOpen_Ioi.eqOn_of_deriv_eq (convex_Ioi E.right).isPreconnected
      (fun y _ => (E.smooth.differentiable (by simp) y).differentiableWithinAt)
      (fun y _ => ((hasDerivAt_id' y).add_const
        (E.logProfile (E.right + 1) - (E.right + 1))).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        rw [E.right_cone y hy.le]
        exact (((hasDerivAt_id' y).add_const
          (E.logProfile (E.right + 1) - (E.right + 1))).deriv).symm)
      (show E.right + 1 ∈ Ioi E.right by change E.right < E.right + 1; linarith)
      (show E.logProfile (E.right + 1) =
        (E.right + 1) + (E.logProfile (E.right + 1) - (E.right + 1)) by ring)
    exact fun y hy => heq hy

end SeedPositiveLogExtension
end ContinuousFlexibility.Radial
