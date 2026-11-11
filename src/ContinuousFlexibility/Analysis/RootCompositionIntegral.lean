import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

/-!
# Smooth dependence of a compact interval integral

Jointly smooth integrands can be integrated over a fixed compact interval.
The parameter space is proper, so a continuous derivative is uniformly
bounded on a compact parameter neighborhood times the integration interval.
This supplies the local domination needed for differentiation under the
integral.  Finite-order induction then gives smoothness of every order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Interval

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The parameter derivative of an integral of a jointly smooth integrand. -/
theorem hasFDerivAt_intervalIntegral_of_contDiff
    {G : E × ℝ → F} (hG : ContDiff ℝ ∞ G) (a b : ℝ) (x₀ : E) :
    HasFDerivAt (fun x : E => ∫ t in a..b, G (x, t))
      (∫ t in a..b,
        (fderiv ℝ G (x₀, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x₀ := by
  let G' : E × ℝ → E →L[ℝ] F := fun q =>
    (fderiv ℝ G q).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hG' : ContDiff ℝ ∞ G' :=
    (contDiff_infty_iff_fderiv.mp hG).2.clm_comp contDiff_const
  have hsection (x : E) : Continuous (fun t : ℝ => G (x, t)) :=
    hG.continuous.comp (continuous_const.prodMk continuous_id)
  have hsection' (x : E) : Continuous (fun t : ℝ => G' (x, t)) :=
    hG'.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨B, hB⟩ :=
    ((isCompact_closedBall x₀ 1).prod (isCompact_uIcc : IsCompact (uIcc a b)))
      .exists_bound_of_continuousOn hG'.continuous.continuousOn
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x t => G (x, t)) (F' := fun x t => G' (x, t))
    (μ := volume) (a := a) (b := b) (s := ball x₀ 1)
    (bound := fun _ : ℝ => B) (ball_mem_nhds x₀ zero_lt_one)
    (Filter.Eventually.of_forall fun x => (hsection x).aestronglyMeasurable)
    ((hsection x₀).intervalIntegrable a b)
    ((hsection' x₀).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ht x hx =>
      hB (x, t) ⟨ball_subset_closedBall hx, uIoc_subset_uIcc ht⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ x _ =>
      ((hG.differentiable (by simp)) (x, t)).hasFDerivAt.comp x
        (hasFDerivAt_prodMk_left x t))

private theorem contDiff_nat_intervalIntegral_of_contDiff (n : ℕ) (a b : ℝ) :
    ∀ {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      {G : E × ℝ → V}, ContDiff ℝ ∞ G →
      ContDiff ℝ n (fun x : E => ∫ t in a..b, G (x, t)) := by
  induction n with
  | zero =>
      intro V _ _ _ G hG
      apply contDiff_zero.mpr
      have hd : Differentiable ℝ (fun x : E => ∫ t in a..b, G (x, t)) :=
        fun x => (hasFDerivAt_intervalIntegral_of_contDiff hG a b x).differentiableAt
      exact hd.continuous
  | succ n ih =>
      intro V _ _ _ G hG
      let G' : E × ℝ → E →L[ℝ] V := fun q =>
        (fderiv ℝ G q).comp (ContinuousLinearMap.inl ℝ E ℝ)
      have hG' : ContDiff ℝ ∞ G' :=
        (contDiff_infty_iff_fderiv.mp hG).2.clm_comp contDiff_const
      have hnext : ContDiff ℝ ((n : ℕ∞ω) + 1)
          (fun x : E => ∫ t in a..b, G (x, t)) := by
        apply contDiff_succ_iff_hasFDerivAt.mpr
        exact ⟨fun x => ∫ t in a..b, G' (x, t), ih hG',
          hasFDerivAt_intervalIntegral_of_contDiff hG a b⟩
      simpa only [Nat.cast_add, Nat.cast_one] using hnext

/-- Integration over a fixed compact interval preserves smoothness in a
proper normed parameter space. -/
theorem contDiff_intervalIntegral_of_contDiff
    {G : E × ℝ → F} (hG : ContDiff ℝ ∞ G) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x : E => ∫ t in a..b, G (x, t)) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_nat_intervalIntegral_of_contDiff n a b hG

end ContinuousFlexibility.Analysis
