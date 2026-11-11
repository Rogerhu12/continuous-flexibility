import ContinuousFlexibility.Analysis.CanonicalCubicMixed

/-!
# Joint smoothness of compact parameter integrals

The integration variable ranges over a fixed compact interval.  A continuous
weight therefore preserves smooth dependence on the finite dimensional
cylinder parameter.  The proof differentiates once under the integral and
then applies the same statement to the Banach space of linear maps.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology Interval

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

private def compactParameterDifferential (g : PolarPoint × ℝ → G)
    (q : PolarPoint × ℝ) : PolarPoint →L[ℝ] G :=
  (fderiv ℝ g q).comp (ContinuousLinearMap.inl ℝ PolarPoint ℝ)

omit [CompleteSpace G] in
private theorem contDiff_compactParameterDifferential
    {g : PolarPoint × ℝ → G} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (compactParameterDifferential g) := by
  exact (contDiff_infty_iff_fderiv.mp hg).2.clm_comp contDiff_const

omit [CompleteSpace G] in
/-- The differential of an integral over a fixed compact interval is the
integral of the actual parameter differentials. -/
theorem hasFDerivAt_compact_parameterIntegral
    {w : ℝ → ℝ} {g : PolarPoint × ℝ → G}
    (hw : Continuous w) (hg : ContDiff ℝ ∞ g) (p : PolarPoint) :
    HasFDerivAt (fun x : PolarPoint => ∫ t in (0 : ℝ)..1, w t • g (x, t))
      (∫ t in (0 : ℝ)..1, w t • compactParameterDifferential g (p, t)) p := by
  have hg' : Continuous (compactParameterDifferential g) :=
    (contDiff_compactParameterDifferential hg).continuous
  have hsection (x : PolarPoint) :
      Continuous (fun t : ℝ => w t • g (x, t)) :=
    hw.smul (hg.continuous.comp (continuous_const.prodMk continuous_id))
  have hsection' (x : PolarPoint) :
      Continuous (fun t : ℝ => w t • compactParameterDifferential g (x, t)) :=
    hw.smul (hg'.comp (continuous_const.prodMk continuous_id))
  have hcont : Continuous (fun q : PolarPoint × ℝ =>
      w q.2 • compactParameterDifferential g q) :=
    (hw.comp continuous_snd).smul hg'
  have hcompact : IsCompact
      (Metric.closedBall p 1 ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall p 1).prod isCompact_Icc
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x t => w t • g (x, t))
    (F' := fun x t => w t • compactParameterDifferential g (x, t))
    (μ := volume) (a := 0) (b := 1) (s := Metric.ball p 1)
    (bound := fun _ : ℝ => B) (Metric.ball_mem_nhds p zero_lt_one)
    (Filter.Eventually.of_forall (fun x => (hsection x).aestronglyMeasurable))
    ((hsection p).intervalIntegrable 0 1)
    ((hsection' p).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun t ht x hx => by
      have ht' : t ∈ Icc (0 : ℝ) 1 :=
        Ioc_subset_Icc_self (by simpa only [uIoc_of_le zero_le_one] using ht)
      exact hB (x, t) ⟨Metric.ball_subset_closedBall hx, ht'⟩))
    intervalIntegrable_const
  exact Filter.Eventually.of_forall (fun t _ x _ =>
    (((hg.differentiable (by simp) (x, t)).hasFDerivAt).comp x
      (hasFDerivAt_prodMk_left x t)).const_smul (w t))

private theorem contDiff_nat_compact_parameterIntegral (n : ℕ) :
    ∀ {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      {w : ℝ → ℝ} {g : PolarPoint × ℝ → G},
      Continuous w → ContDiff ℝ ∞ g →
      ContDiff ℝ n (fun x : PolarPoint => ∫ t in (0 : ℝ)..1, w t • g (x, t)) := by
  induction n with
  | zero =>
      intro G _ _ _ w g hw hg
      have hd : Differentiable ℝ
          (fun x : PolarPoint => ∫ t in (0 : ℝ)..1, w t • g (x, t)) :=
        fun x => (hasFDerivAt_compact_parameterIntegral hw hg x).differentiableAt
      simpa only [Nat.cast_zero] using (contDiff_zero.mpr hd.continuous)
  | succ n ih =>
      intro G _ _ _ w g hw hg
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
        contDiff_succ_iff_fderiv]
      refine ⟨fun x => (hasFDerivAt_compact_parameterIntegral hw hg x).differentiableAt,
        by simp, ?_⟩
      have heq : fderiv ℝ
          (fun x : PolarPoint => ∫ t in (0 : ℝ)..1, w t • g (x, t)) =
          fun x => ∫ t in (0 : ℝ)..1, w t • compactParameterDifferential g (x, t) := by
        funext x
        exact (hasFDerivAt_compact_parameterIntegral hw hg x).fderiv
      rw [heq]
      exact ih hw (contDiff_compactParameterDifferential hg)

/-- Joint smoothness of an integral with a continuous scalar weight and
smooth integrand on the cylinder parameter and integration variable. -/
theorem contDiff_compact_parameterIntegral
    {w : ℝ → ℝ} {g : PolarPoint × ℝ → G}
    (hw : Continuous w) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x : PolarPoint => ∫ t in (0 : ℝ)..1, w t • g (x, t)) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_nat_compact_parameterIntegral n hw hg

/-- Joint smoothness is retained when only the radial coordinate is scaled
by the integration variable. -/
theorem contDiff_scaled_cylinderIntegral
    {w : ℝ → ℝ} {g : PolarPoint → ℝ}
    (hw : Continuous w) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun q : PolarPoint => ∫ t in (0 : ℝ)..1, w t * g (t * q.1, q.2)) := by
  have hmap : ContDiff ℝ ∞ (fun q : PolarPoint × ℝ => (q.2 * q.1.1, q.1.2)) :=
    (contDiff_snd.mul (contDiff_fst.fst)).prodMk contDiff_fst.snd
  exact contDiff_compact_parameterIntegral hw (hg.comp hmap)

end ContinuousFlexibility.Analysis
