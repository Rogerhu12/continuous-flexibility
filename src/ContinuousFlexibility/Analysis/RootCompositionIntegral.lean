module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Order.Compact

/-!
# Smooth dependence of a compact interval integral

Jointly smooth integrands can be integrated over a fixed compact interval.
The parameter space is proper, so a continuous derivative is uniformly
bounded on a compact parameter neighborhood times the integration interval.
This supplies the local domination needed for differentiation under the
integral.  Finite-order induction then gives smoothness of every order.
-/

@[expose] public section

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
  have hc : IsCompact (closedBall x₀ 1 ×ˢ uIcc a b) :=
    (isCompact_closedBall x₀ 1).prod isCompact_uIcc
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn hG'.continuous.continuousOn
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

/-- Restricting the first derivative to the parameter factor cannot
increase the norm of any higher jet. -/
theorem norm_iteratedFDeriv_paramDerivative_le
    {G : E × ℝ → F} (hG : ContDiff ℝ ∞ G) (n : ℕ) (q : E × ℝ) :
    ‖iteratedFDeriv ℝ n
      (fun q : E × ℝ => (fderiv ℝ G q).comp (ContinuousLinearMap.inl ℝ E ℝ)) q‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) G q‖ := by
  let T : ((E × ℝ) →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
    (ContinuousLinearMap.compL ℝ E (E × ℝ) F).flip (ContinuousLinearMap.inl ℝ E ℝ)
  have hT : ‖T‖ ≤ 1 := by
    have hc : ‖(ContinuousLinearMap.compL ℝ E (E × ℝ) F).flip‖ ≤ 1 := by
      simpa only [ContinuousLinearMap.opNorm_flip] using
        (ContinuousLinearMap.norm_compL_le (𝕜 := ℝ) (E := E) (Fₗ := E × ℝ) (Gₗ := F))
    calc
      ‖T‖ ≤ ‖(ContinuousLinearMap.compL ℝ E (E × ℝ) F).flip‖ *
          ‖ContinuousLinearMap.inl ℝ E ℝ‖ :=
        (ContinuousLinearMap.compL ℝ E (E × ℝ) F).flip.le_opNorm _
      _ ≤ 1 * ‖ContinuousLinearMap.inl ℝ E ℝ‖ :=
        mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ 1 := by
        simpa only [one_mul] using
          (ContinuousLinearMap.norm_inl_le_one (𝕜 := ℝ) (E := E) (F := ℝ))
  have hder : ContDiff ℝ ∞ (fderiv ℝ G) := (contDiff_infty_iff_fderiv.mp hG).2
  have heq : T ∘ fderiv ℝ G =
      (fun q : E × ℝ => (fderiv ℝ G q).comp (ContinuousLinearMap.inl ℝ E ℝ)) := by
    ext q v
    simp only [T, Function.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.compL_apply]
  have h := T.norm_iteratedFDeriv_comp_left (x := q) (n := n) hder.contDiffAt (by simp)
  rw [heq] at h
  calc
    _ ≤ ‖T‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ G) q‖ := h
    _ ≤ 1 * ‖iteratedFDeriv ℝ n (fderiv ℝ G) q‖ :=
      mul_le_mul_of_nonneg_right hT (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (n + 1) G q‖ := by
      rw [one_mul, norm_iteratedFDeriv_fderiv]

private theorem norm_iteratedFDeriv_intervalIntegral_le_aux
    (n : ℕ) (a b : ℝ) (x : E) (B : ℝ) :
    ∀ {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      {G : E × ℝ → V}, ContDiff ℝ ∞ G →
      (∀ t ∈ uIcc a b, ‖iteratedFDeriv ℝ n G (x, t)‖ ≤ B) →
      ‖iteratedFDeriv ℝ n (fun y : E => ∫ t in a..b, G (y, t)) x‖ ≤ B * |b - a| := by
  induction n with
  | zero =>
      intro V _ _ _ G _ hB
      rw [norm_iteratedFDeriv_zero]
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      simpa only [norm_iteratedFDeriv_zero] using hB t (uIoc_subset_uIcc ht)
  | succ n ih =>
      intro V _ _ _ G hG hB
      let G' : E × ℝ → E →L[ℝ] V := fun q =>
        (fderiv ℝ G q).comp (ContinuousLinearMap.inl ℝ E ℝ)
      have hG' : ContDiff ℝ ∞ G' :=
        (contDiff_infty_iff_fderiv.mp hG).2.clm_comp contDiff_const
      have hfd : fderiv ℝ (fun y : E => ∫ t in a..b, G (y, t)) =
          (fun y : E => ∫ t in a..b, G' (y, t)) := by
        funext y
        exact (hasFDerivAt_intervalIntegral_of_contDiff hG a b y).fderiv
      rw [← norm_iteratedFDeriv_fderiv, hfd]
      apply ih hG'
      intro t ht
      exact (norm_iteratedFDeriv_paramDerivative_le hG n (x, t)).trans (hB t ht)

/-- Uniform bounds for a joint jet of an integrand give the same-order
bound for its parameter integral, with only the interval length as a factor. -/
theorem norm_iteratedFDeriv_intervalIntegral_le
    {G : E × ℝ → F} (hG : ContDiff ℝ ∞ G) (n : ℕ) (a b : ℝ) (x : E) (B : ℝ)
    (hB : ∀ t ∈ uIcc a b, ‖iteratedFDeriv ℝ n G (x, t)‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y : E => ∫ t in a..b, G (y, t)) x‖ ≤ B * |b - a| :=
  norm_iteratedFDeriv_intervalIntegral_le_aux n a b x B hG hB

end ContinuousFlexibility.Analysis
