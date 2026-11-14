import ContinuousFlexibility.Analysis.ScalarSpatialRegularity
import ContinuousFlexibility.Analysis.OneHighCircleFlowIntegral

/-!
# Compact integration with only continuous time dependence

The existing compact-parameter derivative theorem is applied to the true
one-dimensional spatial derivative. Induction then preserves every finite
spatial order while allowing a merely continuous time variable.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem hasDerivAt_scalar_parametric_intervalIntegral
    {f g : PolarPoint → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ x t : ℝ, HasDerivAt (fun y => f (y, t)) (g (x, t)) x)
    (a b x : ℝ) :
    HasDerivAt (fun y => ∫ t in a..b, f (y, t))
      (∫ t in a..b, g (x, t)) x := by
  let L : PolarPoint → ℝ →L[ℝ] ℝ := fun p =>
    ContinuousLinearMap.toSpanSingleton ℝ (g p)
  have hL : Continuous L :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.comp hg
  have hD (y t : ℝ) :
      HasFDerivAt (fun q => f (q, t)) (L (y, t)) y :=
    (hd y t).hasFDerivAt
  have hi := hasFDerivAt_parametric_intervalIntegral hf hL hD a b x
  have hsection : Continuous (fun t : ℝ => L (x, t)) :=
    hL.comp (continuous_const.prodMk continuous_id)
  have he : (∫ t in a..b, L (x, t)) 1 = ∫ t in a..b, g (x, t) := by
    rw [ContinuousLinearMap.intervalIntegral_apply
      (μ := volume) (hsection.intervalIntegrable (μ := volume) a b) (1 : ℝ)]
    simp only [L, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul]
  exact hi.hasDerivAt.congr_deriv he

/-- A moving time endpoint preserves finite spatial regularity. Its
dependence on time is proved only continuous, and is never differentiated. -/
theorem ScalarSpatialRegularity.primitive {n : ℕ} {f : PolarPoint → ℝ}
    (hf : ScalarSpatialRegularity n f) (a : ℝ) :
    ScalarSpatialRegularity n (fun p : PolarPoint => ∫ t in a..p.2, f (p.1, t)) := by
  induction n generalizing f with
  | zero =>
      exact (contDiff_parametric_primitive_nat
        (n := 0) (contDiff_zero.mpr hf.continuous) a).continuous
  | succ n ih =>
      have hc : Continuous (fun p : PolarPoint => ∫ t in a..p.2, f (p.1, t)) :=
        (contDiff_parametric_primitive_nat
          (n := 0) (contDiff_zero.mpr hf.continuous) a).continuous
      have hd (x t : ℝ) :
          HasDerivAt (fun y => ∫ r in a..t, f (y, r))
            (∫ r in a..t, scalarSpatialDerivative f (x, r)) x :=
        hasDerivAt_scalar_parametric_intervalIntegral hf.1 hf.2.2.continuous
          (fun y r => (hf.2.1 y r).hasDerivAt) a t x
      refine ⟨hc, fun x t => (hd x t).differentiableAt, ?_⟩
      have he : scalarSpatialDerivative
          (fun p : PolarPoint => ∫ t in a..p.2, f (p.1, t)) =
          fun p : PolarPoint => ∫ t in a..p.2, scalarSpatialDerivative f (p.1, t) := by
        funext p
        exact (hd p.1 p.2).deriv
      rw [he]
      exact ih hf.2.2

end ContinuousFlexibility.Analysis
