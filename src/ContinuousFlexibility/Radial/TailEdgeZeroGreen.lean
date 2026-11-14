module

public import ContinuousFlexibility.Radial.TailEdgeKernel

/-!
# The zero-potential Green solution on one edge

Splitting the kernel at the evaluation point gives two ordinary integrals.
Their actual derivatives prove the inhomogeneous Dirichlet equation and
the endpoint flux formulas.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory

private def tailEdgeLeftMoment (a : ℝ) (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in a..s, (t - a) * g t

private def tailEdgeRightMoment (b : ℝ) (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in s..b, (b - t) * g t

/-- The actual solution obtained by splitting the Dirichlet kernel integral. -/
def tailEdgeZeroSolve (a b : ℝ) (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  ((b - s) * tailEdgeLeftMoment a g s + (s - a) * tailEdgeRightMoment b g s) /
    (b - a)

private theorem hasDerivAt_tailEdgeLeftMoment {g : ℝ → ℝ} (hg : Continuous g) (a s : ℝ) :
    HasDerivAt (tailEdgeLeftMoment a g) ((s - a) * g s) s := by
  have hc : Continuous (fun t => (t - a) * g t) :=
    (continuous_id.sub continuous_const).mul hg
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a s)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

private theorem hasDerivAt_tailEdgeRightMoment {g : ℝ → ℝ} (hg : Continuous g) (b s : ℝ) :
    HasDerivAt (tailEdgeRightMoment b g) (-((b - s) * g s)) s := by
  have hc : Continuous (fun t => (b - t) * g t) :=
    (continuous_const.sub continuous_id).mul hg
  exact intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable s b)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- The two moving-boundary terms cancel in the first derivative. -/
theorem hasDerivAt_tailEdgeZeroSolve {g : ℝ → ℝ} (hg : Continuous g) (a b s : ℝ) :
    HasDerivAt (tailEdgeZeroSolve a b g)
      ((tailEdgeRightMoment b g s - tailEdgeLeftMoment a g s) / (b - a)) s := by
  have hL := ((hasDerivAt_const s b).sub (hasDerivAt_id s)).mul
    (hasDerivAt_tailEdgeLeftMoment hg a s)
  have hR := ((hasDerivAt_id s).sub (hasDerivAt_const s a)).mul
    (hasDerivAt_tailEdgeRightMoment hg b s)
  convert ((hL.add hR).div_const (b - a)) using 1
  · funext x
    rfl
  · simp only [Pi.sub_apply, id_eq]
    ring

theorem hasDerivAt_deriv_tailEdgeZeroSolve {g : ℝ → ℝ} (hg : Continuous g)
    {a b : ℝ} (hab : a < b) (s : ℝ) :
    HasDerivAt (deriv (tailEdgeZeroSolve a b g)) (-g s) s := by
  rw [show deriv (tailEdgeZeroSolve a b g) = _ from
    funext fun x => (hasDerivAt_tailEdgeZeroSolve hg a b x).deriv]
  have h := ((hasDerivAt_tailEdgeRightMoment hg b s).sub
    (hasDerivAt_tailEdgeLeftMoment hg a s)).div_const (b - a)
  convert h using 1
  field_simp [(sub_pos.mpr hab).ne']
  ring

theorem tailEdgeZeroSolve_endpoints (a b : ℝ) (g : ℝ → ℝ) :
    tailEdgeZeroSolve a b g a = 0 ∧ tailEdgeZeroSolve a b g b = 0 := by
  simp [tailEdgeZeroSolve, tailEdgeLeftMoment, tailEdgeRightMoment]

theorem tailEdgeZeroSolve_endpoint_deriv {g : ℝ → ℝ} (hg : Continuous g) (a b : ℝ) :
    deriv (tailEdgeZeroSolve a b g) a =
        (∫ t in a..b, (b - t) * g t) / (b - a) ∧
      deriv (tailEdgeZeroSolve a b g) b =
        -(∫ t in a..b, (t - a) * g t) / (b - a) := by
  simp only [(hasDerivAt_tailEdgeZeroSolve hg a b a).deriv,
    (hasDerivAt_tailEdgeZeroSolve hg a b b).deriv, tailEdgeLeftMoment, tailEdgeRightMoment,
    intervalIntegral.integral_same, sub_zero, zero_sub, and_self]

/-- The solution uses the pointwise Green function on the full closed edge. -/
theorem tailEdgeZeroSolve_eq_integral {g : ℝ → ℝ} (hg : Continuous g) {a b s : ℝ}
    (hs : s ∈ Icc a b) :
    tailEdgeZeroSolve a b g s = ∫ t in a..b, tailEdgeGreen a b s t * g t := by
  have hcont : Continuous (fun t => tailEdgeGreen a b s t * g t) := by
    unfold tailEdgeGreen
    exact ((((continuous_const.min continuous_id).sub continuous_const).mul
      (continuous_const.sub (continuous_const.max continuous_id))).div_const _).mul hg
  have hL : (∫ t in a..s, tailEdgeGreen a b s t * g t) =
      ((b - s) / (b - a)) * tailEdgeLeftMoment a g s := by
    rw [tailEdgeLeftMoment, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hs.1]
    intro t ht
    simp only [tailEdgeGreen, min_eq_right ht.2, max_eq_left ht.2]
    ring
  have hR : (∫ t in s..b, tailEdgeGreen a b s t * g t) =
      ((s - a) / (b - a)) * tailEdgeRightMoment b g s := by
    rw [tailEdgeRightMoment, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hs.2]
    intro t ht
    simp only [tailEdgeGreen, min_eq_left ht.1, max_eq_right ht.1]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable a s)
    (hcont.intervalIntegrable s b), hL, hR, tailEdgeZeroSolve]
  ring

end ContinuousFlexibility.Radial
