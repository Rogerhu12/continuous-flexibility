import ContinuousFlexibility.Analysis.RootCompositionSmooth
import ContinuousFlexibility.Analysis.RootCompositionZeroOrder
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# The root chart within the nonnegative half-plane

The even and odd root formulas are smooth within x ≥ 0. Their prescribed
values on x < 0 need not be a smooth extension. Accordingly every
derivative and Jacobian in this file is taken within the nonnegative
half-plane. A positive odd coefficient gives a smooth radial rescaling,
an explicit nondegenerate boundary Jacobian, and a positive local collar.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- The physical side of a root boundary. -/
abbrev rootChartHalfPlane : Set (ℝ × ℝ) := Ici (0 : ℝ) ×ˢ univ

/-- The signed odd divided coefficient used by the root coordinate. -/
def rootOddCoefficient (G : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -rootOdd G p

/-- The radial factor converting the characteristic root to its
canonical normalization. -/
def rootRadialFactor (G : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (((3 : ℝ) / 2) * rootOddCoefficient G p) ^ (2 / 3 : ℝ)

/-- The canonical radial coordinate on the physical side. -/
def rootRadialCoordinate (G : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * rootRadialFactor G p

/-- The radial coordinate and the even angular coordinate. -/
def rootEvenOddChart (G : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (rootRadialCoordinate G p, rootEven G p)

/-- The actual determinant of the derivative within the physical side. -/
def rootChartJacobianWithin (G : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  let D := fderivWithin ℝ (rootEvenOddChart G) rootChartHalfPlane p
  (D (1, 0)).1 * (D (0, 1)).2 - (D (1, 0)).2 * (D (0, 1)).1

theorem uniqueDiffOn_rootChartHalfPlane : UniqueDiffOn ℝ rootChartHalfPlane :=
  (uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ

theorem rootOddCoefficient_zero (G : ℝ × ℝ × ℝ → ℝ) (θ : ℝ) :
    rootOddCoefficient G (0, θ) = -deriv (fun ζ => G (0, ζ, θ)) 0 := by
  rw [rootOddCoefficient, rootOdd_zero]

theorem contDiffOn_rootOddCoefficient {G : ℝ × ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) :
    ContDiffOn ℝ ∞ (rootOddCoefficient G) rootChartHalfPlane :=
  (contDiffOn_rootOdd hG).neg

/-- At a point where the odd coefficient is nonzero, the rescaled chart
is smooth within the physical half-plane. -/
theorem contDiffWithinAt_rootEvenOddChart
    {G : ℝ × ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    {p : ℝ × ℝ} (hp : p ∈ rootChartHalfPlane)
    (hχ : rootOddCoefficient G p ≠ 0) :
    ContDiffWithinAt ℝ ∞ (rootEvenOddChart G) rootChartHalfPlane p := by
  have hχsmooth := contDiffOn_rootOddCoefficient hG p hp
  have ha : ContDiffWithinAt ℝ ∞ (rootRadialFactor G) rootChartHalfPlane p :=
    (contDiffWithinAt_const.mul hχsmooth).rpow_const_of_ne
      (mul_ne_zero (by norm_num : (3 : ℝ) / 2 ≠ 0) hχ)
  exact (contDiffWithinAt_fst.mul ha).prodMk (contDiffOn_rootEven hG p hp)

theorem contDiffOn_rootEvenOddChart_positive
    {G : ℝ × ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiffOn ℝ ∞ (rootEvenOddChart G)
      (rootChartHalfPlane ∩ {p | 0 < rootOddCoefficient G p}) := by
  intro p hp
  exact (contDiffWithinAt_rootEvenOddChart hG hp.1 hp.2.ne').mono inter_subset_left

theorem rootRadialFactor_pos {G : ℝ × ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hχ : 0 < rootOddCoefficient G p) : 0 < rootRadialFactor G p :=
  Real.rpow_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) hχ) _

/-- At x = 0 the derivative of the radial factor is multiplied by zero.
Only its value contributes to the radial coordinate derivative. -/
theorem hasFDerivWithinAt_rootRadialCoordinate_zero
    {G : ℝ × ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (θ : ℝ)
    (hχ : rootOddCoefficient G (0, θ) ≠ 0) :
    HasFDerivWithinAt (rootRadialCoordinate G)
      (rootRadialFactor G (0, θ) • ContinuousLinearMap.fst ℝ ℝ ℝ)
      rootChartHalfPlane (0, θ) := by
  have hm : (0, θ) ∈ rootChartHalfPlane := (by simp [rootChartHalfPlane])
  have ha : ContDiffWithinAt ℝ ∞ (rootRadialFactor G) rootChartHalfPlane (0, θ) :=
    (contDiffWithinAt_const.mul (contDiffOn_rootOddCoefficient hG (0, θ) hm)).rpow_const_of_ne
      (mul_ne_zero (by norm_num : (3 : ℝ) / 2 ≠ 0) hχ)
  have hd := (ha.differentiableWithinAt (by simp)).hasFDerivWithinAt
  have hx : HasFDerivWithinAt
      (ContinuousLinearMap.fst ℝ ℝ ℝ : (ℝ × ℝ) → ℝ)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) rootChartHalfPlane (0, θ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.hasFDerivWithinAt
  simpa only [rootRadialCoordinate, ContinuousLinearMap.coe_fst', zero_smul, zero_add] using
    hx.fun_mul hd

theorem fderivWithin_rootRadialCoordinate_zero
    {G : ℝ × ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (θ : ℝ)
    (hχ : rootOddCoefficient G (0, θ) ≠ 0) :
    fderivWithin ℝ (rootRadialCoordinate G) rootChartHalfPlane (0, θ) =
      rootRadialFactor G (0, θ) • ContinuousLinearMap.fst ℝ ℝ ℝ :=
  (hasFDerivWithinAt_rootRadialCoordinate_zero hG θ hχ).fderivWithin
    (uniqueDiffOn_rootChartHalfPlane (0, θ) (by simp [rootChartHalfPlane]))

/-- The angular boundary derivative is the derivative of the prescribed
zero-section angular map, even though radial derivatives are one-sided. -/
theorem fderivWithin_rootEven_zero_angle
    {G : ℝ × ℝ × ℝ → ℝ} {hL : ℝ → ℝ} {θ a : ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ η : ℝ, G (0, 0, η) = hL η)
    (hLderiv : HasDerivAt hL a θ) :
    fderivWithin ℝ (rootEven G) rootChartHalfPlane (0, θ) (0, 1) = a := by
  have hm : (0, θ) ∈ rootChartHalfPlane := (by simp [rootChartHalfPlane])
  have hd := ((contDiffOn_rootEven hG (0, θ) hm).differentiableWithinAt
    (by simp)).hasFDerivWithinAt
  have hp : HasDerivAt (fun η : ℝ => ((0 : ℝ), η)) (0, 1) θ :=
    (hasDerivAt_const θ (0 : ℝ)).prodMk (hasDerivAt_id θ)
  have hc := hd.comp_hasDerivAt θ hp
    (Eventually.of_forall fun η => (show (0, η) ∈ rootChartHalfPlane from
      (by simp [rootChartHalfPlane])))
  have he : rootEven G ∘ (fun η : ℝ => ((0 : ℝ), η)) = hL := by
    funext η
    simp only [Function.comp_apply, rootEven_zero, hzero]
  rw [he] at hc
  exact hc.unique hLderiv

/-- The boundary determinant within the physical side is the radial
factor times the true angular boundary derivative. -/
theorem rootChartJacobianWithin_zero
    {G : ℝ × ℝ × ℝ → ℝ} {hL : ℝ → ℝ} {θ a : ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ η : ℝ, G (0, 0, η) = hL η)
    (hLderiv : HasDerivAt hL a θ)
    (hχ : rootOddCoefficient G (0, θ) ≠ 0) :
    rootChartJacobianWithin G (0, θ) = rootRadialFactor G (0, θ) * a := by
  have hm : (0, θ) ∈ rootChartHalfPlane := (by simp [rootChartHalfPlane])
  have hr := hasFDerivWithinAt_rootRadialCoordinate_zero hG θ hχ
  have ha := ((contDiffOn_rootEven hG (0, θ) hm).differentiableWithinAt
    (by simp)).hasFDerivWithinAt
  have hchart : HasFDerivWithinAt (rootEvenOddChart G)
      ((rootRadialFactor G (0, θ) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (fderivWithin ℝ (rootEven G) rootChartHalfPlane (0, θ)))
      rootChartHalfPlane (0, θ) := hr.prodMk ha
  have hD := hchart.fderivWithin (uniqueDiffOn_rootChartHalfPlane (0, θ) hm)
  have hang := fderivWithin_rootEven_zero_angle hG hzero hLderiv
  simp only [rootChartJacobianWithin, hD, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
    smul_eq_mul, mul_one, mul_zero, sub_zero, hang]

/-- A positive odd coefficient and positive angular derivative give an
actual neighborhood on the physical side where the chart Jacobian
remains positive. No assertion about the formula at negative x is made. -/
theorem exists_rootEvenOddChart_positive_collar
    {G : ℝ × ℝ × ℝ → ℝ} {hL : ℝ → ℝ} {θ a : ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ η : ℝ, G (0, 0, η) = hL η)
    (hLderiv : HasDerivAt hL a θ)
    (hχ : 0 < rootOddCoefficient G (0, θ)) (ha : 0 < a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ rootChartHalfPlane, dist p (0, θ) < δ →
      0 < rootOddCoefficient G p ∧ 0 < rootChartJacobianWithin G p := by
  have hm : (0, θ) ∈ rootChartHalfPlane := (by simp [rootChartHalfPlane])
  have hs := contDiffWithinAt_rootEvenOddChart hG hm hχ.ne'
  have hD : ContinuousWithinAt
      (fderivWithin ℝ (rootEvenOddChart G) rootChartHalfPlane)
      rootChartHalfPlane (0, θ) :=
    hs.continuousWithinAt_fderivWithin uniqueDiffOn_rootChartHalfPlane (by simp) hm
  have h1 : ContinuousWithinAt
      (fun p => fderivWithin ℝ (rootEvenOddChart G) rootChartHalfPlane p (1, 0))
      rootChartHalfPlane (0, θ) := hD.clm_apply continuousWithinAt_const
  have h2 : ContinuousWithinAt
      (fun p => fderivWithin ℝ (rootEvenOddChart G) rootChartHalfPlane p (0, 1))
      rootChartHalfPlane (0, θ) := hD.clm_apply continuousWithinAt_const
  have hJ : ContinuousWithinAt (rootChartJacobianWithin G) rootChartHalfPlane (0, θ) :=
    (h1.fst.mul h2.snd).sub (h1.snd.mul h2.fst)
  have hJ0 : 0 < rootChartJacobianWithin G (0, θ) := by
    rw [rootChartJacobianWithin_zero hG hzero hLderiv hχ.ne']
    exact mul_pos (rootRadialFactor_pos hχ) ha
  have hχevent : ∀ᶠ p in 𝓝[rootChartHalfPlane] (0, θ),
      0 < rootOddCoefficient G p :=
    (contDiffOn_rootOddCoefficient hG (0, θ) hm).continuousWithinAt.tendsto.eventually
      (Ioi_mem_nhds hχ)
  have hJevent : ∀ᶠ p in 𝓝[rootChartHalfPlane] (0, θ),
      0 < rootChartJacobianWithin G p :=
    hJ.tendsto.eventually (Ioi_mem_nhds hJ0)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp (hχevent.and hJevent)
  exact ⟨δ, hδ, fun p hp hdist => hδsub ⟨Metric.mem_ball.mpr hdist, hp⟩⟩

end ContinuousFlexibility.Analysis
