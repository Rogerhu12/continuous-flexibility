module

public import ContinuousFlexibility.Analysis.RootChartWithin
public import ContinuousFlexibility.Analysis.RootInverseParameterDerivative

/-!
# The actual inverse-flow root chart

The scalar function used in the even/odd root construction is the fixed
angular normalization composed with the actual inverse endpoint flow.
Its zero-section value and independent-root derivative come from the
ODE and the inverse identity. They give the exact boundary radial scale,
angular derivative, and positive Jacobian within the physical half-plane.

A smooth extension across that half-plane boundary is not asserted here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

/-- The actual normalized inverse flow, in the (x, ζ, θ) order expected
by the rootEven/rootOdd interface. -/
def rootInverseCoordinate
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) (hL : ℝ → ℝ) :
    ℝ × ℝ × ℝ → ℝ :=
  fun q => hL (parameterizedCircleInverse
    (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2) ((q.1, q.2.1), q.2.2))

/-- Joint smoothness follows from the genuine circle inverse theorem. -/
theorem contDiff_rootInverseCoordinate
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {T : ℝ} {hL : ℝ → ℝ}
    (hT : T ≠ 0)
    (hEndpoint : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2))
    (hpositive : ∀ p θ, 0 < deriv (fun η => Θ p 1 η) θ)
    (hperiod : ∀ p θ, Θ p 1 (θ + T) = Θ p 1 θ + T)
    (hhL : ContDiff ℝ ∞ hL) :
    ContDiff ℝ ∞ (rootInverseCoordinate Θ hL) := by
  have hI := contDiff_parameterizedCircleInverse hT hEndpoint
    (fun z => hpositive z.1 z.2) hperiod
  have hm : ContDiff ℝ ∞
      (fun q : ℝ × ℝ × ℝ => ((q.1, q.2.1), q.2.2)) :=
    (contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd
  exact hhL.comp (hI.comp hm)

/-- Both root components of the actual inverse coordinate are smooth
through every order within the nonnegative half-plane. -/
theorem contDiffOn_rootInverseCoordinate_parts
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {T : ℝ} {hL : ℝ → ℝ}
    (hT : T ≠ 0)
    (hEndpoint : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2))
    (hpositive : ∀ p θ, 0 < deriv (fun η => Θ p 1 η) θ)
    (hperiod : ∀ p θ, Θ p 1 (θ + T) = Θ p 1 θ + T)
    (hhL : ContDiff ℝ ∞ hL) :
    ContDiffOn ℝ ∞ (rootEven (rootInverseCoordinate Θ hL)) rootChartHalfPlane ∧
      ContDiffOn ℝ ∞ (rootOddCoefficient (rootInverseCoordinate Θ hL)) rootChartHalfPlane := by
  have hG := contDiff_rootInverseCoordinate hT hEndpoint hpositive hperiod hhL
  exact ⟨contDiffOn_rootEven hG, contDiffOn_rootOddCoefficient hG⟩

section ActualRootFlow

variable {d c₀ : ℝ × ℝ → ℝ}
  {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {T : ℝ} {hL : ℝ → ℝ}
  (hT : T ≠ 0) (hc₀ : ContDiff ℝ ∞ c₀)
  (hinit : ∀ p θ, Θ p 0 θ = θ)
  (hflow : ∀ p θ t, t ∈ Icc (0 : ℝ) 1 →
    HasDerivWithinAt (fun r => Θ p r θ)
      (2 * p.1 * t * d (p.1 * t ^ 2, Θ p t θ) +
        2 * p.2 * t ^ 2 * c₀ (p.1 * t ^ 2, Θ p t θ))
      (Icc (0 : ℝ) 1) t)
  (hΘ : ContinuousOn
    (fun q : ((ℝ × ℝ) × ℝ) × ℝ => Θ q.1.1 q.2 q.1.2)
    (univ ×ˢ Icc (0 : ℝ) 1))
  (hEndpoint : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2))
  (hpositive : ∀ p θ, 0 < deriv (fun η => Θ p 1 η) θ)
  (hperiod : ∀ p θ, Θ p 1 (θ + T) = Θ p 1 θ + T)
  (hhL : ContDiff ℝ ∞ hL)

include hT hinit hflow hEndpoint hperiod in
/-- The actual inverse coordinate has the prescribed angular value at
zero radial and independent-root parameters. -/
theorem rootInverseCoordinate_zero (θ : ℝ) :
    rootInverseCoordinate Θ hL (0, 0, θ) = hL θ := by
  have hr := parameterizedCircleInverse_right_inverse hT hEndpoint hperiod ((0, 0), θ)
  have hi : parameterizedCircleInverse
      (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2) ((0, 0), θ) = θ :=
    (rootRegularizedFlow_zero_parameters hinit hflow _
      (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)).symm.trans hr
  exact congrArg hL hi

include hT hc₀ hinit hflow hΘ hEndpoint hpositive hperiod hhL in
/-- The actual odd coefficient at the root is determined by the forced
variation of the constructed flow and its true inverse. -/
theorem rootOddCoefficient_rootInverseCoordinate_zero (θ : ℝ) :
    rootOddCoefficient (rootInverseCoordinate Θ hL) (0, θ) =
      ((2 : ℝ) / 3) * c₀ (0, θ) * deriv hL θ := by
  rw [rootOddCoefficient_zero]
  simpa only [rootInverseCoordinate] using
    rootRegularizedCoordinate_neg_deriv_rootParameter_zero
      hT hc₀ hinit hflow hΘ hEndpoint hpositive hperiod hhL θ

include hT hc₀ hinit hflow hΘ hEndpoint hpositive hperiod hhL in
theorem rootRadialFactor_rootInverseCoordinate_zero (θ : ℝ) :
    rootRadialFactor (rootInverseCoordinate Θ hL) (0, θ) =
      (c₀ (0, θ) * deriv hL θ) ^ (2 / 3 : ℝ) := by
  rw [rootRadialFactor, rootOddCoefficient_rootInverseCoordinate_zero
    hT hc₀ hinit hflow hΘ hEndpoint hpositive hperiod hhL θ]
  congr 1
  ring

include hT hc₀ hinit hflow hΘ hEndpoint hpositive hperiod hhL in
/-- The actual inverse-flow root chart is smooth from the physical side
and has the claimed three boundary derivative entries and Jacobian.
Strict positivity persists on an explicit local physical collar. -/
theorem rootInverseCoordinate_boundary_chart (θ : ℝ)
    (hcpos : 0 < c₀ (0, θ)) (hlpos : 0 < deriv hL θ) :
    ContDiffWithinAt ℝ ∞ (rootEvenOddChart (rootInverseCoordinate Θ hL))
        rootChartHalfPlane (0, θ) ∧
      fderivWithin ℝ (rootRadialCoordinate (rootInverseCoordinate Θ hL))
        rootChartHalfPlane (0, θ) (1, 0) =
          (c₀ (0, θ) * deriv hL θ) ^ (2 / 3 : ℝ) ∧
      fderivWithin ℝ (rootRadialCoordinate (rootInverseCoordinate Θ hL))
        rootChartHalfPlane (0, θ) (0, 1) = 0 ∧
      fderivWithin ℝ (rootEven (rootInverseCoordinate Θ hL))
        rootChartHalfPlane (0, θ) (0, 1) = deriv hL θ ∧
      rootChartJacobianWithin (rootInverseCoordinate Θ hL) (0, θ) =
        (c₀ (0, θ) * deriv hL θ) ^ (2 / 3 : ℝ) * deriv hL θ ∧
      0 < rootChartJacobianWithin (rootInverseCoordinate Θ hL) (0, θ) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ rootChartHalfPlane, dist p (0, θ) < δ →
        0 < rootOddCoefficient (rootInverseCoordinate Θ hL) p ∧
          0 < rootChartJacobianWithin (rootInverseCoordinate Θ hL) p := by
  let G := rootInverseCoordinate Θ hL
  have hG : ContDiff ℝ ∞ G :=
    contDiff_rootInverseCoordinate hT hEndpoint hpositive hperiod hhL
  have hzero : ∀ η : ℝ, G (0, 0, η) = hL η :=
    rootInverseCoordinate_zero hT hinit hflow hEndpoint hperiod
  have hdL : HasDerivAt hL (deriv hL θ) θ :=
    (hhL.differentiable (by simp) θ).hasDerivAt
  have hχ : 0 < rootOddCoefficient G (0, θ) := by
    rw [rootOddCoefficient_rootInverseCoordinate_zero
      hT hc₀ hinit hflow hΘ hEndpoint hpositive hperiod hhL θ]
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2 / 3) hcpos) hlpos
  have hξ : fderivWithin ℝ (rootRadialCoordinate G) rootChartHalfPlane (0, θ) =
      (c₀ (0, θ) * deriv hL θ) ^ (2 / 3 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ := by
    rw [fderivWithin_rootRadialCoordinate_zero hG θ hχ.ne',
      rootRadialFactor_rootInverseCoordinate_zero
        hT hc₀ hinit hflow hΘ hEndpoint hpositive hperiod hhL θ]
  have hJ : rootChartJacobianWithin G (0, θ) =
      (c₀ (0, θ) * deriv hL θ) ^ (2 / 3 : ℝ) * deriv hL θ := by
    rw [rootChartJacobianWithin_zero hG hzero hdL hχ.ne',
      rootRadialFactor_rootInverseCoordinate_zero
        hT hc₀ hinit hflow hΘ hEndpoint hpositive hperiod hhL θ]
  have hJpos : 0 < rootChartJacobianWithin G (0, θ) := by
    rw [hJ]
    exact mul_pos (Real.rpow_pos_of_pos (mul_pos hcpos hlpos) _) hlpos
  refine ⟨contDiffWithinAt_rootEvenOddChart hG (by simp [rootChartHalfPlane]) hχ.ne',
    ?_, ?_, fderivWithin_rootEven_zero_angle hG hzero hdL, hJ, hJpos,
    exists_rootEvenOddChart_positive_collar hG hzero hdL hχ hlpos⟩
  · rw [hξ]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
      smul_eq_mul, mul_one]
  · rw [hξ]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
      smul_eq_mul, mul_zero]

end ActualRootFlow
end ContinuousFlexibility.Analysis
