module

public import ContinuousFlexibility.Analysis.RootChartExtension
public import ContinuousFlexibility.Analysis.RootChartSymmetry
public import ContinuousFlexibility.Scalar.FormPullback

/-!
# The genuine extended root chart has a positive ordinary Jacobian

The fixed Seeley extension agrees with the root formulas on the physical
half-plane. Its ordinary derivative there is therefore the computed
within derivative. At the boundary this gives the exact determinant.
Continuity of the extended coefficient and ordinary Jacobian then gives
a genuine two-sided collar. No regularity of the unextended formula at
negative radial coordinates is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- The extended chart is smooth on either side of the boundary wherever
its actual extended odd coefficient is nonzero. -/
theorem contDiffAt_extendedRootEvenOddChart_of_ne_zero
    {G : ℝ × ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) {T : ℝ} (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T)
    (hφperiod : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T)
    {p : ℝ × ℝ} (hχ : extendedRootOddCoefficient G p ≠ 0) :
    ContDiffAt ℝ ∞ (extendedRootEvenOddChart G) p := by
  have hs : ContDiffAt ℝ ∞ (extendedRootRadialFactor G) p :=
    (contDiffAt_const.mul
      (contDiff_extendedRootOddCoefficient hG hT hχperiod).contDiffAt).rpow_const_of_ne
        (mul_ne_zero (by norm_num : (3 : ℝ) / 2 ≠ 0) hχ)
  exact (contDiffAt_fst.mul hs).prodMk
    (contDiff_extendedRootEven hG hT hφperiod).contDiffAt

/-- On the physical side the ordinary determinant of the extension is
the determinant of the actual within derivative of the root formula. -/
theorem planeJacobian_extendedRootEvenOddChart_eq_within
    {G : ℝ × ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) {T : ℝ} (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T)
    (hφperiod : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T)
    {p : ℝ × ℝ} (hp : p ∈ rootChartHalfPlane) (hχ : rootOddCoefficient G p ≠ 0) :
    planeJacobian (extendedRootEvenOddChart G) p = rootChartJacobianWithin G p := by
  simp only [planeJacobian, rootChartJacobianWithin,
    fderiv_extendedRootEvenOddChart_eq_within hG hT hχperiod hφperiod hp hχ]

/-- The whole ordinary derivative at the root has the prescribed radial
row and the true within angular row. -/
theorem fderiv_extendedRootEvenOddChart_zero
    {G : ℝ × ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) {T : ℝ} (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T)
    (hφperiod : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T)
    (θ : ℝ) (hχ : rootOddCoefficient G (0, θ) ≠ 0) :
    fderiv ℝ (extendedRootEvenOddChart G) (0, θ) =
      (rootRadialFactor G (0, θ) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (fderivWithin ℝ (rootEven G) rootChartHalfPlane (0, θ)) := by
  have hm : (0, θ) ∈ rootChartHalfPlane := (by simp [rootChartHalfPlane])
  rw [fderiv_extendedRootEvenOddChart_eq_within hG hT hχperiod hφperiod hm hχ]
  have hr := hasFDerivWithinAt_rootRadialCoordinate_zero hG θ hχ
  have ha := ((contDiffOn_rootEven hG (0, θ) hm).differentiableWithinAt
    (by simp)).hasFDerivWithinAt
  exact (hr.prodMk ha).fderivWithin (uniqueDiffOn_rootChartHalfPlane (0, θ) hm)

theorem planeJacobian_extendedRootEvenOddChart_zero
    {G : ℝ × ℝ × ℝ → ℝ} {hL : ℝ → ℝ} {θ a T : ℝ}
    (hG : ContDiff ℝ ∞ G) (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun η => rootOddCoefficient G (r, η)) T)
    (hφperiod : ∀ r, 0 ≤ r → ∀ η, rootEven G (r, η + T) = rootEven G (r, η) + T)
    (hzero : ∀ η : ℝ, G (0, 0, η) = hL η)
    (hLderiv : HasDerivAt hL a θ) (hχ : rootOddCoefficient G (0, θ) ≠ 0) :
    planeJacobian (extendedRootEvenOddChart G) (0, θ) = rootRadialFactor G (0, θ) * a := by
  rw [planeJacobian_extendedRootEvenOddChart_eq_within hG hT hχperiod hφperiod
    (show (0, θ) ∈ rootChartHalfPlane from (by simp [rootChartHalfPlane])) hχ,
    rootChartJacobianWithin_zero hG hzero hLderiv hχ]

/-- Positivity at the root extends to a true ball, including negative
radial coordinates of the genuine smooth extension. -/
theorem exists_extendedRootEvenOddChart_positive_collar
    {G : ℝ × ℝ × ℝ → ℝ} {hL : ℝ → ℝ} {θ a T : ℝ}
    (hG : ContDiff ℝ ∞ G) (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun η => rootOddCoefficient G (r, η)) T)
    (hφperiod : ∀ r, 0 ≤ r → ∀ η, rootEven G (r, η + T) = rootEven G (r, η) + T)
    (hzero : ∀ η : ℝ, G (0, 0, η) = hL η)
    (hLderiv : HasDerivAt hL a θ)
    (hχ : 0 < rootOddCoefficient G (0, θ)) (ha : 0 < a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ × ℝ, dist p (0, θ) < δ →
      ContDiffAt ℝ ∞ (extendedRootEvenOddChart G) p ∧
        0 < extendedRootOddCoefficient G p ∧
        0 < planeJacobian (extendedRootEvenOddChart G) p := by
  have heχ : 0 < extendedRootOddCoefficient G (0, θ) := by
    rwa [extendedRootOddCoefficient_of_nonneg G (le_refl (0 : ℝ))]
  have hs := contDiffAt_extendedRootEvenOddChart_of_ne_zero
    hG hT hχperiod hφperiod heχ.ne'
  have hD := hs.continuousAt_fderiv (by simp)
  have h1 : ContinuousAt
      (fun p => fderiv ℝ (extendedRootEvenOddChart G) p (1, 0)) (0, θ) :=
    hD.clm_apply continuousAt_const
  have h2 : ContinuousAt
      (fun p => fderiv ℝ (extendedRootEvenOddChart G) p (0, 1)) (0, θ) :=
    hD.clm_apply continuousAt_const
  have hJ : ContinuousAt (planeJacobian (extendedRootEvenOddChart G)) (0, θ) :=
    (h1.fst.mul h2.snd).sub (h1.snd.mul h2.fst)
  have hJ0 : 0 < planeJacobian (extendedRootEvenOddChart G) (0, θ) := by
    rw [planeJacobian_extendedRootEvenOddChart_zero hG hT hχperiod hφperiod
      hzero hLderiv hχ.ne']
    exact mul_pos (rootRadialFactor_pos hχ) ha
  have hχevent : ∀ᶠ p in 𝓝 (0, θ), 0 < extendedRootOddCoefficient G p :=
    (contDiff_extendedRootOddCoefficient hG hT hχperiod).continuous.continuousAt.tendsto.eventually
      (Ioi_mem_nhds heχ)
  have hJevent : ∀ᶠ p in 𝓝 (0, θ),
      0 < planeJacobian (extendedRootEvenOddChart G) p :=
    hJ.tendsto.eventually (Ioi_mem_nhds hJ0)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (hχevent.and hJevent)
  refine ⟨δ, hδ, ?_⟩
  intro p hp
  have hpos := hsub (Metric.mem_ball.mpr hp)
  exact ⟨contDiffAt_extendedRootEvenOddChart_of_ne_zero
    hG hT hχperiod hφperiod hpos.1.ne', hpos.1, hpos.2⟩

/-- The actual normalized inverse flow therefore gives a genuinely
smooth boundary chart with the explicit positive ordinary Jacobian. -/
theorem rootInverseCoordinate_boundary_extension
    {d c₀ : ℝ × ℝ → ℝ} {T : ℝ} {hL : ℝ → ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
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
    (hLperiod : ∀ θ, hL (θ + T) = hL θ + T)
    (θ : ℝ) (hcpos : 0 < c₀ (0, θ)) (hlpos : 0 < deriv hL θ) :
    ContDiffAt ℝ ∞ (extendedRootEvenOddChart (rootInverseCoordinate Θ hL)) (0, θ) ∧
      planeJacobian (extendedRootEvenOddChart (rootInverseCoordinate Θ hL)) (0, θ) =
        (c₀ (0, θ) * deriv hL θ) ^ (2 / 3 : ℝ) * deriv hL θ ∧
      0 < planeJacobian (extendedRootEvenOddChart (rootInverseCoordinate Θ hL)) (0, θ) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℝ × ℝ, dist p (0, θ) < δ →
        ContDiffAt ℝ ∞ (extendedRootEvenOddChart (rootInverseCoordinate Θ hL)) p ∧
          0 < extendedRootOddCoefficient (rootInverseCoordinate Θ hL) p ∧
          0 < planeJacobian (extendedRootEvenOddChart (rootInverseCoordinate Θ hL)) p := by
  let G := rootInverseCoordinate Θ hL
  have hG : ContDiff ℝ ∞ G :=
    contDiff_rootInverseCoordinate hT hEndpoint hpositive hperiod hhL
  have hGperiod : ∀ x ζ η, G (x, ζ, η + T) = G (x, ζ, η) + T :=
    rootInverseCoordinate_period_add hT hEndpoint hpositive hperiod hLperiod
  have hχperiod : ∀ r, 0 ≤ r →
      Function.Periodic (fun η => rootOddCoefficient G (r, η)) T :=
    fun r _ => rootOddCoefficient_periodic hGperiod r
  have hφperiod : ∀ r, 0 ≤ r → ∀ η,
      rootEven G (r, η + T) = rootEven G (r, η) + T :=
    fun r _ => rootEven_period_add hGperiod r
  have hzero : ∀ η : ℝ, G (0, 0, η) = hL η :=
    rootInverseCoordinate_zero hT hinit hflow hEndpoint hperiod
  have hdL : HasDerivAt hL (deriv hL θ) θ :=
    (hhL.differentiable (by simp) θ).hasDerivAt
  have hχ : 0 < rootOddCoefficient G (0, θ) := by
    rw [rootOddCoefficient_rootInverseCoordinate_zero
      hT hc₀ hinit hflow hΘ hEndpoint hpositive hperiod hhL θ]
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2 / 3) hcpos) hlpos
  have hJ : planeJacobian (extendedRootEvenOddChart G) (0, θ) =
      (c₀ (0, θ) * deriv hL θ) ^ (2 / 3 : ℝ) * deriv hL θ := by
    rw [planeJacobian_extendedRootEvenOddChart_zero hG hT hχperiod hφperiod
      hzero hdL hχ.ne', rootRadialFactor_rootInverseCoordinate_zero
        hT hc₀ hinit hflow hΘ hEndpoint hpositive hperiod hhL θ]
  have hJpos : 0 < planeJacobian (extendedRootEvenOddChart G) (0, θ) := by
    rw [hJ]
    exact mul_pos (Real.rpow_pos_of_pos (mul_pos hcpos hlpos) _) hlpos
  exact ⟨contDiffAt_extendedRootEvenOddChart hG hT hχperiod hφperiod
      (by simp [rootChartHalfPlane]) hχ.ne', hJ, hJpos,
    exists_extendedRootEvenOddChart_positive_collar
      hG hT hχperiod hφperiod hzero hdL hχ hlpos⟩

end ContinuousFlexibility.Analysis
