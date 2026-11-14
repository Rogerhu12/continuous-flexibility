module

public import ContinuousFlexibility.Analysis.RootChartExtensionGeometry
public import ContinuousFlexibility.Analysis.PeriodicGermCollar
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# A uniform collar for a periodic root chart

Local neighborhoods of the boundary axis reduce to one compact angular
period. A positive thickening of that compact set gives one radial
radius valid at every angle. This compactness argument has no asserted
uniformity over additional states or over distinct root components.

Applied to the genuine smooth extension, it gives an ordinary smooth
chart with positive Jacobian on a full two-sided periodic collar.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- A fixed translation of the output does not change the actual
derivative, so derivatives of degree-one lifts are angular-periodic. -/
theorem fderiv_periodic_lift_snd
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : P × ℝ → E} {T : ℝ} {c : E}
    (hperiod : ∀ p θ, F (p, θ + T) = F (p, θ) + c) (p : P) :
    Function.Periodic (fun θ => fderiv ℝ F (p, θ)) T := by
  have he : (fun x : P × ℝ => F (x + ((0 : P), T))) =
      (fun x : P × ℝ => F x + c) := by
    funext x
    rcases x with ⟨q, θ⟩
    simpa only [Prod.mk_add_mk, add_zero] using hperiod q θ
  intro θ
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := (p, θ)) ((0 : P), T)
  rw [he, fderiv_add_const] at hd
  simpa only [Prod.mk_add_mk, add_zero] using hd.symm

theorem planeJacobian_periodic_snd {F : (ℝ × ℝ) → ℝ × ℝ} {T : ℝ}
    (hperiod : ∀ r θ, F (r, θ + T) = F (r, θ) + (0, T)) (r : ℝ) :
    Function.Periodic (fun θ => planeJacobian F (r, θ)) T := by
  intro θ
  simp only [planeJacobian, fderiv_periodic_lift_snd hperiod r θ]

/-- Positive root coefficient and positive boundary angular derivative
give one genuine smooth collar for every angle of the periodic chart. -/
theorem exists_extendedRootEvenOddChart_uniform_positive_collar
    {G : ℝ × ℝ × ℝ → ℝ} {hL : ℝ → ℝ} {T : ℝ}
    (hG : ContDiff ℝ ∞ G) (hT : T ≠ 0)
    (hχperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) T)
    (hφperiod : ∀ r, 0 ≤ r → ∀ θ, rootEven G (r, θ + T) = rootEven G (r, θ) + T)
    (hzero : ∀ θ : ℝ, G (0, 0, θ) = hL θ)
    (hhL : ContDiff ℝ ∞ hL)
    (hχ : ∀ θ : ℝ, 0 < rootOddCoefficient G (0, θ))
    (hLpos : ∀ θ : ℝ, 0 < deriv hL θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r θ : ℝ, |r| < δ →
      ContDiffAt ℝ ∞ (extendedRootEvenOddChart G) (r, θ) ∧
        0 < extendedRootOddCoefficient G (r, θ) ∧
        0 < planeJacobian (extendedRootEvenOddChart G) (r, θ) := by
  have hχe : ∀ r, Function.Periodic
      (fun θ => extendedRootOddCoefficient G (r, θ)) T :=
    fun r => seeleyPeriodicExtension_periodic hχperiod r
  have hJe : ∀ r, Function.Periodic
      (fun θ => planeJacobian (extendedRootEvenOddChart G) (r, θ)) T :=
    planeJacobian_periodic_snd (extendedRootEvenOddChart_period hχperiod hφperiod)
  obtain ⟨δ, hδ, hb⟩ := exists_uniform_periodic_collar_of_local
    (Q := fun p => 0 < extendedRootOddCoefficient G p ∧
      0 < planeJacobian (extendedRootEvenOddChart G) p) hT
    (fun r θ => by simp only [hχe r θ, hJe r θ])
    (fun θ => by
      obtain ⟨ε, hε, hlocal⟩ := exists_extendedRootEvenOddChart_positive_collar
        hG hT hχperiod hφperiod hzero
        (hhL.differentiable (by simp) θ).hasDerivAt (hχ θ) (hLpos θ)
      exact Metric.mem_nhds_iff.mpr
        ⟨ε, hε, fun p hp => (hlocal p (Metric.mem_ball.mp hp)).2⟩)
  refine ⟨δ, hδ, ?_⟩
  intro r θ hr
  have hpos := hb r θ hr
  exact ⟨contDiffAt_extendedRootEvenOddChart_of_ne_zero
    hG hT hχperiod hφperiod hpos.1.ne', hpos.1, hpos.2⟩

/-- The true inverse root flow and its computed boundary coefficient
supply every hypothesis of the uniform periodic-collar construction. -/
theorem exists_rootInverseCoordinate_uniform_positive_collar
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
    (hcpos : ∀ θ, 0 < c₀ (0, θ)) (hlpos : ∀ θ, 0 < deriv hL θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r θ : ℝ, |r| < δ →
      ContDiffAt ℝ ∞ (extendedRootEvenOddChart (rootInverseCoordinate Θ hL)) (r, θ) ∧
        0 < extendedRootOddCoefficient (rootInverseCoordinate Θ hL) (r, θ) ∧
        0 < planeJacobian (extendedRootEvenOddChart (rootInverseCoordinate Θ hL)) (r, θ) := by
  let G := rootInverseCoordinate Θ hL
  have hG : ContDiff ℝ ∞ G :=
    contDiff_rootInverseCoordinate hT hEndpoint hpositive hperiod hhL
  have hGperiod : ∀ x ζ θ, G (x, ζ, θ + T) = G (x, ζ, θ) + T :=
    rootInverseCoordinate_period_add hT hEndpoint hpositive hperiod hLperiod
  have hχ : ∀ θ : ℝ, 0 < rootOddCoefficient G (0, θ) := by
    intro θ
    rw [rootOddCoefficient_rootInverseCoordinate_zero
      hT hc₀ hinit hflow hΘ hEndpoint hpositive hperiod hhL θ]
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2 / 3) (hcpos θ)) (hlpos θ)
  exact exists_extendedRootEvenOddChart_uniform_positive_collar hG hT
    (fun r _ => rootOddCoefficient_periodic hGperiod r)
    (fun r _ => rootEven_period_add hGperiod r)
    (rootInverseCoordinate_zero hT hinit hflow hEndpoint hperiod)
    hhL hχ hlpos

end ContinuousFlexibility.Analysis
