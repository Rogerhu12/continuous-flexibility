module

public import ContinuousFlexibility.Analysis.N04bActualRootCoordinates
public import ContinuousFlexibility.Analysis.RootUniformCollar
public import ContinuousFlexibility.Analysis.RootSmoothHeight
public import ContinuousFlexibility.Analysis.SeeleyRootReflection

/-!
# Boundary geometry of the genuinely constructed root coordinate

The actual root-flow output supplies every hypothesis of the existing
Seeley extension and height construction. Compactness of one period
gives a single two-sided collar on which the coefficient, Jacobian,
angular coordinate derivative and angular-product denominator are all
positive. The angular derivative is included explicitly for the true
collar inverse construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

namespace N04bRootCoordinateProperties

variable {d c₀ : PolarPoint → ℝ} {hL : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
  {R σ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
  (H : N04bRootCoordinateProperties d c₀ hL Φ R σ G)

include H

theorem odd_period (r : ℝ) :
    Function.Periodic (fun θ => rootOddCoefficient G (r, θ)) Real.pi :=
  rootOddCoefficient_periodic H.period r

theorem even_period (r θ : ℝ) :
    rootEven G (r, θ + Real.pi) = rootEven G (r, θ) + Real.pi :=
  rootEven_period_add H.period r θ

theorem extended_chart_period (r θ : ℝ) :
    extendedRootEvenOddChart G (r, θ + Real.pi) =
      extendedRootEvenOddChart G (r, θ) + (0, Real.pi) :=
  extendedRootEvenOddChart_period (fun r _ => H.odd_period r)
    (fun r _ => H.even_period r) r θ

theorem extended_even_period (r θ : ℝ) :
    extendedRootEven G (r, θ + Real.pi) = extendedRootEven G (r, θ) + Real.pi :=
  congrArg Prod.snd (H.extended_chart_period r θ)

theorem extended_odd_period (r : ℝ) :
    Function.Periodic (fun θ => extendedRootOddCoefficient G (r, θ)) Real.pi :=
  seeleyPeriodicExtension_periodic (fun r _ => H.odd_period r) r

/-- The extended chart maps the whole physical root axis to its actual
angular label on the zero canonical axis. -/
theorem extended_chart_zero (θ : ℝ) :
    extendedRootEvenOddChart G (0, θ) = (0, hL θ) := by
  apply Prod.ext
  · simp only [extendedRootEvenOddChart, extendedRootRadialCoordinate, zero_mul]
  · change extendedRootEven G (0, θ) = hL θ
    rw [extendedRootEven_of_nonneg G (le_refl (0 : ℝ)), rootEven_zero, H.zero_section]

theorem extended_chart_reflection (r θ : ℝ) :
    extendedRootEvenOddChart G (r, -θ) =
      ((extendedRootEvenOddChart G (r, θ)).1,
        -(extendedRootEvenOddChart G (r, θ)).2) :=
  extendedRootEvenOddChart_reflect
    (fun r _ => rootOddCoefficient_reflect H.smooth H.reflection r)
    (fun r _ => rootEven_reflect H.reflection r) r θ

theorem extended_angle_derivative_period (r : ℝ) :
    Function.Periodic (fun θ => angularPartial (extendedRootEven G) (r, θ)) Real.pi := by
  intro θ
  exact congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1))
    (fderiv_periodic_lift_snd H.extended_even_period r θ)

theorem angularProduct_period (r : ℝ) :
    Function.Periodic (fun θ => rootAngularProduct G (r, θ)) Real.pi := by
  have hχ : ∀ r θ, extendedRootOddCoefficient G (r, θ + Real.pi) =
      extendedRootOddCoefficient G (r, θ) + (0 : ℝ) := by
    intro r θ
    simpa only [add_zero] using H.extended_odd_period r θ
  intro θ
  simp only [rootAngularProduct, angularPartial,
    fderiv_periodic_lift_snd H.extended_even_period r θ,
    fderiv_periodic_lift_snd hχ r θ]

/-- The true ordinary Jacobian at the root has the expected positive
scale, derived from the actual divided odd coefficient. -/
theorem boundary_jacobian (θ : ℝ) :
    planeJacobian (extendedRootEvenOddChart G) (0, θ) =
        (c₀ (0, θ) * deriv hL θ) ^ (2 / 3 : ℝ) * deriv hL θ ∧
      0 < planeJacobian (extendedRootEvenOddChart G) (0, θ) := by
  have hj := planeJacobian_extendedRootEvenOddChart_zero H.smooth Real.pi_ne_zero
    (fun r _ => H.odd_period r) (fun r _ => H.even_period r) H.zero_section
    (H.label_smooth.differentiable (by simp) θ).hasDerivAt (H.odd_positive θ).ne'
  have hr : rootRadialFactor G (0, θ) =
      (c₀ (0, θ) * deriv hL θ) ^ (2 / 3 : ℝ) := by
    rw [rootRadialFactor, H.odd_zero θ]
    congr 1
    ring
  refine ⟨by simpa only [hr] using hj, ?_⟩
  rw [hj]
  exact mul_pos (rootRadialFactor_pos (H.odd_positive θ)) (H.label_positive θ)

/-- One actual two-sided collar works for every angle and includes the
positive angular derivative required by the genuine collar inverse. -/
theorem exists_uniform_positive_geometry :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r θ : ℝ, |r| < δ →
      ContDiffAt ℝ ∞ (extendedRootEvenOddChart G) (r, θ) ∧
        0 < extendedRootOddCoefficient G (r, θ) ∧
        0 < planeJacobian (extendedRootEvenOddChart G) (r, θ) ∧
        0 < angularPartial (extendedRootEven G) (r, θ) ∧
        0 < rootAngularProduct G (r, θ) := by
  obtain ⟨δ₁, hδ₁, hchart⟩ :=
    exists_extendedRootEvenOddChart_uniform_positive_collar H.smooth Real.pi_ne_zero
      (fun r _ => H.odd_period r) (fun r _ => H.even_period r) H.zero_section
      H.label_smooth H.odd_positive H.label_positive
  have hφ : ContDiff ℝ ∞ (extendedRootEven G) :=
    contDiff_extendedRootEven H.smooth Real.pi_ne_zero (fun r _ => H.even_period r)
  have hφθ : Continuous (angularPartial (extendedRootEven G)) :=
    ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hB : Continuous (rootAngularProduct G) :=
    (contDiff_rootAngularProduct H.smooth Real.pi_ne_zero
      (fun r _ => H.odd_period r) (fun r _ => H.even_period r)).continuous
  obtain ⟨δ₂, hδ₂, hpositive⟩ := exists_uniform_periodic_collar_of_local
    (Q := fun p => 0 < angularPartial (extendedRootEven G) p ∧
      0 < rootAngularProduct G p) Real.pi_ne_zero
    (fun r θ => by
      simp only [H.extended_angle_derivative_period r θ, H.angularProduct_period r θ])
    (fun θ => by
      have hder := (H.label_smooth.differentiable (by simp) θ).hasDerivAt
      have hφzero : 0 < angularPartial (extendedRootEven G) (0, θ) := by
        rw [angularPartial_extendedRootEven_zero H.smooth Real.pi_ne_zero
          (fun r _ => H.even_period r) H.zero_section hder]
        exact H.label_positive θ
      have hBzero : 0 < rootAngularProduct G (0, θ) := by
        rw [rootAngularProduct_zero H.smooth Real.pi_ne_zero
          (fun r _ => H.even_period r) H.zero_section hder]
        exact pow_pos (H.label_positive θ) 2
      exact (hφθ.continuousAt.tendsto.eventually (Ioi_mem_nhds hφzero)).and
        (hB.continuousAt.tendsto.eventually (Ioi_mem_nhds hBzero)))
  refine ⟨min δ₁ δ₂, lt_min_iff.mpr ⟨hδ₁, hδ₂⟩, ?_⟩
  intro r θ hr
  have hc := hchart r θ (hr.trans_le (min_le_left _ _))
  have hp := hpositive r θ (hr.trans_le (min_le_right _ _))
  exact ⟨hc.1, hc.2.1, hc.2.2, hp.1, hp.2⟩

/-- Every prescribed positive canonical radius contains the image of a
sufficiently thin uniform physical root collar. Periodicity makes the
thickness common to all angular points. -/
theorem exists_uniform_first_lt {B : ℝ} (hB : 0 < B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x θ : ℝ, |x| < δ →
      (extendedRootEvenOddChart G (x, θ)).1 < B := by
  obtain ⟨η, hη, hgeometry⟩ := H.exists_uniform_positive_geometry
  apply exists_uniform_periodic_collar_of_local
    (Q := fun p => (extendedRootEvenOddChart G p).1 < B) Real.pi_ne_zero
  · intro x θ
    have he : (extendedRootEvenOddChart G (x, θ + Real.pi)).1 =
        (extendedRootEvenOddChart G (x, θ)).1 := by
      simpa only [Prod.fst_add, add_zero] using
        congrArg Prod.fst (H.extended_chart_period x θ)
    simp only [he]
  · intro θ
    have hzero : |(0 : ℝ)| < η := by simpa only [abs_zero] using hη
    have hF : ContDiffAt ℝ ∞ (extendedRootEvenOddChart G) (0, θ) :=
      (hgeometry 0 θ hzero).1
    have hbound : (extendedRootEvenOddChart G (0, θ)).1 < B := by
      simpa only [H.extended_chart_zero θ] using hB
    exact hF.fst.continuousAt.tendsto.eventually (Iio_mem_nhds hbound)

/-- Every hypothesis of the smooth boundary-height theorem is now
supplied by the actual coordinate construction, apart from the actual
leading coefficient's local smoothness and positivity. -/
theorem height_boundary {a : PolarPoint → ℝ} (θ : ℝ)
    (ha : ContDiffAt ℝ ∞ a (0, θ)) (ha0 : 0 < a (0, θ)) :
    rootHeightFactor a G (0, θ) =
        a (0, θ) * rootRadialFactor G (0, θ) / deriv hL θ ∧
      ContDiffAt ℝ ∞ (rootSmoothHeight a G) (0, θ) ∧
      0 < rootSmoothHeight a G (0, θ) ∧
      rootSmoothHeight a G (0, θ) ^ 2 * rootHeightFactor a G (0, θ) = 1 :=
  rootSmoothHeight_boundary H.smooth Real.pi_ne_zero
    (fun r _ => H.odd_period r) (fun r _ => H.even_period r) H.zero_section
    (H.label_smooth.differentiable (by simp) θ).hasDerivAt (H.label_positive θ)
    (H.odd_positive θ) ha ha0

end N04bRootCoordinateProperties

/-- On the physical positive side, the constructed chart has strictly
positive first coordinate whenever its genuine root coefficient is positive. -/
theorem n04b_extended_root_first_pos
    {G : ℝ × ℝ × ℝ → ℝ} {p : PolarPoint}
    (hp : 0 < p.1) (hχ : 0 < extendedRootOddCoefficient G p) :
    0 < (extendedRootEvenOddChart G p).1 := by
  exact mul_pos hp (Real.rpow_pos_of_pos
    (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) hχ) _)

end ContinuousFlexibility.Analysis
