import ContinuousFlexibility.Analysis.ParameterizedCircleInverse
import ContinuousFlexibility.Analysis.BoundaryMixedJets
import ContinuousFlexibility.Analysis.CylinderSobolev
import ContinuousFlexibility.Geometry.GraphSurfaceGeometry

/-!
# Actual endpoint jets in angular inverse coordinates

The radial field is first written at fixed canonical angle using the
genuine smooth inverse of the chosen angular lift. A constant radial
boundary value makes its angular derivative vanish, so the positive
radial boundary slope is unchanged. Matching finite jets in these
fiber coordinates then matches the original physical radial jets after
composition with the angular lift.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def angularFiberPullback (φ ξ : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  ξ (p.1, parameterizedCircleInverse φ p)

theorem contDiff_angularFiberPullback
    {φ ξ : PolarPoint → ℝ} {T : ℝ} (hT : T ≠ 0)
    (hφ : ContDiff ℝ ∞ φ) (hξ : ContDiff ℝ ∞ ξ)
    (hpositive : ∀ p : PolarPoint, 0 < deriv (fun θ => φ (p.1, θ)) p.2)
    (hperiod : ∀ r θ, φ (r, θ + T) = φ (r, θ) + T) :
    ContDiff ℝ ∞ (angularFiberPullback φ ξ) :=
  hξ.comp (contDiff_fst.prodMk
    (contDiff_parameterizedCircleInverse hT hφ hpositive hperiod))

/-- This equality uses the actual left inverse, at every physical point. -/
theorem angularFiberPullback_cancel
    {φ ξ : PolarPoint → ℝ}
    (hpositive : ∀ p : PolarPoint, 0 < deriv (fun θ => φ (p.1, θ)) p.2)
    (p : PolarPoint) :
    angularFiberPullback φ ξ (p.1, φ p) = ξ p := by
  unfold angularFiberPullback
  rw [parameterizedCircleInverse_left_inverse hpositive p]

theorem angularFiberPullback_boundary
    {φ ξ : PolarPoint → ℝ} {c v : ℝ}
    (hvalue : ∀ θ, ξ (c, θ) = v) (η : ℝ) :
    angularFiberPullback φ ξ (c, η) = v :=
  hvalue (parameterizedCircleInverse φ (c, η))

/-- At a constant boundary, changing to fixed canonical angle preserves
the actual positive radial slope. No derivative of the chosen inverse
is postulated: its smoothness comes from the parameterized inverse theorem. -/
theorem radialPartial_angularFiberPullback_boundary
    {φ ξ : PolarPoint → ℝ} {T c v : ℝ} (hT : T ≠ 0)
    (hφ : ContDiff ℝ ∞ φ) (hξ : ContDiff ℝ ∞ ξ)
    (hpositive : ∀ p : PolarPoint, 0 < deriv (fun θ => φ (p.1, θ)) p.2)
    (hperiod : ∀ r θ, φ (r, θ + T) = φ (r, θ) + T)
    (hvalue : ∀ θ, ξ (c, θ) = v) (η : ℝ) :
    radialPartial (angularFiberPullback φ ξ) (c, η) =
      radialPartial ξ (c, parameterizedCircleInverse φ (c, η)) := by
  let A := parameterizedCircleInverse φ
  have hA : ContDiff ℝ ∞ A :=
    contDiff_parameterizedCircleInverse hT hφ hpositive hperiod
  have hσ := contDiff_angularFiberPullback hT hφ hξ hpositive hperiod
  have hAs : ContDiff ℝ ∞ (fun r : ℝ => A (r, η)) :=
    hA.comp (contDiff_id.prodMk contDiff_const)
  have hline : HasDerivAt (fun r : ℝ => (r, A (r, η)))
      (1, deriv (fun r => A (r, η)) c) c :=
    (hasDerivAt_id c).prodMk ((hAs.differentiable (by simp) c).hasDerivAt)
  have hd := (hξ.differentiable (by simp) (c, A (c, η))).hasFDerivAt
    |>.comp_hasDerivAt c hline
  have hzero : angularPartial ξ (c, A (c, η)) = 0 := by
    rw [← deriv_cylinder_angular_slice (hξ.differentiable (by simp)) c (A (c, η))]
    have he : (fun θ : ℝ => ξ (c, θ)) = fun _ => v := funext hvalue
    rw [he, deriv_const]
  rw [← deriv_cylinder_radial_slice (hσ.differentiable (by simp)) c η]
  calc
    _ = fderiv ℝ ξ (c, A (c, η)) (1, deriv (fun r => A (r, η)) c) := hd.deriv
    _ = radialPartial ξ (c, A (c, η)) := by
      rw [height_fderiv_coordinates, hzero]
      simp only [mul_one, zero_mul, add_zero]

theorem angularFiberPullback_periodic
    {φ ξ : PolarPoint → ℝ} {T : ℝ} (hT : T ≠ 0)
    (hφ : ContDiff ℝ ∞ φ)
    (hpositive : ∀ p : PolarPoint, 0 < deriv (fun θ => φ (p.1, θ)) p.2)
    (hperiod : ∀ r θ, φ (r, θ + T) = φ (r, θ) + T)
    (hξperiod : ∀ r θ, ξ (r, θ + T) = ξ (r, θ)) (r η : ℝ) :
    angularFiberPullback φ ξ (r, η + T) = angularFiberPullback φ ξ (r, η) := by
  unfold angularFiberPullback
  rw [parameterizedCircleInverse_period_add hT hφ hpositive hperiod, hξperiod]

theorem angularFiberPullback_reflect
    {φ ξ : PolarPoint → ℝ} {T : ℝ} (hT : T ≠ 0)
    (hφ : ContDiff ℝ ∞ φ)
    (hpositive : ∀ p : PolarPoint, 0 < deriv (fun θ => φ (p.1, θ)) p.2)
    (hperiod : ∀ r θ, φ (r, θ + T) = φ (r, θ) + T)
    (hφodd : ∀ r θ, φ (r, -θ) = -φ (r, θ))
    (hξeven : ∀ r θ, ξ (r, -θ) = ξ (r, θ)) (r η : ℝ) :
    angularFiberPullback φ ξ (r, -η) = angularFiberPullback φ ξ (r, η) := by
  have hInv : parameterizedCircleInverse φ (r, -η) =
      -parameterizedCircleInverse φ (r, η) :=
    parameterizedCircleInverse_reflect (σ := id) hT hφ hpositive hperiod hφodd r η
  unfold angularFiberPullback
  rw [hInv, hξeven]

/-- Finite matching in the actual angular inverse coordinates implies
finite matching of the physical radial coordinate. These are actual
derivatives, obtained by transporting the zero jet of the difference. -/
theorem radialBoundaryJets_angularFiber_composition
    {φ ξ Y : PolarPoint → ℝ} {T c : ℝ} {n : ℕ} (hT : T ≠ 0)
    (hφ : ContDiff ℝ ∞ φ) (hξ : ContDiff ℝ ∞ ξ) (hY : ContDiff ℝ ∞ Y)
    (hpositive : ∀ p : PolarPoint, 0 < deriv (fun θ => φ (p.1, θ)) p.2)
    (hperiod : ∀ r θ, φ (r, θ + T) = φ (r, θ) + T)
    (hjet : ∀ j ≤ n, ∀ η, radialBoundaryJet Y c j η =
      radialBoundaryJet (angularFiberPullback φ ξ) c j η) :
    ∀ k ≤ n, ∀ θ,
      radialBoundaryJet (fun p => Y (p.1, φ p)) c k θ =
        radialBoundaryJet ξ c k θ := by
  let σ := angularFiberPullback φ ξ
  let D : PolarPoint → ℝ := fun p => Y p - σ p
  have hσ : ContDiff ℝ ∞ σ :=
    contDiff_angularFiberPullback hT hφ hξ hpositive hperiod
  have hD : ContDiff ℝ ∞ D := hY.sub hσ
  have hzero (j : ℕ) (hj : j ≤ n) (η : ℝ) : radialBoundaryJet D c j η = 0 := by
    have hYs : ContDiff ℝ ∞ (fun r : ℝ => Y (r, η)) :=
      hY.comp (contDiff_id.prodMk contDiff_const)
    have hσs : ContDiff ℝ ∞ (fun r : ℝ => σ (r, η)) :=
      hσ.comp (contDiff_id.prodMk contDiff_const)
    change iteratedDeriv j (fun r : ℝ => Y (r, η) - σ (r, η)) c = 0
    rw [iteratedDeriv_fun_sub
      ((hYs.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)
      ((hσs.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)]
    exact sub_eq_zero.mpr (hjet j hj η)
  intro k hk θ
  let γ : ℝ → PolarPoint := fun r => (r, φ (r, θ))
  have hγ : ContDiff ℝ ∞ γ :=
    contDiff_id.prodMk (hφ.comp (contDiff_id.prodMk contDiff_const))
  have hz := iteratedDeriv_comp_eq_zero_of_radialBoundaryJets_zero
    isOpen_univ hD.contDiffOn c (fun _ => mem_univ _) hzero
    (γ := γ) hγ.contDiffAt (show γ c = (c, φ (c, θ)) from rfl) hk
  have he : D ∘ γ = fun r : ℝ => Y (r, φ (r, θ)) - ξ (r, θ) := by
    funext r
    dsimp only [Function.comp_apply, D, γ, σ]
    rw [angularFiberPullback_cancel hpositive (r, θ)]
  rw [he] at hz
  have hYs : ContDiff ℝ ∞ (fun r : ℝ => Y (r, φ (r, θ))) := hY.comp hγ
  have hξs : ContDiff ℝ ∞ (fun r : ℝ => ξ (r, θ)) :=
    hξ.comp (contDiff_id.prodMk contDiff_const)
  rw [iteratedDeriv_fun_sub
    ((hYs.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)
    ((hξs.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)] at hz
  exact sub_eq_zero.mp hz

end ContinuousFlexibility.Analysis

