import ContinuousFlexibility.Analysis.WholePositiveChartGeometry
import ContinuousFlexibility.Analysis.CoordinateOperatorConstruction
import ContinuousFlexibility.Analysis.CanonicalCoefficientIdentities

/-!
# Actual fields of a whole positive canonical piece

The chart is the inverse transport, its inverse is the transport, and its
height is the reciprocal relative height at the chart point.  The standard
open, closed, and normalization clauses follow from these actual maps.
The coefficient and potential fields use the actual coordinate formulas.
At the reference member they retain the physical coefficient field.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem WholePositiveChartGeometry.open_fields
    {F G : PolarPoint → PolarPoint} {h : PolarPoint → ℝ} {l r c d : ℝ}
    (H : WholePositiveChartGeometry F G h l r c d) :
    MapsTo F (Ioo l r ×ˢ (univ : Set ℝ)) (Ioo l r ×ˢ (univ : Set ℝ)) ∧
    MapsTo G (Ioo l r ×ˢ (univ : Set ℝ)) (Ioo l r ×ˢ (univ : Set ℝ)) ∧
    (∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), G (F p) = p) ∧
    (∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), F (G p) = p) ∧
    ContDiffOn ℝ ∞ F (Ioo l r ×ˢ (univ : Set ℝ)) ∧
    ContDiffOn ℝ ∞ G (Ioo l r ×ˢ (univ : Set ℝ)) ∧
    ContDiffOn ℝ ∞ h (Ioo l r ×ˢ (univ : Set ℝ)) ∧
    (∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ),
      0 < h p ∧ planeJacobian F p ≠ 0 ∧
      F (p + (0, Real.pi)) = F p + (0, Real.pi) ∧
      h (p + (0, Real.pi)) = h p) := by
  exact ⟨H.maps_open, H.inverse_maps_open, fun p _ => H.left_inverse p,
    fun p _ => H.right_inverse p, H.chart_smooth.contDiffOn,
    H.inverse_smooth.contDiffOn, H.height_smooth.contDiffOn,
    fun p _ => ⟨H.height_positive p, (H.jacobian_positive p).ne',
      H.period_add p, H.height_period p⟩⟩

theorem WholePositiveChartGeometry.boundary_fields
    {F G : PolarPoint → PolarPoint} {h : PolarPoint → ℝ} {l r c d : ℝ}
    (H : WholePositiveChartGeometry F G h l r c d) (hlr : l < r) :
    MapsTo F (closure (Ioo l r ×ˢ (univ : Set ℝ)))
      (Icc l r ×ˢ (univ : Set ℝ)) ∧
    MapsTo G (Icc l r ×ˢ (univ : Set ℝ))
      (closure (Ioo l r ×ˢ (univ : Set ℝ))) ∧
    (∀ p ∈ closure (Ioo l r ×ˢ (univ : Set ℝ)), G (F p) = p) ∧
    (∀ p ∈ Icc l r ×ˢ (univ : Set ℝ), F (G p) = p) ∧
    (∀ p ∈ closure (Ioo l r ×ˢ (univ : Set ℝ)),
      ContDiffAt ℝ ∞ F p ∧ ContDiffAt ℝ ∞ h p ∧
      planeJacobian F p ≠ 0 ∧ 0 < h p) ∧
    (∀ p ∈ frontier (Ioo l r ×ˢ (univ : Set ℝ)),
      CanonicalBoundaryInverseGerm F G p) := by
  have hclosed : closure (Ioo l r ×ˢ (univ : Set ℝ)) =
      Icc l r ×ˢ (univ : Set ℝ) := by
    rw [closure_prod_eq, closure_Ioo hlr.ne, closure_univ]
  rw [hclosed]
  exact ⟨H.maps_closed, H.inverse_maps_closed, fun p _ => H.left_inverse p,
    fun p _ => H.right_inverse p,
    fun p _ => ⟨H.chart_smooth.contDiffAt, H.height_smooth.contDiffAt,
      (H.jacobian_positive p).ne', H.height_positive p⟩,
    fun p _ => H.boundary_inverse p⟩

/-- Both directions are genuine ordinary-neighborhood inverse germs,
including points on either closed boundary circle. -/
theorem WholePositiveChartGeometry.inverse_germs
    {F G : PolarPoint → PolarPoint} {h : PolarPoint → ℝ} {l r c d : ℝ}
    (H : WholePositiveChartGeometry F G h l r c d) (p : PolarPoint) :
    CanonicalBoundaryInverseGerm F G p ∧ CanonicalBoundaryInverseGerm G F p := by
  have hi : F ∘ G =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint) :=
    Filter.Eventually.of_forall H.right_inverse
  have hprod := planeJacobian_inverse_mul_of_germ
    (H.inverse_smooth.differentiable (by simp) p)
    (H.chart_smooth.differentiable (by simp) (G p)) hi
  have hJG : planeJacobian G p ≠ 0 := by
    intro he
    rw [he, mul_zero] at hprod
    exact zero_ne_one hprod
  exact ⟨H.boundary_inverse p,
    canonicalBoundaryInverseGerm_of_global_leftInverse
      H.inverse_smooth.contDiffAt hJG H.right_inverse⟩

theorem WholePositiveChartGeometry.normalization_on_middle
    {F G : PolarPoint → PolarPoint} {h : PolarPoint → ℝ} {l r c d : ℝ}
    (H : WholePositiveChartGeometry F G h l r c d) {p : PolarPoint}
    (hp : p.1 ∈ Icc c d) : F p = p ∧ G p = p ∧ h p = 1 := by
  rcases p with ⟨x, θ⟩
  exact ⟨(H.middle_germ x hp θ).eq_of_nhds,
    (H.inverse_middle_germ x hp θ).eq_of_nhds,
    (H.height_middle_germ x hp θ).eq_of_nhds⟩

/-- The positive principal field is the actual density for the inverse
transport and the reciprocal relative-height gauge. -/
def wholePositiveCanonicalCoefficients (A : SymmetricCoefficients)
    (τ σ : PolarPoint → PolarPoint) (Q : PolarPoint → ℝ) : SymmetricCoefficients :=
  inverseChartPrincipalCoefficients A σ τ (wholePositiveChartHeight σ Q)

/-- The positive type has the minus sign in the canonical operator. -/
def wholePositiveCanonicalPotential (A : SymmetricCoefficients)
    (τ σ : PolarPoint → PolarPoint) (Q : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  -inverseChartPotential A σ τ (wholePositiveChartHeight σ Q) p

theorem inverseChartPrincipalCoefficients_id_one (A : SymmetricCoefficients) :
    inverseChartPrincipalCoefficients A id id (fun _ => 1) = A := by
  cases A
  simp only [inverseChartPrincipalCoefficients, coordinatePrincipalDensity,
    coefficientQuadratic, planeJacobian, id_eq, fderiv_id,
    ContinuousLinearMap.id_apply, one_pow, zero_pow two_ne_zero,
    one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add, sub_zero,
    abs_one, div_one]

theorem inverseChartPotential_id_one (A : SymmetricCoefficients) :
    inverseChartPotential A id id (fun _ => 1) = (fun _ => 0) := by
  funext p
  simp only [inverseChartPotential, id_eq, divergenceOperator_const, mul_zero, zero_div]

/-- The reference coefficient field is exactly the physical field.
No determinant or unit-principal condition is imposed on it. -/
theorem wholePositiveCanonicalFields_reference (A : SymmetricCoefficients)
    {τ σ : PolarPoint → PolarPoint} {Q : PolarPoint → ℝ}
    (hτ : τ = id) (hσ : σ = id) (hQ : Q = (fun _ => 1)) :
    wholePositiveChartHeight σ Q = (fun _ => 1) ∧
    wholePositiveCanonicalCoefficients A τ σ Q = A ∧
    wholePositiveCanonicalPotential A τ σ Q = (fun _ => 0) := by
  subst τ
  subst σ
  subst Q
  have hh : wholePositiveChartHeight id (fun _ => 1) = (fun _ => 1) := by
    funext p
    simp only [wholePositiveChartHeight, inv_one]
  refine ⟨hh, ?_, ?_⟩
  · simpa only [wholePositiveCanonicalCoefficients, hh] using
      inverseChartPrincipalCoefficients_id_one A
  · funext p
    simp only [wholePositiveCanonicalPotential, hh, inverseChartPotential_id_one, neg_zero]

/-- This is the actual positive canonical operator at the inverse-chart
point. Physical coefficient regularity and the constructed geometry prove
the identity; the displayed operator identity is not an input. -/
theorem wholePositiveCanonicalFields_operator
    {A : SymmetricCoefficients} {τ σ : PolarPoint → PolarPoint}
    {Q : PolarPoint → ℝ} {l r c d : ℝ}
    (H : WholePositiveChartGeometry σ τ (wholePositiveChartHeight σ Q) l r c d)
    {p : PolarPoint}
    (ha : ContDiffAt ℝ ∞ A.a (τ p)) (hb : ContDiffAt ℝ ∞ A.b (τ p))
    (hc : ContDiffAt ℝ ∞ A.c (τ p))
    (W : PolarPoint → ℝ) (hW : ContDiff ℝ ∞ W) :
    -(wholePositiveChartHeight σ Q (τ p) *
        divergenceOperator A (fun x => wholePositiveChartHeight σ Q x * W (σ x))
          (τ p) / |planeJacobian σ (τ p)|) =
      -divergenceOperator (wholePositiveCanonicalCoefficients A τ σ Q) W p +
        wholePositiveCanonicalPotential A τ σ Q p * W p := by
  have hi : ∀ᶠ x in 𝓝 (τ p), τ (σ x) = x :=
    Filter.Eventually.of_forall H.left_inverse
  have hop := coordinateOperator_explicit_fields
    (A := A) (F := σ) (G := τ) (h := wholePositiveChartHeight σ Q) (x := τ p)
    ha hb hc H.chart_smooth.contDiffAt H.inverse_smooth.contDiffAt
    H.height_smooth.contDiffAt hW (H.jacobian_positive (τ p)).ne' hi
  rw [H.right_inverse p] at hop
  dsimp only [wholePositiveCanonicalCoefficients, wholePositiveCanonicalPotential]
  rw [hop]
  ring

end ContinuousFlexibility.Analysis

