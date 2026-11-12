import ContinuousFlexibility.Analysis.WholePositiveTransportAssembly
import ContinuousFlexibility.Analysis.CoordinatePrincipalDeterminant

/-!
# Actual positive charts from the constructed whole-component transport

The chart is the displayed inverse transport, and its height is the
reciprocal of the constructed relative height at that inverse point.
All assertions below concern these actual functions. They do not force
unit principal density or assume the final canonical operator identity.
This is a new reconstruction after the workspace reset.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def wholePositiveChartHeight (σ : PolarPoint → PolarPoint) (Q : PolarPoint → ℝ)
    (p : PolarPoint) : ℝ := (Q (σ p))⁻¹

structure WholePositiveChartGeometry
    (F G : PolarPoint → PolarPoint) (h : PolarPoint → ℝ) (l r c d : ℝ) : Prop where
  chart_smooth : ContDiff ℝ ∞ F
  inverse_smooth : ContDiff ℝ ∞ G
  height_smooth : ContDiff ℝ ∞ h
  height_positive : ∀ p, 0 < h p
  left_inverse : Function.LeftInverse G F
  right_inverse : Function.RightInverse G F
  jacobian_positive : ∀ p, 0 < planeJacobian F p
  bijOn : BijOn F (Ioo l r ×ˢ (univ : Set ℝ)) (Ioo l r ×ˢ (univ : Set ℝ))
  maps_open : MapsTo F (Ioo l r ×ˢ (univ : Set ℝ)) (Ioo l r ×ˢ (univ : Set ℝ))
  inverse_maps_open : MapsTo G
    (Ioo l r ×ˢ (univ : Set ℝ)) (Ioo l r ×ˢ (univ : Set ℝ))
  maps_closed : MapsTo F (Icc l r ×ˢ (univ : Set ℝ)) (Icc l r ×ˢ (univ : Set ℝ))
  inverse_maps_closed : MapsTo G
    (Icc l r ×ˢ (univ : Set ℝ)) (Icc l r ×ˢ (univ : Set ℝ))
  period_add : ∀ p, F (p + (0, Real.pi)) = F p + (0, Real.pi)
  inverse_period_add : ∀ p, G (p + (0, Real.pi)) = G p + (0, Real.pi)
  height_period : ∀ p, h (p + (0, Real.pi)) = h p
  reflect : ∀ p, F (p.1, -p.2) = ((F p).1, -(F p).2)
  inverse_reflect : ∀ p, G (p.1, -p.2) = ((G p).1, -(G p).2)
  height_even : ∀ p, h (p.1, -p.2) = h p
  jacobian_even : ∀ p, planeJacobian F (p.1, -p.2) = planeJacobian F p
  middle_germ : ∀ x ∈ Icc c d, ∀ θ, F =ᶠ[𝓝 (x, θ)] (id : PolarPoint → PolarPoint)
  inverse_middle_germ : ∀ x ∈ Icc c d, ∀ θ,
    G =ᶠ[𝓝 (x, θ)] (id : PolarPoint → PolarPoint)
  height_middle_germ : ∀ x ∈ Icc c d, ∀ θ, h =ᶠ[𝓝 (x, θ)] (fun _ => (1 : ℝ))
  boundary_inverse : ∀ p, CanonicalBoundaryInverseGerm F G p

theorem wholePositiveChartGeometry_of_transport
    {τ σ : PolarPoint → PolarPoint} {Q : PolarPoint → ℝ} {l r c d J : ℝ}
    (hgeometry : WholeComponentTransportGeometry τ σ l r c d J)
    (hQ : ContDiff ℝ ∞ Q) (hQpos : ∀ p, 0 < Q p)
    (hQperiod : ∀ x θ, Q (x, θ + Real.pi) = Q (x, θ))
    (hQeven : ∀ x θ, Q (x, -θ) = Q (x, θ))
    (hQmiddle : ∀ x ∈ Icc c d, ∀ θ, Q =ᶠ[𝓝 (x, θ)] (fun _ => (1 : ℝ))) :
    WholePositiveChartGeometry σ τ (wholePositiveChartHeight σ Q) l r c d := by
  have hJ (p : PolarPoint) : 0 < planeJacobian σ p := by
    have hinverse : τ ∘ σ =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint) :=
      Filter.Eventually.of_forall hgeometry.right_inverse
    have hprod := planeJacobian_inverse_mul_of_germ
      (hgeometry.inverse_smooth.differentiable (by simp) p)
      (hgeometry.smooth.differentiable (by simp) (σ p)) hinverse
    by_contra hnot
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos
      (hgeometry.jacobian_positive (σ p)).le (le_of_not_gt hnot)
    rw [hprod] at hnonpos
    exact (not_le_of_gt zero_lt_one) hnonpos
  have hQP (p : PolarPoint) : Q (p + (0, Real.pi)) = Q p := by
    rcases p with ⟨x, θ⟩
    simpa only [Prod.mk_add_mk, add_zero] using hQperiod x θ
  have hheight : ContDiff ℝ ∞ (wholePositiveChartHeight σ Q) :=
    (hQ.comp hgeometry.inverse_smooth).inv (fun p => (hQpos (σ p)).ne')
  have hleft : Function.LeftInverse τ σ := hgeometry.right_inverse
  have hbij : BijOn σ (Ioo l r ×ˢ (univ : Set ℝ)) (Ioo l r ×ˢ (univ : Set ℝ)) :=
    ⟨hgeometry.inverse_maps_open, hleft.injective.injOn,
      fun p hp => ⟨τ p, hgeometry.maps_open hp, hgeometry.left_inverse p⟩⟩
  refine {
    chart_smooth := hgeometry.inverse_smooth
    inverse_smooth := hgeometry.smooth
    height_smooth := hheight
    height_positive := fun p => inv_pos.mpr (hQpos (σ p))
    left_inverse := hgeometry.right_inverse
    right_inverse := hgeometry.left_inverse
    jacobian_positive := hJ
    bijOn := hbij
    maps_open := hgeometry.inverse_maps_open
    inverse_maps_open := hgeometry.maps_open
    maps_closed := hgeometry.inverse_maps_closed
    inverse_maps_closed := hgeometry.maps_closed
    period_add := hgeometry.inverse_period_add
    inverse_period_add := hgeometry.period_add
    height_period := ?_
    reflect := hgeometry.inverse_reflect
    inverse_reflect := hgeometry.reflect
    height_even := ?_
    jacobian_even := planeJacobian_even_of_angle_reflection
      (hgeometry.inverse_smooth.differentiable (by simp)) hgeometry.inverse_reflect
    middle_germ := hgeometry.inverse_middle_germ
    inverse_middle_germ := hgeometry.middle_germ
    height_middle_germ := ?_
    boundary_inverse := fun p => canonicalBoundaryInverseGerm_of_global_leftInverse
      hgeometry.inverse_smooth.contDiffAt (hJ p).ne' hgeometry.right_inverse }
  · intro p
    change (Q (σ (p + (0, Real.pi))))⁻¹ = (Q (σ p))⁻¹
    rw [hgeometry.inverse_period_add, hQP]
  · intro p
    change (Q (σ (p.1, -p.2)))⁻¹ = (Q (σ p))⁻¹
    rw [hgeometry.inverse_reflect, hQeven]
  · intro x hx θ
    filter_upwards [hgeometry.inverse_middle_germ x hx θ, hQmiddle x hx θ] with p hpσ hpQ
    change (Q (σ p))⁻¹ = 1
    rw [hpσ, hpQ, inv_one]

theorem wholePositiveChartGeometry_of_matching
    {n : ℕ} {F : Bool → PolarPoint → PolarPoint} {q : Bool → PolarPoint → ℝ}
    {τ σ : PolarPoint → PolarPoint} {Q : PolarPoint → ℝ} {l r c d J H : ℝ}
    (h : WholePositiveTransportMatching n F q τ σ Q l r c d J H) :
    WholePositiveChartGeometry σ τ (wholePositiveChartHeight σ Q) l r c d :=
  wholePositiveChartGeometry_of_transport h.geometry h.height_smooth
    h.height_positive h.height_period h.height_even h.height_middle_germ

/-- The relative height is the one already constructed, at the same
reference point. No total inverse is evaluated outside its true formula. -/
theorem wholePositiveChartHeight_reference_ratio
    {τ σ : PolarPoint → PolarPoint} (Q : PolarPoint → ℝ)
    (hleft : Function.LeftInverse σ τ) (p : PolarPoint) :
    1 / wholePositiveChartHeight σ Q (τ p) = Q p := by
  simp only [wholePositiveChartHeight, hleft p, one_div, inv_inv]

theorem wholePositiveChartHeight_bound
    {σ : PolarPoint → PolarPoint} {Q : PolarPoint → ℝ} {H : ℝ}
    (hQ : ∀ p, Q p ≤ H ∧ (Q p)⁻¹ ≤ H) (p : PolarPoint) :
    wholePositiveChartHeight σ Q p ≤ H ∧
      (wholePositiveChartHeight σ Q p)⁻¹ ≤ H := by
  exact ⟨(hQ (σ p)).2, by simpa only [wholePositiveChartHeight, inv_inv] using (hQ (σ p)).1⟩

end ContinuousFlexibility.Analysis
