import ContinuousFlexibility.Analysis.WholePositiveCanonicalFields

/-!
# A fixed reference gauge for the same positive transport

The reference chart and height are retained explicitly. Composing them
with the already constructed inverse transport changes the raw canonical
fields while preserving the actual relative transport and height ratio.
No width, endpoint source, or member of the transport family is reselected.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

def wholePositiveReferenceGaugeChart
    (ψ σ : PolarPoint → PolarPoint) : PolarPoint → PolarPoint := ψ ∘ σ

def wholePositiveReferenceGaugeInverse
    (τ χ : PolarPoint → PolarPoint) : PolarPoint → PolarPoint := τ ∘ χ

def wholePositiveReferenceGaugeHeight
    (h₀ : PolarPoint → ℝ) (σ : PolarPoint → PolarPoint) (Q : PolarPoint → ℝ)
    (p : PolarPoint) : ℝ := h₀ (σ p) * wholePositiveChartHeight σ Q p

theorem wholePositiveReferenceGaugeHeight_eq
    (h₀ : PolarPoint → ℝ) (σ : PolarPoint → PolarPoint) (Q : PolarPoint → ℝ)
    (p : PolarPoint) :
    wholePositiveReferenceGaugeHeight h₀ σ Q p = h₀ (σ p) / Q (σ p) := by
  rw [wholePositiveReferenceGaugeHeight, wholePositiveChartHeight, div_eq_mul_inv]

/-- The existing geometry certificate is closed under this fixed
reference change. Both global inverses and every true open/closed-strip
mapping clause concern the displayed composite fields. -/
theorem wholePositiveReferenceGauge_geometry
    {ψ χ τ σ : PolarPoint → PolarPoint} {h₀ Q : PolarPoint → ℝ}
    {l r c d : ℝ}
    (H₀ : WholePositiveChartGeometry ψ χ h₀ l r c d)
    (H : WholePositiveChartGeometry σ τ (wholePositiveChartHeight σ Q) l r c d) :
    WholePositiveChartGeometry (wholePositiveReferenceGaugeChart ψ σ)
      (wholePositiveReferenceGaugeInverse τ χ)
      (wholePositiveReferenceGaugeHeight h₀ σ Q) l r c d := by
  let F := wholePositiveReferenceGaugeChart ψ σ
  let G := wholePositiveReferenceGaugeInverse τ χ
  let h := wholePositiveReferenceGaugeHeight h₀ σ Q
  have hF : ContDiff ℝ ∞ F := H₀.chart_smooth.comp H.chart_smooth
  have hG : ContDiff ℝ ∞ G := H.inverse_smooth.comp H₀.inverse_smooth
  have hh : ContDiff ℝ ∞ h :=
    (H₀.height_smooth.comp H.chart_smooth).mul H.height_smooth
  have hleft : Function.LeftInverse G F := by
    intro p
    simp only [F, G, wholePositiveReferenceGaugeChart, wholePositiveReferenceGaugeInverse,
      Function.comp_apply, H₀.left_inverse, H.left_inverse]
  have hright : Function.RightInverse G F := by
    intro p
    simp only [F, G, wholePositiveReferenceGaugeChart, wholePositiveReferenceGaugeInverse,
      Function.comp_apply, H.right_inverse, H₀.right_inverse]
  have hmaps : MapsTo F (Ioo l r ×ˢ (univ : Set ℝ))
      (Ioo l r ×ˢ (univ : Set ℝ)) := fun _ hp => H₀.maps_open (H.maps_open hp)
  have hinverseMaps : MapsTo G (Ioo l r ×ˢ (univ : Set ℝ))
      (Ioo l r ×ˢ (univ : Set ℝ)) :=
    fun _ hp => H.inverse_maps_open (H₀.inverse_maps_open hp)
  have hJ (p : PolarPoint) : 0 < planeJacobian F p := by
    change 0 < planeJacobian (ψ ∘ σ) p
    rw [planeJacobian_comp (H.chart_smooth.differentiable (by simp) p)
      (H₀.chart_smooth.differentiable (by simp) (σ p))]
    exact mul_pos (H₀.jacobian_positive (σ p)) (H.jacobian_positive p)
  have hreflect (p : PolarPoint) : F (p.1, -p.2) = ((F p).1, -(F p).2) := by
    simp only [F, wholePositiveReferenceGaugeChart, Function.comp_apply,
      H.reflect, H₀.reflect]
  refine {
    chart_smooth := hF
    inverse_smooth := hG
    height_smooth := hh
    height_positive := fun p => mul_pos (H₀.height_positive (σ p)) (H.height_positive p)
    left_inverse := hleft
    right_inverse := hright
    jacobian_positive := hJ
    bijOn := ⟨hmaps, hleft.injective.injOn,
      fun p hp => ⟨G p, hinverseMaps hp, hright p⟩⟩
    maps_open := hmaps
    inverse_maps_open := hinverseMaps
    maps_closed := fun _ hp => H₀.maps_closed (H.maps_closed hp)
    inverse_maps_closed := fun _ hp => H.inverse_maps_closed (H₀.inverse_maps_closed hp)
    period_add := ?_
    inverse_period_add := ?_
    height_period := ?_
    reflect := hreflect
    inverse_reflect := ?_
    height_even := ?_
    jacobian_even := planeJacobian_even_of_angle_reflection
      (hF.differentiable (by simp)) hreflect
    middle_germ := ?_
    inverse_middle_germ := ?_
    height_middle_germ := ?_
    boundary_inverse := fun p =>
      canonicalBoundaryInverseGerm_of_global_leftInverse hF.contDiffAt (hJ p).ne' hleft }
  · intro p
    simp only [wholePositiveReferenceGaugeChart, Function.comp_apply,
      H.period_add, H₀.period_add]
  · intro p
    simp only [wholePositiveReferenceGaugeInverse, Function.comp_apply,
      H₀.inverse_period_add, H.inverse_period_add]
  · intro p
    simp only [wholePositiveReferenceGaugeHeight, H.period_add,
      H₀.height_period, H.height_period]
  · intro p
    simp only [wholePositiveReferenceGaugeInverse, Function.comp_apply,
      H₀.inverse_reflect, H.inverse_reflect]
  · intro p
    simp only [wholePositiveReferenceGaugeHeight, H.reflect,
      H₀.height_even, H.height_even]
  · intro x hx θ
    filter_upwards [H.middle_germ x hx θ, H₀.middle_germ x hx θ] with p hp hp₀
    simpa only [wholePositiveReferenceGaugeChart, Function.comp_apply, hp] using hp₀
  · intro x hx θ
    filter_upwards [H₀.inverse_middle_germ x hx θ, H.inverse_middle_germ x hx θ] with p hp₀ hp
    simpa only [wholePositiveReferenceGaugeInverse, Function.comp_apply, hp₀] using hp
  · intro x hx θ
    filter_upwards [H.middle_germ x hx θ, H₀.height_middle_germ x hx θ,
      H.height_middle_germ x hx θ] with p hp hp₀ hph
    simp only [wholePositiveReferenceGaugeHeight, hp, hp₀, hph, one_mul]

/-- At the reference member the raw fields are exactly the prescribed
reference chart, inverse and height; they need not be unit fields. -/
theorem wholePositiveReferenceGauge_reference
    (ψ χ : PolarPoint → PolarPoint) (h₀ : PolarPoint → ℝ)
    {τ σ : PolarPoint → PolarPoint} {Q : PolarPoint → ℝ}
    (hτ : τ = id) (hσ : σ = id) (hQ : Q = (fun _ => 1)) :
    wholePositiveReferenceGaugeChart ψ σ = ψ ∧
      wholePositiveReferenceGaugeInverse τ χ = χ ∧
      wholePositiveReferenceGaugeHeight h₀ σ Q = h₀ := by
  subst τ
  subst σ
  subst Q
  refine ⟨?_, ?_, ?_⟩
  · funext p
    simp only [wholePositiveReferenceGaugeChart, Function.comp_apply, id_eq]
  · funext p
    simp only [wholePositiveReferenceGaugeInverse, Function.comp_apply, id_eq]
  · funext p
    simp only [wholePositiveReferenceGaugeHeight, wholePositiveChartHeight,
      id_eq, inv_one, mul_one]

/-- These are the actual current-point, reference-point and relative
height formulas. They follow from the same true inverses, without a new
transport or a new height being chosen. -/
theorem wholePositiveReferenceGauge_relative_fields
    {ψ χ τ σ : PolarPoint → PolarPoint} {h₀ Q : PolarPoint → ℝ}
    (hχψ : Function.LeftInverse χ ψ) (hστ : Function.LeftInverse σ τ)
    (hh₀ : ∀ p, h₀ p ≠ 0) :
    wholePositiveReferenceGaugeInverse τ χ ∘ ψ = τ ∧
      χ ∘ wholePositiveReferenceGaugeChart ψ σ = σ ∧
      ∀ p, h₀ p / wholePositiveReferenceGaugeHeight h₀ σ Q (τ p) = Q p := by
  refine ⟨?_, ?_, ?_⟩
  · funext p
    simp only [wholePositiveReferenceGaugeInverse, Function.comp_apply, hχψ p]
  · funext p
    simp only [wholePositiveReferenceGaugeChart, Function.comp_apply, hχψ (σ p)]
  · intro p
    by_cases hQ : Q p = 0
    · simp only [wholePositiveReferenceGaugeHeight, wholePositiveChartHeight,
        hστ p, hQ, inv_zero, mul_zero, div_zero]
    · field_simp [wholePositiveReferenceGaugeHeight, wholePositiveChartHeight,
        hστ p, hh₀ p, hQ] <;> ring

end ContinuousFlexibility.Analysis
