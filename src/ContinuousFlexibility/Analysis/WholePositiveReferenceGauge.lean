module

public import ContinuousFlexibility.Analysis.PositiveChartRangeGeometry

/-!
# A fixed reference gauge with its actual canonical range

The reference chart may map the physical interval (l, r) to a distinct
canonical interval (u, v). The existing relative transport remains a
self-map of the physical interval. Their displayed composites have the
true canonical range and preserve the original relative transport and
height ratio. Middle normalization is equality with the fixed reference
fields, not an identity assumption on those fields.
-/

@[expose] public section

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

/-- The two range certificates compose without identifying physical
and canonical endpoints. Only the original relative maps are used. -/
theorem wholePositiveReferenceGauge_geometry
    {ψ χ τ σ : PolarPoint → PolarPoint} {h₀ Q : PolarPoint → ℝ}
    {l r u v c d : ℝ}
    (H₀ : PositiveChartRangeGeometry ψ χ h₀ l r u v)
    (H : WholePositiveChartGeometry σ τ (wholePositiveChartHeight σ Q) l r c d) :
    PositiveChartRangeGeometry (wholePositiveReferenceGaugeChart ψ σ)
      (wholePositiveReferenceGaugeInverse τ χ)
      (wholePositiveReferenceGaugeHeight h₀ σ Q) l r u v := by
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
      Function.comp_apply, H₀.left_inverse (σ p), H.left_inverse p]
  have hright : Function.RightInverse G F := by
    intro p
    simp only [F, G, wholePositiveReferenceGaugeChart, wholePositiveReferenceGaugeInverse,
      Function.comp_apply, H.right_inverse (χ p), H₀.right_inverse p]
  refine {
    chart_smooth := hF
    inverse_smooth := hG
    height_smooth := hh
    height_positive := fun p => mul_pos (H₀.height_positive (σ p)) (H.height_positive p)
    left_inverse := hleft
    right_inverse := hright
    jacobian_positive := ?_
    maps_open := fun _ hp => H₀.maps_open (H.maps_open hp)
    inverse_maps_open := fun _ hp => H.inverse_maps_open (H₀.inverse_maps_open hp)
    maps_closed := fun _ hp => H₀.maps_closed (H.maps_closed hp)
    inverse_maps_closed := fun _ hp => H.inverse_maps_closed (H₀.inverse_maps_closed hp)
    period_add := ?_
    inverse_period_add := ?_
    height_period := ?_
    reflect := ?_
    inverse_reflect := ?_
    height_even := ?_ }
  · intro p
    change 0 < planeJacobian (ψ ∘ σ) p
    rw [planeJacobian_comp (H.chart_smooth.differentiable (by simp) p)
      (H₀.chart_smooth.differentiable (by simp) (σ p))]
    exact mul_pos (H₀.jacobian_positive (σ p)) (H.jacobian_positive p)
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
    simp only [wholePositiveReferenceGaugeChart, Function.comp_apply,
      H.reflect, H₀.reflect]
  · intro p
    simp only [wholePositiveReferenceGaugeInverse, Function.comp_apply,
      H₀.inverse_reflect, H.inverse_reflect]
  · intro p
    simp only [wholePositiveReferenceGaugeHeight, H.reflect,
      H₀.height_even, H.height_even]

/-- The middle is frozen to the actual reference fields. The inverse
comparison is at the reference chart image of the physical middle point. -/
theorem wholePositiveReferenceGauge_middle_germs
    {ψ χ τ σ : PolarPoint → PolarPoint} {h₀ Q : PolarPoint → ℝ}
    {l r u v c d : ℝ}
    (H₀ : PositiveChartRangeGeometry ψ χ h₀ l r u v)
    (H : WholePositiveChartGeometry σ τ (wholePositiveChartHeight σ Q) l r c d)
    {x : ℝ} (hx : x ∈ Icc c d) (θ : ℝ) :
    (wholePositiveReferenceGaugeChart ψ σ =ᶠ[𝓝 (x, θ)] ψ) ∧
      (wholePositiveReferenceGaugeHeight h₀ σ Q =ᶠ[𝓝 (x, θ)] h₀) ∧
      (wholePositiveReferenceGaugeInverse τ χ =ᶠ[𝓝 (ψ (x, θ))] χ) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [H.middle_germ x hx θ] with p hp
    simp only [wholePositiveReferenceGaugeChart, Function.comp_apply, hp, id_eq]
  · filter_upwards [H.middle_germ x hx θ, H.height_middle_germ x hx θ] with p hp hph
    simp only [wholePositiveReferenceGaugeHeight, hp, hph, id_eq, mul_one]
  · have hχ : Tendsto χ (𝓝 (ψ (x, θ))) (𝓝 (x, θ)) := by
      have hc := H₀.inverse_smooth.continuous.continuousAt (x := ψ (x, θ))
      change Tendsto χ (𝓝 (ψ (x, θ))) (𝓝 (χ (ψ (x, θ)))) at hc
      simpa only [H₀.left_inverse (x, θ)] using hc
    have he := (H.inverse_middle_germ x hx θ).comp_tendsto hχ
    filter_upwards [he] with p hp
    simpa only [wholePositiveReferenceGaugeInverse, Function.comp_apply, id_eq] using hp

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
    rw [wholePositiveReferenceGaugeHeight_eq, hστ p]
    by_cases hQ : Q p = 0
    · simp only [hQ, div_zero]
    · field_simp [hh₀ p, hQ] <;> ring

end ContinuousFlexibility.Analysis
