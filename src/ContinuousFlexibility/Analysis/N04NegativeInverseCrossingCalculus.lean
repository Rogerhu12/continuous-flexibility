import ContinuousFlexibility.Analysis.N04NegativeInversePhysicalBounds

/-!
# Scalar calculus for changing the reference half

These elementary steps are proved before the physical atlas is
instantiated. Their applications preserve the actual directional tower
and the coefficient chosen for its whole finite prefix.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

/-- A genuine joint tower is continuous in the physical variable at
each point of its open product domain. -/
theorem n04NegativeInverse_fixedParameter_continuousAt
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {Ω : Set PolarPoint} {f : E × PolarPoint → ℝ}
    (J : SmoothDirections (U ×ˢ Ω) f)
    {z : E} (hz : z ∈ U) {p : PolarPoint} (hp : p ∈ Ω) :
    ContinuousAt (fun q : PolarPoint => f (z, q)) p := by
  have hJ : ContinuousAt f (z, p) :=
    J.continuousOn.continuousAt (J.open_domain.mem_nhds ⟨hz, hp⟩)
  exact hJ.comp (continuousAt_const.prodMk continuousAt_id)

/-- Zeroth mixed differentiation and a zeroth material power retain
the actual pointwise difference. -/
theorem n04NegativeInverse_mixedZero_lt
    {E δ : ℝ} {f g : PolarPoint → ℝ} {q : PolarPoint}
    (h : E ^ (0 : ℝ) * |mixedDerivative 0 0 (fun p => f p - g p) q| < δ) :
    |f q - g q| < δ := by
  simpa only [Real.rpow_zero, one_mul, spaces_mixedDerivative_zero] using h

/-- Remove a zeroth real power before substituting the material data. -/
theorem n04NegativeInverse_remove_rpow_zero
    {a E C : ℝ} (h : a * E ^ (0 : ℝ) ≤ C) : a ≤ C := by
  simpa only [Real.rpow_zero, mul_one] using h

/-- Enlarge a prefix coefficient without changing either its height
weight or its saved spatial power. -/
theorem n04NegativeInverse_prefix_mono
    {x M B H t : ℝ} (hcost : M ≤ B) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (hx : x ≤ M * H * t) : x ≤ B * H * t :=
  hx.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcost hH) ht)

end ContinuousFlexibility.Analysis
