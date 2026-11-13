import ContinuousFlexibility.Analysis.N04PositiveGeometryPlaneSavedPrefix

/-! # Finite saved-word prefixes under actual composition and inversion -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem n04PositiveGeometry_movingPoint_saved_prefix (N : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ degree : ℕ,
    ∀ (U : Set E) (f : E × PolarPoint → F) (g : E × PolarPoint → PolarPoint)
      (JF : SmoothDirections (U ×ˢ univ) f) (JG : SmoothDirections (U ×ˢ univ) g)
      (JO : SmoothDirections (U ×ˢ univ) (fun z => f (z.1, g z))),
    ∀ x ∈ U, ∀ Ω : Set PolarPoint, MapsTo (fun y => g (x, y)) Ω Ω →
    ∀ (p q : Seminorm ℝ E) (R M H t : ℝ), 0 ≤ R → 1 ≤ M →
      0 ≤ H → H ≤ M → 1 ≤ t → ∀ K C : ℕ, 1 ≤ C →
      N04PlaneSavedWordBounds JF N K C x Ω p q R M H t →
      N04PlaneSavedWordBounds JG N K C x Ω p q R M H t →
      N04PlaneSavedWordBounds JO N K C x Ω p q R (A * M ^ degree) H t := by
  choose a ha hbound using fun j => n04PositiveGeometry_movingPoint_unit_saved_word_bound
    (E := E) (V := PolarPoint) (Z := F) j
  obtain ⟨A, hA, degree, hmajor⟩ := n04PositiveGeometry_finite_nat_power_majorant
    N a (fun j => 2 * j + 2) ha
  refine ⟨A, hA, degree, ?_⟩
  intro U f g JF JG JO x hx Ω hmap p q R M H t hR hM hH hHM ht K C hC hf hg
    y hy j hj hjN w hw v hpure hbox
  have hb := hbound j (U ×ˢ univ) (U ×ˢ univ) f g JF JG JO
    (x, y) ⟨hx, mem_univ _⟩ ⟨hx, mem_univ _⟩ p q R hR M H t hM hH hHM ht K C hC
    (fun k hk hkj u hu a ha hbox => hf (g (x, y)) (hmap hy) k hk (hkj.trans hjN)
      u hu a ha hbox)
    (fun k hk hkj u hu a ha hbox => hg y hy k hk (hkj.trans hjN) u hu a ha hbox)
    hj w hw v hpure hbox
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hmajor j hjN M hM) (parameterHeightWeight_nonneg hH _))
    (pow_nonneg (zero_le_one.trans ht) _))

theorem n04PositiveGeometry_angularInverse_saved_prefix (N : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ degree : ℕ,
    ∀ (U : Set E) (φ : E → PolarPoint → ℝ)
      (JF : SmoothDirections (U ×ˢ univ)
        (fun z : E × PolarPoint => n04PositiveGeometry_angularGraph (φ z.1) z.2))
      (JG : SmoothDirections (U ×ˢ univ)
        (fun z : E × PolarPoint => n04PositiveGeometry_angularGraphInverse (φ z.1) z.2)),
      (∀ z ∈ U, ContDiff ℝ ∞ (φ z)) →
      (∀ z ∈ U, ∀ y, 0 < deriv (fun θ => φ z (y.1, θ)) y.2) →
      (∀ z ∈ U, ∀ r θ, φ z (r, θ + Real.pi) = φ z (r, θ) + Real.pi) →
    ∀ x ∈ U, ∀ Ω : Set PolarPoint,
      MapsTo (n04PositiveGeometry_angularGraphInverse (φ x)) Ω Ω →
    ∀ (p q : Seminorm ℝ E) (R M H t : ℝ), 0 ≤ R → 1 ≤ M →
      0 ≤ H → H ≤ M → 1 ≤ t →
      (∀ y ∈ Ω, |(deriv (fun θ => φ x (y.1, θ))
        (parameterizedCircleInverse (φ x) y))⁻¹| ≤ M) →
    ∀ K C : ℕ, 1 ≤ C →
      N04PlaneSavedWordBounds JF N K C x Ω p q R M H t →
      N04PlaneSavedWordBounds JG N K C x Ω p q R (A * M ^ degree) H t := by
  choose a ha d hbound using fun j => n04PositiveGeometry_angularInverse_unit_word_bound
    (E := E) j
  obtain ⟨A, hA, degree, hmajor⟩ :=
    n04PositiveGeometry_finite_nat_power_majorant N a d ha
  refine ⟨A, hA, degree, ?_⟩
  intro U φ JF JG hsmooth hpositive hperiod x hx Ω hmap p q R M H t hR hM hH hHM ht
    hslope K C hC hf y hy j hj hjN w hw v hpure hbox
  have hb := hbound j U φ JF JG hsmooth hpositive hperiod (x, y) hx p q R hR
    M H t hM hH hHM ht (hslope y hy) K C hC
    (fun k hk hkj u hu a ha hbox =>
      hf (n04PositiveGeometry_angularGraphInverse (φ x) y) (hmap hy)
        k hk (hkj.trans hjN) u hu a ha hbox) hj w hw v hpure hbox
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hmajor j hjN M hM) (parameterHeightWeight_nonneg hH _))
    (pow_nonneg (zero_le_one.trans ht) _))

end ContinuousFlexibility.Analysis
