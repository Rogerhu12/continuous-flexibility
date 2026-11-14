module

public import ContinuousFlexibility.Analysis.N04bRootHeightMatching

/-!
# Actual matched collars at both physical roots

These existence theorems construct one common two-sided collar for the
ordinary chart, its positive Jacobian and angular derivative, and the
positive smooth height. On the physical side both functions agree with
the actual global travel construction. Every input is from Through03,
the physical/material data, or raw coefficient regularity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A convenient name for the conclusions already proved by the actual
root-height collar construction. This is not an upstream field premise. -/
abbrev N04bRootChartHeightCollar
    (D : ReferenceData) {S : PhysicalSpacesData} (L : ReturnCorrectionData S)
    (z : AnnularState S × ℝ) (r₀ ι : ℝ) (G : ℝ × ℝ × ℝ → ℝ) (δ : ℝ) : Prop :=
  ∀ x θ : ℝ, |x| < δ →
    rootProfileShift r₀ ι (x, θ) ∈ annularOpen D ∧
    ContDiffAt ℝ ∞ (extendedRootEvenOddChart G) (x, θ) ∧
    0 < extendedRootOddCoefficient G (x, θ) ∧
    0 < planeJacobian (extendedRootEvenOddChart G) (x, θ) ∧
    0 < angularPartial (extendedRootEven G) (x, θ) ∧
    0 < rootAngularProduct G (x, θ) ∧
    ContDiffAt ℝ ∞ (rootSmoothHeight (n04bRootLeadingCoefficient L z r₀ ι) G) (x, θ) ∧
    0 < rootSmoothHeight (n04bRootLeadingCoefficient L z r₀ ι) G (x, θ) ∧
    rootSmoothHeight (n04bRootLeadingCoefficient L z r₀ ι) G (x, θ) ^ 2 *
      rootHeightFactor (n04bRootLeadingCoefficient L z r₀ ι) G (x, θ) = 1

/-- The left smooth chart and height are constructed on a full uniform
periodic collar and match the literal global formulas inside. -/
theorem n04b_exists_left_matched_root_collar_with_physical_factors
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∃ (ρ δ : ℝ) (d c₀ : PolarPoint → ℝ) (G : ℝ × ℝ × ℝ → ℝ),
      0 < ρ ∧ C.left m + ρ < C.right m ∧
      N04bRootCoordinateProperties d c₀ (stateLeftChart S z.1 m)
        (fun θ x => L.minusFlow z m (C.left m + x) θ) ρ (-1) G ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ c₀ ∧
      (∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
        Real.sqrt x * c₀ (x, θ) =
          n04bCharacteristicHalfGap (L.coefficients z) (C.left m + x, θ)) ∧
      (∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
        d (x, θ) = n04bCharacteristicDrift (L.coefficients z) (C.left m + x, θ)) ∧
      0 < δ ∧ δ ≤ ρ ∧ N04bRootChartHeightCollar D L z (C.left m) 1 G δ ∧
      ∀ x ∈ Ioo (0 : ℝ) δ, ∀ θ : ℝ,
        extendedRootEvenOddChart G (x, θ) =
          n04bRootPhysicalChart (n04bActualTravelChart S C L z m)
            (C.travel m) false (C.left m + x, θ) ∧
        rootSmoothHeight (n04bRootLeadingCoefficient L z (C.left m) 1) G (x, θ) =
          n04bRootPhysicalHeight (L.coefficients z)
            (n04bCharacteristicHalfGap (L.coefficients z))
            (n04bActualTravelChart S C L z m) (C.travel m) false (C.left m + x, θ) := by
  obtain ⟨ρ, d, c₀, G, hρ, hspan, H, hd, hc, hgap, hdrift⟩ :=
    n04b_exists_left_physical_root_coordinate_with_physical_factors hT hS h03 hfield hz hs m
  have hcontrol : controlGeometryConditions D S C := h03.1.1.2.2.2.1
  have hr₀ : C.left m ∈ Ioo D.a D.b :=
    ⟨(hcontrol.1 m).1, (hcontrol.1 m).2.1.trans (hcontrol.1 m).2.2⟩
  obtain ⟨δ₀, hδ₀, hcollar⟩ :=
    n04b_exists_actual_root_height_collar (ι := (1 : ℝ)) hfield hz hs hr₀ H
  let δ := min ρ δ₀
  have hδ : 0 < δ := lt_min_iff.mpr ⟨hρ, hδ₀⟩
  have hδρ : δ ≤ ρ := min_le_left _ _
  have hδ₀le : δ ≤ δ₀ := min_le_right _ _
  refine ⟨ρ, δ, d, c₀, G, hρ, hspan, H, hd, hc, hgap, hdrift, hδ, hδρ, ?_, ?_⟩
  · intro x θ hx
    exact hcollar x θ (hx.trans_le hδ₀le)
  · intro x hx θ
    have hxc : x ∈ Icc (0 : ℝ) ρ := ⟨hx.1.le, hx.2.le.trans hδρ⟩
    have hsmall : |x| < δ₀ := by
      rw [abs_of_pos hx.1]
      exact hx.2.trans_le hδ₀le
    have hχ : 0 < rootOddCoefficient G (x, θ) := by
      have he : 0 < extendedRootOddCoefficient G (x, θ) :=
        (hcollar x θ hsmall).2.2.1
      rwa [extendedRootOddCoefficient_of_nonneg G hx.1.le] at he
    exact ⟨n04b_left_root_chart_matching H hxc θ hx.1 hχ,
      n04b_left_root_height_matching H hgap hxc θ hx.1 hχ⟩

/-- Projection retaining the established matched-collar interface. -/
theorem n04b_exists_left_matched_root_collar
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∃ (ρ δ : ℝ) (d c₀ : PolarPoint → ℝ) (G : ℝ × ℝ × ℝ → ℝ),
      0 < ρ ∧ C.left m + ρ < C.right m ∧
      N04bRootCoordinateProperties d c₀ (stateLeftChart S z.1 m)
        (fun θ x => L.minusFlow z m (C.left m + x) θ) ρ (-1) G ∧
      0 < δ ∧ δ ≤ ρ ∧ N04bRootChartHeightCollar D L z (C.left m) 1 G δ ∧
      ∀ x ∈ Ioo (0 : ℝ) δ, ∀ θ : ℝ,
        extendedRootEvenOddChart G (x, θ) =
          n04bRootPhysicalChart (n04bActualTravelChart S C L z m)
            (C.travel m) false (C.left m + x, θ) ∧
        rootSmoothHeight (n04bRootLeadingCoefficient L z (C.left m) 1) G (x, θ) =
          n04bRootPhysicalHeight (L.coefficients z)
            (n04bCharacteristicHalfGap (L.coefficients z))
            (n04bActualTravelChart S C L z m) (C.travel m) false (C.left m + x, θ) := by
  obtain ⟨ρ, δ, d, c₀, G, hρ, hspan, H, _, _, _, _, hδ, hδρ, hcollar, hmatch⟩ :=
    n04b_exists_left_matched_root_collar_with_physical_factors hT hS h03 hfield hz hs m
  exact ⟨ρ, δ, d, c₀, G, hρ, hspan, H, hδ, hδρ, hcollar, hmatch⟩

/-- The right collar has the same actual smooth overlap, with the
genuine inward chart supplied by the exact right return normalization. -/
theorem n04b_exists_right_matched_root_collar_with_physical_factors
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∃ (ρ δ : ℝ) (d c₀ : PolarPoint → ℝ) (G : ℝ × ℝ × ℝ → ℝ),
      0 < ρ ∧ C.left m < C.right m - ρ ∧
      N04bRootCoordinateProperties d c₀ (rightChartCandidate S C z m)
        (n04bRightRootFlow C L z m) ρ 1 G ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ c₀ ∧
      (∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
        Real.sqrt x * c₀ (x, θ) =
          n04bCharacteristicHalfGap (L.coefficients z) (C.right m - x, θ)) ∧
      (∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
        d (x, θ) = -n04bCharacteristicDrift (L.coefficients z) (C.right m - x, θ)) ∧
      0 < δ ∧ δ ≤ ρ ∧ N04bRootChartHeightCollar D L z (C.right m) (-1) G δ ∧
      ∀ x ∈ Ioo (0 : ℝ) δ, ∀ θ : ℝ,
        extendedRootEvenOddChart G (x, θ) =
          n04bRootPhysicalChart (n04bActualTravelChart S C L z m)
            (C.travel m) true (C.right m - x, θ) ∧
        rootSmoothHeight (n04bRootLeadingCoefficient L z (C.right m) (-1)) G (x, θ) =
          n04bRootPhysicalHeight (L.coefficients z)
            (n04bCharacteristicHalfGap (L.coefficients z))
            (n04bActualTravelChart S C L z m) (C.travel m) true (C.right m - x, θ) := by
  obtain ⟨ρ, d, c₀, G, hρ, hspan, H, hd, hc, hgap, hdrift⟩ :=
    n04b_exists_right_physical_root_coordinate_with_physical_factors hT hS h03 hfield hz hs m
  have hcontrol : controlGeometryConditions D S C := h03.1.1.2.2.2.1
  have hr₀ : C.right m ∈ Ioo D.a D.b :=
    ⟨(hcontrol.1 m).1.trans (hcontrol.1 m).2.1, (hcontrol.1 m).2.2⟩
  obtain ⟨δ₀, hδ₀, hcollar⟩ :=
    n04b_exists_actual_root_height_collar (ι := (-1 : ℝ)) hfield hz hs hr₀ H
  let δ := min ρ δ₀
  have hδ : 0 < δ := lt_min_iff.mpr ⟨hρ, hδ₀⟩
  have hδρ : δ ≤ ρ := min_le_left _ _
  have hδ₀le : δ ≤ δ₀ := min_le_right _ _
  refine ⟨ρ, δ, d, c₀, G, hρ, hspan, H, hd, hc, hgap, hdrift, hδ, hδρ, ?_, ?_⟩
  · intro x θ hx
    exact hcollar x θ (hx.trans_le hδ₀le)
  · intro x hx θ
    have hxc : x ∈ Icc (0 : ℝ) ρ := ⟨hx.1.le, hx.2.le.trans hδρ⟩
    have hsmall : |x| < δ₀ := by
      rw [abs_of_pos hx.1]
      exact hx.2.trans_le hδ₀le
    have hχ : 0 < rootOddCoefficient G (x, θ) := by
      have he : 0 < extendedRootOddCoefficient G (x, θ) :=
        (hcollar x θ hsmall).2.2.1
      rwa [extendedRootOddCoefficient_of_nonneg G hx.1.le] at he
    exact ⟨n04b_right_root_chart_matching hT hS h03 hfield hz hs m hspan H hxc θ hx.1 hχ,
      n04b_right_root_height_matching hT hS h03 hfield hz hs m hspan H hgap hxc θ hx.1 hχ⟩

/-- Projection retaining the established matched-collar interface. -/
theorem n04b_exists_right_matched_root_collar
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∃ (ρ δ : ℝ) (d c₀ : PolarPoint → ℝ) (G : ℝ × ℝ × ℝ → ℝ),
      0 < ρ ∧ C.left m < C.right m - ρ ∧
      N04bRootCoordinateProperties d c₀ (rightChartCandidate S C z m)
        (n04bRightRootFlow C L z m) ρ 1 G ∧
      0 < δ ∧ δ ≤ ρ ∧ N04bRootChartHeightCollar D L z (C.right m) (-1) G δ ∧
      ∀ x ∈ Ioo (0 : ℝ) δ, ∀ θ : ℝ,
        extendedRootEvenOddChart G (x, θ) =
          n04bRootPhysicalChart (n04bActualTravelChart S C L z m)
            (C.travel m) true (C.right m - x, θ) ∧
        rootSmoothHeight (n04bRootLeadingCoefficient L z (C.right m) (-1)) G (x, θ) =
          n04bRootPhysicalHeight (L.coefficients z)
            (n04bCharacteristicHalfGap (L.coefficients z))
            (n04bActualTravelChart S C L z m) (C.travel m) true (C.right m - x, θ) := by
  obtain ⟨ρ, δ, d, c₀, G, hρ, hspan, H, _, _, _, _, hδ, hδρ, hcollar, hmatch⟩ :=
    n04b_exists_right_matched_root_collar_with_physical_factors hT hS h03 hfield hz hs m
  exact ⟨ρ, δ, d, c₀, G, hρ, hspan, H, hδ, hδρ, hcollar, hmatch⟩

end ContinuousFlexibility.Analysis
