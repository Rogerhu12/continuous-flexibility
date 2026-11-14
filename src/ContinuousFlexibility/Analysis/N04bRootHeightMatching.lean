module

public import ContinuousFlexibility.Analysis.N04bRootTravelMatching
public import ContinuousFlexibility.Analysis.N04bRootHeightSymmetry
public import ContinuousFlexibility.Analysis.N04bConstructedRootDensity

/-!
# Actual matching of the smooth root chart and height

The smooth extended root chart equals the explicit global travel chart
on its physical collar. The transported root speed factor equals the
actual corrected characteristic half-gap, so the smooth height quotient
also equals the explicit global interior height. These identities provide
the overlap equalities needed for literal chart and height gluing.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04b_rootTravelPower_eq_rootCoordinate (s : ℝ) :
    rootTravelPower s = n04bRootCoordinate s := by
  unfold rootTravelPower n04bRootCoordinate
  congr 1
  ring

namespace N04bRootCoordinateProperties

variable {d c₀ : PolarPoint → ℝ} {hL : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
  {R σ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
  (H : N04bRootCoordinateProperties d c₀ hL Φ R σ G)

include H

/-- The actual root-flow transport equations supply the entire smooth
height quotient identity; no normal-form premise is used. -/
theorem height_factor (a : PolarPoint → ℝ) {p : PolarPoint}
    (hp : 0 < p.1) (hχ : 0 < rootOddCoefficient G p) :
    rootHeightFactor a G p =
      a p * (Real.sqrt p.1 * c₀ p) * extendedRootScale G p := by
  apply rootHeightFactor_eq_characteristicFactor (d := d p)
    (v := Real.sqrt p.1 * c₀ p) a H.smooth Real.pi_ne_zero
    (fun r _ => H.odd_period r) (fun r _ => H.even_period r) hp hχ
  · simpa only [rootPhysicalSpeed, one_mul] using H.transport 1 p.1 p.2 hp
  · simpa only [rootPhysicalSpeed, neg_one_mul, one_mul, neg_mul, sub_eq_add_neg] using
      H.transport (-1) p.1 p.2 hp
  · exact (H.angular_positive 1 p.1 p.2 hp).ne'
  · exact (H.angular_positive (-1) p.1 p.2 hp).ne'

end N04bRootCoordinateProperties

/-- The actual left smooth chart agrees with the global root chart on
the physical side, where the genuine root coefficient is positive. -/
theorem n04b_left_root_chart_matching
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {z : AnnularState S × ℝ} {m : ℕ}
    {ρ : ℝ} {d c₀ : PolarPoint → ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (H : N04bRootCoordinateProperties d c₀ (stateLeftChart S z.1 m)
      (fun θ x => L.minusFlow z m (C.left m + x) θ) ρ (-1) G)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) ρ) (θ : ℝ)
    (hxp : 0 < x) (hχ : 0 < rootOddCoefficient G (x, θ)) :
    extendedRootEvenOddChart G (x, θ) =
      n04bRootPhysicalChart (n04bActualTravelChart S C L z m)
        (C.travel m) false (C.left m + x, θ) := by
  have he := extendedRootEvenOddChart_eq_rootTravelPower G hxp hχ.le
  rw [← n04b_left_root_travel_matching H hx θ] at he
  change extendedRootEvenOddChart G (x, θ) =
    (n04bRootCoordinate ((n04bActualTravelChart S C L z m (C.left m + x, θ)).1),
      (n04bActualTravelChart S C L z m (C.left m + x, θ)).2)
  simpa only [n04b_rootTravelPower_eq_rootCoordinate] using he

/-- At the right root the exact N03 return shift changes travel to its
complement, so the inward smooth chart is the right global root chart. -/
theorem n04b_right_root_chart_matching
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    {ρ : ℝ} (hspan : C.left m < C.right m - ρ)
    {d c₀ : PolarPoint → ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (H : N04bRootCoordinateProperties d c₀ (rightChartCandidate S C z m)
      (n04bRightRootFlow C L z m) ρ 1 G)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) ρ) (θ : ℝ)
    (hxp : 0 < x) (hχ : 0 < rootOddCoefficient G (x, θ)) :
    extendedRootEvenOddChart G (x, θ) =
      n04bRootPhysicalChart (n04bActualTravelChart S C L z m)
        (C.travel m) true (C.right m - x, θ) := by
  have he := extendedRootEvenOddChart_eq_rootTravelPower G hxp hχ.le
  rw [n04b_right_root_travel_matching hT hS h03 hfield hz hs m hspan H hx θ] at he
  change extendedRootEvenOddChart G (x, θ) =
    (n04bRootCoordinate
      (C.travel m - (n04bActualTravelChart S C L z m (C.right m - x, θ)).1),
      (n04bActualTravelChart S C L z m (C.right m - x, θ)).2)
  simpa only [n04b_rootTravelPower_eq_rootCoordinate] using he

/-- At the left root, the actual retained speed factor identifies the
positive smooth boundary height with the defined interior height. -/
theorem n04b_left_root_height_matching
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {z : AnnularState S × ℝ} {m : ℕ}
    {ρ : ℝ} {d c₀ : PolarPoint → ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (H : N04bRootCoordinateProperties d c₀ (stateLeftChart S z.1 m)
      (fun θ x => L.minusFlow z m (C.left m + x) θ) ρ (-1) G)
    (hgap : ∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
      Real.sqrt x * c₀ (x, θ) =
        n04bCharacteristicHalfGap (L.coefficients z) (C.left m + x, θ))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) ρ) (θ : ℝ)
    (hxp : 0 < x) (hχ : 0 < rootOddCoefficient G (x, θ)) :
    rootSmoothHeight (n04bRootLeadingCoefficient L z (C.left m) 1) G (x, θ) =
      n04bRootPhysicalHeight (L.coefficients z)
        (n04bCharacteristicHalfGap (L.coefficients z))
        (n04bActualTravelChart S C L z m) (C.travel m) false (C.left m + x, θ) := by
  unfold rootSmoothHeight
  rw [H.height_factor _ hxp hχ, extendedRootScale,
    n04b_left_root_chart_matching H hx θ hxp hχ, hgap x hx θ]
  simp only [n04bRootLeadingCoefficient, rootProfileShift, one_mul,
    n04bRootPhysicalHeight, div_eq_mul_inv]

/-- At the right root the same actual half-gap is retained. The radial
orientation changes the chart, while the positive height matches exactly. -/
theorem n04b_right_root_height_matching
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    {ρ : ℝ} (hspan : C.left m < C.right m - ρ)
    {d c₀ : PolarPoint → ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (H : N04bRootCoordinateProperties d c₀ (rightChartCandidate S C z m)
      (n04bRightRootFlow C L z m) ρ 1 G)
    (hgap : ∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
      Real.sqrt x * c₀ (x, θ) =
        n04bCharacteristicHalfGap (L.coefficients z) (C.right m - x, θ))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) ρ) (θ : ℝ)
    (hxp : 0 < x) (hχ : 0 < rootOddCoefficient G (x, θ)) :
    rootSmoothHeight (n04bRootLeadingCoefficient L z (C.right m) (-1)) G (x, θ) =
      n04bRootPhysicalHeight (L.coefficients z)
        (n04bCharacteristicHalfGap (L.coefficients z))
        (n04bActualTravelChart S C L z m) (C.travel m) true (C.right m - x, θ) := by
  unfold rootSmoothHeight
  rw [H.height_factor _ hxp hχ, extendedRootScale,
    n04b_right_root_chart_matching hT hS h03 hfield hz hs m hspan H hx θ hxp hχ,
    hgap x hx θ]
  simp only [n04bRootLeadingCoefficient, rootProfileShift, neg_one_mul,
    ← sub_eq_add_neg, n04bRootPhysicalHeight, div_eq_mul_inv]

end ContinuousFlexibility.Analysis
