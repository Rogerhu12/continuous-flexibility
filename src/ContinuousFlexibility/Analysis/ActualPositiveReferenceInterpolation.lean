module

public import ContinuousFlexibility.Analysis.ActualPositiveReferenceEndpointData
public import ContinuousFlexibility.Analysis.PositiveReferenceFiniteRadialJets

/-!
# A fixed positive reference map from the actual certified neighbors

The existing endpoint-source choice is used on both sides of the same
positive component. The radial finite-jet factory then supplies one
genuine map to the canonical interval (0,1), with positive reference
height and the prescribed ordinary joint jets at both endpoint circles.
The height is exactly one on the specified closed forbidden set.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

/-- Fixed finite reference data are constructed from the original atlas.
The source choice precedes the interpolation, and no state or derivative
bound on a desired final transport is an input. -/
theorem n04Coordinates_exists_actual_positive_reference_interpolation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    (i : N04PositiveComponent D.a D.b (deriv D.w))
    (j : ∀ side, N04PositiveEndpointSource C i side)
    {F : Set ℝ} (hF : IsClosed F)
    (hl : n04PositiveLeft i ∉ F) (hr : n04PositiveRight i ∉ F)
    {n : ℕ} (hn : 1 ≤ n) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ∃ Y H : ℝ → ℝ,
      PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
        (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1)
        (n04PositiveLeft i) (n04PositiveRight i) 0 1 ∧
      (∀ x ∈ F, H x = 1) ∧
      (∀ side θ k, k ≤ n →
        iteratedFDeriv ℝ k (fun p : PolarPoint => Y p.1)
            (n04PositiveEndpoint i side, θ) =
          iteratedFDeriv ℝ k (n04PositiveReferenceSourceCoordinate (j side) K)
            (n04PositiveEndpoint i side, θ)) ∧
      (∀ side θ k, k ≤ n →
        iteratedFDeriv ℝ k (fun p : PolarPoint => H p.1)
            (n04PositiveEndpoint i side, θ) =
          iteratedFDeriv ℝ k (n04PositiveReferenceSourceHeight (j side) K)
            (n04PositiveEndpoint i side, θ)) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  have hD := n04b_profileGeometry_of_through03 hN
  have hf : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  have hlr : n04PositiveLeft i < n04PositiveRight i :=
    (n04PositiveComponent_bounds hf i).2.1
  have hd (side : Bool) := n04Coordinates_actual_positive_reference_source_data
    hT hS hN hfield e (j side)
  exact exists_positiveReferenceFiniteRadialJets
    (a := fun side => n04PositiveSourceLeft (j side))
    (b := fun side => n04PositiveSourceRight (j side))
    (y := fun side => n04PositiveReferenceSourceCoordinate (j side) K)
    (h := fun side => n04PositiveReferenceSourceHeight (j side) K)
    hF hl hr hlr
    (fun side => (hd side).1)
    (fun side => (hd side).2.1)
    (fun side => (hd side).2.2.1)
    (fun side => (hd side).2.2.2.1)
    (fun side => (hd side).2.2.2.2.1)
    (fun side => (hd side).2.2.2.2.2.1)
    (fun side x hx θ => (hd side).2.2.2.2.2.2.1 x hx θ)
    (fun side x hx θ => (hd side).2.2.2.2.2.2.2.1 x hx θ)
    (fun side => (hd side).2.2.2.2.2.2.2.2.1)
    (fun side => (hd side).2.2.2.2.2.2.2.2.2.1)
    (fun side => (hd side).2.2.2.2.2.2.2.2.2.2)
    hn

end ContinuousFlexibility.Analysis

