module

public import ContinuousFlexibility.Analysis.ActualPositiveReferenceInterpolation

/-!
# One fixed radial reference family with its actual endpoint jets

The same certified neighbors provide every endpoint datum. The reference
family is selected once, before the state. This qualitative existence
result retains the exact finite jets for subsequent geometry assembly;
it does not assign material bounds to the interpolation widths.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

def N04PositiveReferenceFamily
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (K : CanonicalData S)
    (j : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (n : ℕ) (Y H : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ) : Prop :=
  ∀ i,
    PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1 ∧
    (∀ side θ k, k ≤ n →
      iteratedFDeriv ℝ k (fun p : PolarPoint => Y i p.1) (n04PositiveEndpoint i side, θ) =
        iteratedFDeriv ℝ k (n04PositiveReferenceSourceCoordinate (j i side) K)
          (n04PositiveEndpoint i side, θ)) ∧
    (∀ side θ k, k ≤ n →
      iteratedFDeriv ℝ k (fun p : PolarPoint => H i p.1) (n04PositiveEndpoint i side, θ) =
        iteratedFDeriv ℝ k (n04PositiveReferenceSourceHeight (j i side) K)
          (n04PositiveEndpoint i side, θ))

theorem n04Coordinates_exists_positive_reference_family
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    (j : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ Y H : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ,
      N04PositiveReferenceFamily (n04bActualTypedAtlas hT hS hN hfield e) j n Y H := by
  classical
  have hex := fun i => n04Coordinates_exists_actual_positive_reference_interpolation
    hT hS hN hfield e i (j i) (F := ∅) isClosed_empty (by simp) (by simp) hn
  dsimp only at hex
  choose Y H hgeometry hforbidden hY hH using hex
  exact ⟨Y, H, fun i => ⟨hgeometry i, hY i, hH i⟩⟩

end ContinuousFlexibility.Analysis
