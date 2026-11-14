module

public import ContinuousFlexibility.Analysis.CanonicalPositiveReferenceFamily
public import ContinuousFlexibility.Analysis.PositiveReferenceFinitePrescribed
public import ContinuousFlexibility.Analysis.PositiveComponentMaterialCell

/-!
# Actual finite reference family for the displayed material width

The finite certificate is the one retained by the material producer.
This proof fixes its original C0 and B, the actual midpoint cell and the
actual endpoint sources. The resulting Y and H are exactly its displayed
Taylor interpolation; no qualitative family is selected in their place.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04Coordinates_actual_positive_prescribed_reference_family
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D) (n : ℕ) (C0 B : ℝ)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (hcell : ∀ i, n04PositiveMidpoint i ∈ D.cells (cell i))
    (src : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (hfinite : ∀ (i : N04PositiveComponent D.a D.b (deriv D.w))
        (j : ℕ), n04PositiveMidpoint i ∈ D.cells j →
        ∀ src : (side : Bool) → N04PositiveEndpointSource C i side,
          let A := n04bActualTypedAtlas hT hS hN hfield e
          let U := B * (C0 * T.E0 (T.sample j)) ^ B
          1 ≤ U ∧ (n04PositiveRight i - n04PositiveLeft i)⁻¹ ≤ U ∧
            n04PositiveRight i - n04PositiveLeft i ≤ U ∧
            ∀ side : Bool,
              U⁻¹ ≤ radialBoundaryJet (n04PositiveReferenceSourceCoordinate (src side) A)
                (n04PositiveEndpoint i side) 1 0 ∧
              U⁻¹ ≤ radialBoundaryJet (n04PositiveReferenceSourceHeight (src side) A)
                (n04PositiveEndpoint i side) 0 0 ∧
              (∀ k : ℕ, 1 ≤ k → k ≤ n + 1 →
                |radialBoundaryJet (n04PositiveReferenceSourceCoordinate (src side) A)
                  (n04PositiveEndpoint i side) k 0| ≤ U) ∧
              ∀ k : ℕ, k ≤ n + 1 →
                |radialBoundaryJet (n04PositiveReferenceSourceHeight (src side) A)
                  (n04PositiveEndpoint i side) k 0| ≤ U) :
    let A := n04bActualTypedAtlas hT hS hN hfield e
    let U := fun i => B * (C0 * T.E0 (T.sample (cell i))) ^ B
    let δ := fun i => positiveReferenceTaylorWidth n
      (n04PositiveLeft i) (n04PositiveRight i) (U i)⁻¹ (U i)
    let ys := fun i side => radialEndpointTaylorSlice (n + 1)
      (n04PositiveEndpoint i side) (n04PositiveReferenceSourceCoordinate (src i side) A)
    let hs := fun i side => radialEndpointTaylorSlice (n + 1)
      (n04PositiveEndpoint i side) (n04PositiveReferenceSourceHeight (src i side) A)
    let Y := fun i => positiveReferenceCoordinate (n04PositiveLeft i) (n04PositiveRight i)
      (δ i) (deriv (ys i false)) (deriv (ys i true))
    let H := fun i => positiveReferenceHeight (n04PositiveLeft i) (n04PositiveRight i)
      (δ i) (hs i false) (hs i true)
    N04PositiveReferenceFamily A src (n + 1) Y H := by
  let A := n04bActualTypedAtlas hT hS hN hfield e
  let U := fun i => B * (C0 * T.E0 (T.sample (cell i))) ^ B
  let δ := fun i => positiveReferenceTaylorWidth n
    (n04PositiveLeft i) (n04PositiveRight i) (U i)⁻¹ (U i)
  let ys := fun i side => radialEndpointTaylorSlice (n + 1)
    (n04PositiveEndpoint i side) (n04PositiveReferenceSourceCoordinate (src i side) A)
  let hs := fun i side => radialEndpointTaylorSlice (n + 1)
    (n04PositiveEndpoint i side) (n04PositiveReferenceSourceHeight (src i side) A)
  let Y := fun i => positiveReferenceCoordinate (n04PositiveLeft i) (n04PositiveRight i)
    (δ i) (deriv (ys i false)) (deriv (ys i true))
  let H := fun i => positiveReferenceHeight (n04PositiveLeft i) (n04PositiveRight i)
    (δ i) (hs i false) (hs i true)
  have hfamily : N04PositiveReferenceFamily A src (n + 1) Y H := by
    intro i
    let a : Bool → ℝ := fun side => n04PositiveSourceLeft (src i side)
    let b : Bool → ℝ := fun side => n04PositiveSourceRight (src i side)
    let y : Bool → PolarPoint → ℝ :=
      fun side => n04PositiveReferenceSourceCoordinate (src i side) A
    let h : Bool → PolarPoint → ℝ :=
      fun side => n04PositiveReferenceSourceHeight (src i side) A
    have hinput := hfinite i (cell i) (hcell i) (src i)
    have hU : 1 ≤ U i := hinput.1
    have hUpos : 0 < U i := zero_lt_one.trans_le hU
    have hD := n04b_profileGeometry_of_through03 hN
    have hf : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
    have hlr : n04PositiveLeft i < n04PositiveRight i :=
      (n04PositiveComponent_bounds hf i).2.1
    have hd (side : Bool) :=
      n04Coordinates_actual_positive_reference_source_data hT hS hN hfield e (src i side)
    have hfactory := positiveReferenceFiniteRadialJets_prescribed n
      (κ := (U i)⁻¹) (M := U i) (a := a) (b := b) (y := y) (h := h)
      hlr (inv_pos.mpr hUpos) hUpos.le
      (fun side => (hd side).1) (fun side => (hd side).2.1)
      (fun side => (hd side).2.2.1) (fun side => (hd side).2.2.2.1)
      (fun side => (hd side).2.2.2.2.1) (fun side => (hd side).2.2.2.2.2.1)
      (fun side x hx θ => (hd side).2.2.2.2.2.2.1 x hx θ)
      (fun side x hx θ => (hd side).2.2.2.2.2.2.2.1 x hx θ)
      (fun side => (hd side).2.2.2.2.2.2.2.2.1)
      (fun side => (hinput.2.2.2 side).1) (fun side => (hinput.2.2.2 side).2.1)
      (fun side => (hinput.2.2.2 side).2.2.1)
      (fun side => (hinput.2.2.2 side).2.2.2)
    exact ⟨hfactory.1, hfactory.2.1, hfactory.2.2.1⟩
  exact hfamily

end ContinuousFlexibility.Analysis
