import ContinuousFlexibility.Analysis.ActualPositiveReferenceMidpointMaterialData
import ContinuousFlexibility.Analysis.PositiveReferencePrescribedCosts

/-!
# The actual positive reference interpolation at a material width

The same old atlas supplies both endpoint sources. Their actual finite
jets and both interval width costs have one envelope at the physical
midpoint sample. That envelope determines one displayed Taylor width,
one integral coordinate and one clipped-log height. Their finite joint
endpoint jets and global value costs refer to those same functions.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04Coordinates_retained_positive_reference_prescribed_material_costs
    {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S₀ K₀ q length) (hSelected : IsSelectedTail S₀)
    (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {T : MaterialData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {base loss : ℕ} {ε K : ℝ}
    (hT : IsMaterialData Γ.reference T) (hS : IsPhysicalSpaces Γ.reference T S)
    (hN : NonlinearPropertiesThrough03 Γ.reference T S C R L base loss ε)
    (hfield : N04bFieldRegularity Γ.reference S C L base ε)
    (e : ℕ ≃ N04PieceIndex Γ.reference) (hK : 0 < K)
    (hhost : ∀ m, Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells (C.cell m))
    (hoptical : ∀ m x, x ∈ Ioo (C.left m) (C.right m) →
      K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) *
        min (x - C.left m) (C.right m - x) ≤
          -deriv Γ.reference.w x / (x * Γ.reference.w x)) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∀ n : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      ∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (j : ℕ), n04PositiveMidpoint i ∈ Γ.reference.cells j →
      ∀ src : (side : Bool) → N04PositiveEndpointSource C i side,
        let A := n04bActualTypedAtlas hT hS hN hfield e
        let W := C0 * T.E0 (T.sample j)
        let U := B * W ^ B
        let δ := positiveReferenceTaylorWidth n
          (n04PositiveLeft i) (n04PositiveRight i) U⁻¹ U
        let ys := fun side : Bool => radialEndpointTaylorSlice (n + 1)
          (n04PositiveEndpoint i side) (n04PositiveReferenceSourceCoordinate (src side) A)
        let hs := fun side : Bool => radialEndpointTaylorSlice (n + 1)
          (n04PositiveEndpoint i side) (n04PositiveReferenceSourceHeight (src side) A)
        let Y := positiveReferenceCoordinate (n04PositiveLeft i) (n04PositiveRight i) δ
          (deriv (ys false)) (deriv (ys true))
        let H := positiveReferenceHeight (n04PositiveLeft i) (n04PositiveRight i) δ
          (hs false) (hs true)
        let Z := ((24 + 16 * ((n + 2 : ℕ) : ℝ)) * B ^ 2) * W ^ (2 * B)
        PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
          (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1)
          (n04PositiveLeft i) (n04PositiveRight i) 0 1 ∧
        (∀ (side : Bool) (θ : ℝ) (k : ℕ), k ≤ n + 1 →
          iteratedFDeriv ℝ k (fun p : PolarPoint => Y p.1) (n04PositiveEndpoint i side, θ) =
            iteratedFDeriv ℝ k (n04PositiveReferenceSourceCoordinate (src side) A)
              (n04PositiveEndpoint i side, θ)) ∧
        (∀ (side : Bool) (θ : ℝ) (k : ℕ), k ≤ n + 1 →
          iteratedFDeriv ℝ k (fun p : PolarPoint => H p.1) (n04PositiveEndpoint i side, θ) =
            iteratedFDeriv ℝ k (n04PositiveReferenceSourceHeight (src side) A)
              (n04PositiveEndpoint i side, θ)) ∧
        0 < δ ∧ δ ≤ 1 ∧ δ⁻¹ ≤ Z ∧
        ∀ x : ℝ, 0 < deriv Y x ∧ deriv Y x ≤ Z ∧ (deriv Y x)⁻¹ ≤ Z ∧
          0 < H x ∧ H x ≤ Z ∧ (H x)⁻¹ ≤ Z := by
  obtain ⟨C0, hC0, hfloor, hdata⟩ :=
    n04Coordinates_retained_positive_reference_midpoint_material_data
      P hSelected hband hq hΓ hw hcoordinates hT hS hN hfield e hK hhost hoptical
  refine ⟨C0, hC0, hfloor, ?_⟩
  intro n
  obtain ⟨B, hB, hfinite⟩ := hdata (n + 1)
  refine ⟨B, hB, ?_⟩
  intro i j hmid src
  let A := n04bActualTypedAtlas hT hS hN hfield e
  let W : ℝ := C0 * T.E0 (T.sample j)
  let U : ℝ := B * W ^ B
  let a : Bool → ℝ := fun side => n04PositiveSourceLeft (src side)
  let b : Bool → ℝ := fun side => n04PositiveSourceRight (src side)
  let y : Bool → PolarPoint → ℝ :=
    fun side => n04PositiveReferenceSourceCoordinate (src side) A
  let h : Bool → PolarPoint → ℝ :=
    fun side => n04PositiveReferenceSourceHeight (src side) A
  have hinput := hfinite i j hmid src
  have hU : 1 ≤ U := hinput.1
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hD := n04b_profileGeometry_of_through03 hN
  have hf : Continuous (deriv Γ.reference.w) := hD.2.2.1.1.continuous_deriv (by simp)
  have hlr : n04PositiveLeft i < n04PositiveRight i :=
    (n04PositiveComponent_bounds hf i).2.1
  have hd (side : Bool) :=
    n04Coordinates_actual_positive_reference_source_data hT hS hN hfield e (src side)
  have hgeometry := positiveReferenceFiniteRadialJets_prescribed n
    (κ := U⁻¹) (M := U) (a := a) (b := b) (y := y) (h := h)
    hlr (inv_pos.mpr hUpos) hUpos.le
    (fun side => (hd side).1)
    (fun side => (hd side).2.1)
    (fun side => (hd side).2.2.1)
    (fun side => (hd side).2.2.2.1)
    (fun side => (hd side).2.2.2.2.1)
    (fun side => (hd side).2.2.2.2.2.1)
    (fun side x hx θ => (hd side).2.2.2.2.2.2.1 x hx θ)
    (fun side x hx θ => (hd side).2.2.2.2.2.2.2.1 x hx θ)
    (fun side => (hd side).2.2.2.2.2.2.2.2.1)
    (fun side => (hinput.2.2.2 side).1)
    (fun side => (hinput.2.2.2 side).2.1)
    (fun side => (hinput.2.2.2 side).2.2.1)
    (fun side => (hinput.2.2.2 side).2.2.2)
  have hcosts := positiveReferenceFiniteRadialJets_prescribed_costs n
    (κ := U⁻¹) (M := U) (U := U) (a := a) (b := b) (y := y) (h := h)
    hlr (inv_pos.mpr hUpos) hUpos.le hU le_rfl (by simp only [inv_inv])
    hinput.2.1 hinput.2.2.1
    (fun side => (hd side).1)
    (fun side => (hd side).2.1)
    (fun side => (hd side).2.2.1)
    (fun side => (hd side).2.2.2.1)
    (fun side => (hd side).2.2.2.2.1)
    (fun side => (hd side).2.2.2.2.2.1)
    (fun side x hx θ => (hd side).2.2.2.2.2.2.1 x hx θ)
    (fun side x hx θ => (hd side).2.2.2.2.2.2.2.1 x hx θ)
    (fun side => (hd side).2.2.2.2.2.2.2.2.1)
    (fun side => (hinput.2.2.2 side).1)
    (fun side => (hinput.2.2.2 side).2.1)
    (fun side => (hinput.2.2.2 side).2.2.1)
    (fun side => (hinput.2.2.2 side).2.2.2)
  let Dn : ℝ := 24 + 16 * ((n + 2 : ℕ) : ℝ)
  let Z : ℝ := (Dn * B ^ 2) * W ^ (2 * B)
  have hquad : Dn * U ^ 2 ≤ Z :=
    positiveReferencePrescribedCost_material_bound n
      (U := U) (K := B) (W := W) hUpos.le le_rfl (hfloor j)
  have hn0 : 0 ≤ ((n + 2 : ℕ) : ℝ) := by positivity
  have hnD : ((n + 2 : ℕ) : ℝ) ≤ Dn := by dsimp only [Dn]; linarith only [hn0]
  have htwoD : (2 : ℝ) ≤ Dn := by dsimp only [Dn]; linarith only [hn0]
  have hfourD : (4 : ℝ) ≤ Dn := by dsimp only [Dn]; linarith only [hn0]
  have hU2 : U ≤ U ^ 2 := by
    calc
      U = U * 1 := (mul_one U).symm
      _ ≤ U * U := mul_le_mul_of_nonneg_left hU hUpos.le
      _ = U ^ 2 := by ring
  have hlinear {d : ℝ} (hd : 0 ≤ d) (hdD : d ≤ Dn) : d * U ≤ Z :=
    ((mul_le_mul_of_nonneg_left hU2 hd).trans
      (mul_le_mul_of_nonneg_right hdD (sq_nonneg U))).trans hquad
  have hheight : 4 * U ^ 2 ≤ Z :=
    (mul_le_mul_of_nonneg_right hfourD (sq_nonneg U)).trans hquad
  refine ⟨hgeometry.1, hgeometry.2.1, hgeometry.2.2.1,
    hcosts.1, hcosts.2.1, hcosts.2.2.1.trans hquad, ?_⟩
  intro x
  have hx := hcosts.2.2.2 x
  exact ⟨hx.1, hx.2.1.trans (hlinear hn0 hnD),
    hx.2.2.1.trans (hlinear (by norm_num) htwoD), hx.2.2.2.1,
    hx.2.2.2.2.1.trans hheight, hx.2.2.2.2.2.trans hheight⟩

end ContinuousFlexibility.Analysis
