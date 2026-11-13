import ContinuousFlexibility.Analysis.ActualPositiveReferenceMidpointMaterialData
import ContinuousFlexibility.Analysis.PositiveReferenceTaylorAllOrderJets

/-!
# The same actual positive reference family at every spatial order

One low finite envelope is chosen before every derivative order. Its
finite-data certificate is retained explicitly so that the prescribed
geometry and value-cost factories use exactly the same width and fields.
Later orders change only the material exponent and numerical constant.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04Coordinates_retained_positive_reference_allOrder_material_jets
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
      (∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (j : ℕ), n04PositiveMidpoint i ∈ Γ.reference.cells j →
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
                  (n04PositiveEndpoint i side) k 0| ≤ U) ∧
      ∀ N : ℕ, ∃ M : ℝ, 1 ≤ M ∧
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
        ∀ k, k ≤ N → ∀ x : ℝ,
          |iteratedDeriv (k + 1) Y x| ≤ M * W ^ M ∧
          |iteratedDeriv k H x| ≤ M * W ^ M ∧
          |iteratedDeriv k (fun t => (H t)⁻¹) x| ≤ M * W ^ M := by
  obtain ⟨C0, hC0, hfloor, hdata⟩ :=
    n04Coordinates_retained_positive_reference_midpoint_material_data
      P hSelected hband hq hΓ hw hcoordinates hT hS hN hfield e hK hhost hoptical
  refine ⟨C0, hC0, hfloor, ?_⟩
  intro n
  obtain ⟨B, hB, hfinite⟩ := hdata (n + 1)
  refine ⟨B, hB, hfinite, ?_⟩
  intro N
  obtain ⟨J, hJ, hjet⟩ := exists_positiveReferenceTaylor_allOrder_jet_envelope n N
  let d : ℕ := 2 * ((3 * N + 1) * N + 2)
  let coefficient : ℝ := J * B ^ d
  let exponent : ℝ := B * (d : ℝ)
  let M : ℝ := 1 + coefficient + exponent
  have hcoefficient : 0 < coefficient :=
    mul_pos (zero_lt_one.trans_le hJ) (pow_pos (zero_lt_one.trans_le hB) _)
  have hexponent : 0 ≤ exponent := mul_nonneg (zero_le_one.trans hB) (Nat.cast_nonneg _)
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [hcoefficient, hexponent]
  have hcoefficientM : coefficient ≤ M := by dsimp only [M]; linarith only [hexponent]
  have hexponentM : exponent ≤ M := by dsimp only [M]; linarith only [hcoefficient]
  refine ⟨M, hM, ?_⟩
  intro i j hmid src
  let A := n04bActualTypedAtlas hT hS hN hfield e
  let W : ℝ := C0 * T.E0 (T.sample j)
  let U : ℝ := B * W ^ B
  let y : Bool → PolarPoint → ℝ :=
    fun side => n04PositiveReferenceSourceCoordinate (src side) A
  let h : Bool → PolarPoint → ℝ :=
    fun side => n04PositiveReferenceSourceHeight (src side) A
  let δ := positiveReferenceTaylorWidth n (n04PositiveLeft i) (n04PositiveRight i) U⁻¹ U
  let ys : Bool → ℝ → ℝ := fun side =>
    radialEndpointTaylorSlice (n + 1) (n04PositiveEndpoint i side) (y side)
  let hs : Bool → ℝ → ℝ := fun side =>
    radialEndpointTaylorSlice (n + 1) (n04PositiveEndpoint i side) (h side)
  let Y := positiveReferenceCoordinate (n04PositiveLeft i) (n04PositiveRight i) δ
    (deriv (ys false)) (deriv (ys true))
  let H := positiveReferenceHeight (n04PositiveLeft i) (n04PositiveRight i) δ
    (hs false) (hs true)
  have hW : 1 ≤ W := hfloor j
  have hinput := hfinite i j hmid src
  have hU : 1 ≤ U := hinput.1
  have hD := n04b_profileGeometry_of_through03 hN
  have hf : Continuous (deriv Γ.reference.w) := hD.2.2.1.1.continuous_deriv (by simp)
  have hlr : n04PositiveLeft i < n04PositiveRight i :=
    (n04PositiveComponent_bounds hf i).2.1
  have hd (side : Bool) :=
    n04Coordinates_actual_positive_reference_source_data hT hS hN hfield e (src side)
  have hyall (side : Bool) (k : ℕ) (hk : k ≤ n + 1) :
      |radialBoundaryJet (y side) (n04PositiveEndpoint i side) k 0| ≤ U := by
    cases k with
    | zero =>
        change |y side (n04PositiveEndpoint i side, 0)| ≤ U
        have hzero : y side (n04PositiveEndpoint i side, 0) =
            (if side then (1 : ℝ) else 0) := (hd side).2.2.2.2.2.2.2.2.1
        have hvalue : |if side then (1 : ℝ) else 0| ≤ 1 := by
          cases side <;> norm_num
        exact (congrArg (fun t : ℝ => |t|) hzero).trans_le (hvalue.trans hU)
    | succ k => exact (hinput.2.2.2 side).2.2.1 (k + 1) (Nat.succ_pos k) hk
  have hactual : ∀ k, k ≤ N → ∀ x : ℝ,
      |iteratedDeriv (k + 1) Y x| ≤ J * U ^ d ∧
      |iteratedDeriv k H x| ≤ J * U ^ d ∧
      |iteratedDeriv k (fun t => (H t)⁻¹) x| ≤ J * U ^ d :=
    hjet hlr hU hinput.2.1 y h
      (fun side => (hd side).2.2.2.2.1) (fun side => (hd side).2.2.2.2.2.1)
      (fun side => (hinput.2.2.2 side).1) (fun side => (hinput.2.2.2 side).2.1)
      hyall (fun side => (hinput.2.2.2 side).2.2.2)
  have hcost : J * U ^ d ≤ M * W ^ M := by
    calc
      _ = coefficient * W ^ exponent := by
        dsimp only [U, coefficient, exponent]
        rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hW) B d]
        ring
      _ ≤ coefficient * W ^ M := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hW hexponentM) hcoefficient.le
      _ ≤ M * W ^ M := mul_le_mul_of_nonneg_right hcoefficientM
        (Real.rpow_nonneg (zero_le_one.trans hW) _)
  change ∀ k, k ≤ N → ∀ x : ℝ,
    |iteratedDeriv (k + 1) Y x| ≤ M * W ^ M ∧
    |iteratedDeriv k H x| ≤ M * W ^ M ∧
    |iteratedDeriv k (fun t => (H t)⁻¹) x| ≤ M * W ^ M
  intro k hk x
  have hb := hactual k hk x
  exact ⟨hb.1.trans hcost, hb.2.1.trans hcost, hb.2.2.trans hcost⟩

end ContinuousFlexibility.Analysis
