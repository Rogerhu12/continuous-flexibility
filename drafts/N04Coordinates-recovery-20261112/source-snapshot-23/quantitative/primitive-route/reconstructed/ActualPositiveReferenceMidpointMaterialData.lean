import ContinuousFlexibility.Analysis.ActualPositiveReferenceSourceMaterialData
import ContinuousFlexibility.Analysis.RetainedPositiveEndpointHostSample
import ContinuousFlexibility.Analysis.RetainedPositiveComponentMaterialWidth
import ContinuousFlexibility.Analysis.RetainedPositiveComponentInteriorEndpoints

/-!
# Actual positive reference data at the same midpoint sample

The genuine endpoint data keep the original negative host. The retained
geometry compares that host sample with the actual positive midpoint
sample, including the finitely many central pieces. One material power
then controls both endpoint data and both width costs. The retained
certificate and the same-component optical lower remain explicit.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04Coordinates_retained_positive_reference_midpoint_material_data
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
      ∀ N : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      ∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (j : ℕ), n04PositiveMidpoint i ∈ Γ.reference.cells j →
      ∀ src : (side : Bool) → N04PositiveEndpointSource C i side,
        let A := n04bActualTypedAtlas hT hS hN hfield e
        let M := B * (C0 * T.E0 (T.sample j)) ^ B
        1 ≤ M ∧
          (n04PositiveRight i - n04PositiveLeft i)⁻¹ ≤ M ∧
          n04PositiveRight i - n04PositiveLeft i ≤ M ∧
          ∀ side : Bool,
            M⁻¹ ≤ radialBoundaryJet (n04PositiveReferenceSourceCoordinate (src side) A)
              (n04PositiveEndpoint i side) 1 0 ∧
            M⁻¹ ≤ radialBoundaryJet (n04PositiveReferenceSourceHeight (src side) A)
              (n04PositiveEndpoint i side) 0 0 ∧
            (∀ n : ℕ, 1 ≤ n → n ≤ N →
              |radialBoundaryJet (n04PositiveReferenceSourceCoordinate (src side) A)
                (n04PositiveEndpoint i side) n 0| ≤ M) ∧
            ∀ n : ℕ, n ≤ N →
              |radialBoundaryJet (n04PositiveReferenceSourceHeight (src side) A)
                (n04PositiveEndpoint i side) n 0| ≤ M := by
  have hC : controlGeometryConditions Γ.reference S C := hN.1.1.2.2.2.1
  obtain ⟨C0, hC0, hfloor, hsource⟩ :=
    n04Coordinates_actual_positive_reference_source_material_data hT hS hN hfield e hK
  obtain ⟨Bw, Aw, hBw, hAw, hwidth⟩ :=
    retainedReference_positive_component_material_width
      P hSelected hband hq hΓ hw hcoordinates hC hT
  have hC0pos : 0 < C0 := zero_lt_one.trans_le hC0
  refine ⟨C0, hC0, hfloor, ?_⟩
  intro N
  obtain ⟨B₀, hB₀, hraw⟩ := hsource N
  obtain ⟨K₁, A₁, hK₁, hA₁, hsample⟩ :=
    retainedReference_positive_endpoint_host_sample_bound
      P hSelected hband hq hΓ hw hcoordinates hC hT (zero_le_one.trans hB₀)
  let D : ℝ := B₀ * C0 ^ B₀ * K₁
  have hD : 0 < D := mul_pos
    (mul_pos (zero_lt_one.trans_le hB₀) (Real.rpow_pos_of_pos hC0pos _)) hK₁
  let B : ℝ := 1 + D + A₁ + Bw + Aw
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [hD, hA₁, hBw, hAw]
  have hDB : D ≤ B := by dsimp only [B]; linarith only [hA₁, hBw, hAw]
  have hA₁B : A₁ ≤ B := by dsimp only [B]; linarith only [hD, hBw, hAw]
  have hBwB : Bw ≤ B := by dsimp only [B]; linarith only [hD, hA₁, hAw]
  have hAwB : Aw ≤ B := by dsimp only [B]; linarith only [hD, hA₁, hBw]
  refine ⟨B, hB, ?_⟩
  intro i j hmid src
  let A := n04bActualTypedAtlas hT hS hN hfield e
  let W : ℝ := C0 * T.E0 (T.sample j)
  let M : ℝ := B * W ^ B
  have hW : 1 ≤ W := hfloor j
  have hEj : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hΓ.2.1 hT j)).2.2.1
  have hEW : T.E0 (T.sample j) ≤ W := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC0 hEj.le
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hB
    (Real.one_le_rpow hW (zero_le_one.trans hB))
  have hcost {d a : ℝ} (hd : 0 ≤ d) (hdB : d ≤ B) (ha : 0 ≤ a) (haB : a ≤ B) :
      d * T.E0 (T.sample j) ^ a ≤ M := by
    calc
      _ ≤ d * W ^ a := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hEj.le hEW ha) hd
      _ ≤ d * W ^ B :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hW haB) hd
      _ ≤ B * W ^ B :=
        mul_le_mul_of_nonneg_right hdB (Real.rpow_nonneg (zero_le_one.trans hW) _)
  have hwcost := hcost hBw.le hBwB hAw hAwB
  refine ⟨hM, ((hwidth i j hmid).1).trans hwcost,
    ((hwidth i j hmid).2).trans hwcost, ?_⟩
  intro side
  obtain ⟨m, hm⟩ : ∃ m, (src side).val = some m := by
    cases ho : (src side).val with
    | none =>
        have hamb : n04PositiveEndpoint i side =
            (if side then Γ.reference.b else Γ.reference.a) := by
          simpa only [ho] using (src side).property
        have hc := (retainedReference_positive_endpoints_interior
          P hSelected hband hq hΓ hw hcoordinates i side).1
        exfalso
        cases side
        · exact (ne_of_gt hc.1) (by simpa only [Bool.false_eq_true, ↓reduceIte] using hamb)
        · exact (ne_of_lt hc.2) (by simpa only [↓reduceIte] using hamb)
    | some m => exact ⟨m, ho⟩
  have hend : n04PositiveEndpoint i side = (if side then C.left m else C.right m) := by
    simpa only [hm] using (src side).property
  have hs := hsample i side m (C.cell m) j (hhost m) hend hmid
  have hEm : 0 < T.E0 (T.sample (C.cell m)) :=
    (hT.2.1 _ (materialSample_mem_interval hΓ.2.1 hT (C.cell m))).2.2.1
  let M₀ : ℝ := B₀ * (C0 * T.E0 (T.sample (C.cell m))) ^ B₀
  have hM₀ : M₀ ≤ M := by
    calc
      _ = (B₀ * C0 ^ B₀) * T.E0 (T.sample (C.cell m)) ^ B₀ := by
        dsimp only [M₀]
        rw [Real.mul_rpow hC0pos.le hEm.le]
        ring
      _ ≤ (B₀ * C0 ^ B₀) * (K₁ * T.E0 (T.sample j) ^ A₁) :=
        mul_le_mul_of_nonneg_left hs
          (mul_nonneg (zero_le_one.trans hB₀) (Real.rpow_nonneg hC0pos.le _))
      _ = D * T.E0 (T.sample j) ^ A₁ := by dsimp only [D]; ring
      _ ≤ M := hcost hD.le hDB hA₁ hA₁B
  have hactual := hraw m (C.cell m) (hhost m) (hoptical m) i side (src side) hm
  have hpositive : 0 < M₀ := zero_lt_one.trans_le hactual.1
  have hinverse : M⁻¹ ≤ M₀⁻¹ := inv_anti₀ hpositive hM₀
  exact ⟨hinverse.trans hactual.2.1, hinverse.trans hactual.2.2.1,
    fun n hn hNn => (hactual.2.2.2.1 n hn hNn).trans hM₀,
    fun n hn => (hactual.2.2.2.2 n hn).trans hM₀⟩

end ContinuousFlexibility.Analysis
