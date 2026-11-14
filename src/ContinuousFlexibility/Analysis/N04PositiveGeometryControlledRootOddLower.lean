import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRootSpeedFactor
import ContinuousFlexibility.Analysis.N01RootLabels
import ContinuousFlexibility.Analysis.SectorParameterGeometry

/-!
# A uniform positive root coefficient before the parameter prefix

The true zeroth odd coefficient is `(2/3) c β'`. The actual root-label
slope is at least one quarter, and the existing speed-power theorem
controls `c⁻¹` on one fixed low-order box. Retained endpoint geometry
transfers that material cost to the positive component's own sample.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04ControlledRootOddStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

set_option backward.isDefEq.respectTransparency false

private theorem controlled_root_odd_inverse
    {c a : ℝ} (hc : 0 < c) (ha : (1 / 4 : ℝ) ≤ a) :
    0 < ((2 : ℝ) / 3) * c * a ∧
      (((2 : ℝ) / 3) * c * a)⁻¹ ≤ 6 * c⁻¹ := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) ha
  have hpos := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2 / 3) hc) ha0
  have hlo : c / 6 ≤ ((2 : ℝ) / 3) * c * a := by
    nlinarith only [mul_le_mul_of_nonneg_left ha hc.le]
  refine ⟨hpos, (inv_anti₀ (div_pos hc (by norm_num : (0 : ℝ) < 6)) hlo).trans_eq ?_⟩
  rw [inv_div, div_eq_mul_inv]

private theorem controlled_speed_inverse_zero_bound
    {f : PolarPoint → ℝ} {q : PolarPoint} {A V p : ℝ}
    (hf : 0 < f q) (hA : 0 ≤ A) (hV : 1 ≤ V) (hp : p ≤ 1)
    (hjet : ‖iteratedFDeriv ℝ 0 (fun y => f y ^ (-1 : ℝ)) q‖ ≤
      A * V ^ A * (1 + p)) :
    (f q)⁻¹ ≤ 2 * A * V ^ A := by
  rw [norm_iteratedFDeriv_zero, Real.rpow_neg_one,
    Real.norm_of_nonneg (inv_nonneg.mpr hf.le)] at hjet
  have hAV : 0 ≤ A * V ^ A :=
    mul_nonneg hA (Real.rpow_nonneg (zero_le_one.trans hV) _)
  have h := mul_le_mul_of_nonneg_left hp hAV
  nlinarith only [hjet, h]

private theorem controlled_sector_displacement_grade
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : StateDirections S × ℝ) (j : ℕ) :
    pairGrading (stateGrading S) realGrading j
        (liftSectorParameter S C z - (C.referenceState, 0)) =
      pairGrading (sectorGrading S) realGrading j z :=
  (congrArg (pairGrading (stateGrading S) realGrading j)
    (liftSectorParameter_sub_reference S C z)).trans
      (pairGrading_sectorParameterInclusion S j z)

private theorem controlled_root_speed_inverse_material
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε K : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hK : 0 < K) :
    ∃ C0 A : ℝ, ∃ low : ℕ, 1 ≤ C0 ∧ 0 < A ∧ base ≤ low ∧
      (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading low z ≤ 1 →
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ x ∈ Ioo (C.left m) (C.right m),
        K⁻¹ * T.E0 (T.sample j) ^ (-K) * min (x - C.left m) (C.right m - x) ≤
          -deriv D.w x / (x * D.w x)) →
      ∀ (side : Bool) (g : ℝ → ℝ), ContDiff ℝ ∞ g →
      (∀ t, -deriv D.w (n01ComponentRoot C m side +
        n01ComponentRootOrientation side * t) = t * g t) →
      ∀ R : ℝ, 0 < R →
      RootCoefficientStripConditions D.w g
        (stateProfile D S C (liftSectorParameter S C z).1)
        (stateHeight D S C (liftSectorParameter S C z))
        (n01ComponentRoot C m side) (n01ComponentRootOrientation side) R →
      ∀ θ : ℝ,
      let c := factoredCharacteristicSpeed D.w g
        (stateProfile D S C (liftSectorParameter S C z).1)
        (stateHeight D S C (liftSectorParameter S C z))
        (n01ComponentRoot C m side) (n01ComponentRootOrientation side) (0, θ)
      0 < c ∧ c⁻¹ ≤ 2 * A * (C0 * T.E0 (T.sample j)) ^ A := by
  refine (n01_rootSpeed_axis_rpow_material_jets_of_component_optical hS hT hN hK).elim ?_
  intro C0 hCdata
  refine hCdata.elim ?_
  intro lowS hlowData
  refine hlowData.elim ?_
  intro lossS hmaterial
  have hC0 := hmaterial.1
  have hfloor := hmaterial.2.1
  refine (hmaterial.2.2 (-1)).elim ?_
  intro A hAdata
  have hA := hAdata.1
  have hinverse := hAdata.2
  let low : ℕ := max base (max lowS lossS)
  have hlowS : lowS ≤ low := (le_max_left _ _).trans (le_max_right _ _)
  have hlossS : lossS ≤ low := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C0, A 0, low, hC0, hA 0, le_max_left _ _, hfloor, ?_⟩
  intro z hz hzlow m j hhost hoptical side g hg hfactor R hR hstrip θ
  have hzstate := liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl
  have hzsector := hN.2.2.1.liftSectorParameter_sector z
  have hzsmall : pairGrading (stateGrading S) realGrading lowS
      (liftSectorParameter S C z - (C.referenceState, 0)) ≤ 1 :=
    (controlled_sector_displacement_grade S C z lowS).trans_le
      ((sectorPairGrading_monotone S hlowS z).trans hzlow)
  have hzloss : pairGrading (stateGrading S) realGrading (0 + lossS)
      (liftSectorParameter S C z - (C.referenceState, 0)) ≤ 1 := by
    simpa only [zero_add] using
      (controlled_sector_displacement_grade S C z lossS).trans_le
        ((sectorPairGrading_monotone S hlossS z).trans hzlow)
  have hzero : ((0, θ) : PolarPoint) ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) :=
    ⟨⟨by linarith only [hR], by linarith only [hR]⟩, mem_univ _⟩
  have hdata := hstrip (0, θ) hzero
  have hc := factoredCharacteristicSpeed_pos
    hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.1
  exact ⟨hc, controlled_speed_inverse_zero_bound hc (hA 0).le (hfloor j) hzloss
    (hinverse (liftSectorParameter S C z) hzstate hzsector hzsmall
      m j hhost hoptical side g hg hfactor R hR hstrip θ 0)⟩

private theorem controlled_odd_sample_envelope
    {C0 A K P : ℝ} (hC0 : 1 ≤ C0) (hA : 0 < A) (hK : 0 < K) (hP : 0 ≤ P) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ e f E : ℝ, 1 ≤ e → 1 ≤ f → 1 ≤ E → f ≤ E →
      e ^ A ≤ K * f ^ P → 12 * A * (C0 * e) ^ A ≤ B * E ^ B := by
  let D : ℝ := (12 * A * C0 ^ A) * K
  have hD : 0 < D := mul_pos (mul_pos
    (mul_pos (by norm_num : (0 : ℝ) < 12) hA)
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hC0) _)) hK
  obtain ⟨B0, _, hpack⟩ := coefficientEnvelope_pack D P
  let B : ℝ := max 1 B0
  have hB : 1 ≤ B := le_max_left _ _
  have hB0B : B0 ≤ B := le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro e f E he hf hE hfE hs
  calc
    _ = (12 * A * C0 ^ A) * e ^ A := by
      rw [Real.mul_rpow (zero_le_one.trans hC0) (zero_le_one.trans he)]
      ring
    _ ≤ (12 * A * C0 ^ A) * (K * f ^ P) :=
      mul_le_mul_of_nonneg_left hs
        (mul_nonneg (mul_nonneg (by norm_num) hA.le)
          (Real.rpow_nonneg (zero_le_one.trans hC0) _))
    _ = D * f ^ P := by dsimp only [D]; ring
    _ ≤ D * E ^ P := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (zero_le_one.trans hf) hfE hP) hD.le
    _ ≤ B0 * E ^ B0 := hpack E hE
    _ ≤ B * E ^ B := mul_le_mul hB0B
      (Real.rpow_le_rpow_of_exponent_le hE hB0B)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)

private theorem controlled_odd_bound_of_speed
    {c a A V B : ℝ} (hc : 0 < c) (ha : (1 / 4 : ℝ) ≤ a)
    (hspeed : c⁻¹ ≤ 2 * A * V ^ A) (hcost : 12 * A * V ^ A ≤ B) :
    0 < (2 / 3 : ℝ) * c * a ∧ ((2 / 3 : ℝ) * c * a)⁻¹ ≤ B := by
  have hodd := controlled_root_odd_inverse hc ha
  refine ⟨hodd.1, hodd.2.trans ?_⟩
  calc
    6 * c⁻¹ ≤ 6 * (2 * A * V ^ A) :=
      mul_le_mul_of_nonneg_left hspeed (by norm_num : (0 : ℝ) ≤ 6)
    _ = 12 * A * V ^ A := by ring
    _ ≤ B := hcost

/-- Positivity and the reciprocal material cost of the actual zeroth
odd root formula. The low state order is fixed before every component,
division, state and angle, and hence before every parameter prefix. -/
theorem n04PositiveGeometry_rootOddValue_sample_inverse
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∃ B : ℝ, 1 ≤ B ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g →
      (∀ t, -deriv W.D.w (n01ComponentRoot W.C m (!side) +
        n01ComponentRootOrientation (!side) * t) = t * g t) →
      ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 →
      ∀ R : ℝ, 0 < R →
      RootCoefficientStripConditions W.D.w g
        (stateProfile W.D W.S W.C (liftSectorParameter W.S W.C z).1)
        (stateHeight W.D W.S W.C (liftSectorParameter W.S W.C z))
        (n01ComponentRoot W.C m (!side)) (n01ComponentRootOrientation (!side)) R →
      ∀ θ : ℝ,
        let χ := ((2 : ℝ) / 3) * factoredCharacteristicSpeed W.D.w g
          (stateProfile W.D W.S W.C (liftSectorParameter W.S W.C z).1)
          (stateHeight W.D W.S W.C (liftSectorParameter W.S W.C z))
          (n01ComponentRoot W.C m (!side)) (n01ComponentRootOrientation (!side)) (0, θ) *
          deriv (n01RootLabel W.S W.C (liftSectorParameter W.S W.C z) m (!side)) θ
        0 < χ ∧ χ⁻¹ ≤ B * W.U.E0 (W.U.sample (X.cell i)) ^ B := by
  have hN : N01Properties W.D W.T W.S W.C base W.loss ε :=
    n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  refine (controlled_root_speed_inverse_material W.hS W.hT hN X.κ_pos).elim ?_
  intro C0 hCdata
  refine hCdata.elim ?_
  intro A hAdata
  refine hAdata.elim ?_
  intro low hmaterial
  have hC0 := hmaterial.1
  have hA := hmaterial.2.1
  have hbLow := hmaterial.2.2.1
  have hspeed := hmaterial.2.2.2.2
  refine (ContinuousFlexibility.Radial.retainedReference_positive_endpoint_host_sample_bound
      W.P W.metadata.selected W.metadata.first_two one_pos W.realizes W.hw W.coordinates
      W.through03.1.1.2.2.2.1 W.hT hA.le).elim ?_
  intro K hKdata
  refine hKdata.elim ?_
  intro P hsampleData
  have hK := hsampleData.1
  have hP := hsampleData.2.1
  have hsample := hsampleData.2.2
  refine (controlled_odd_sample_envelope hC0 hA hK hP).elim ?_
  intro B hBdata
  have hB := hBdata.1
  have hpack := hBdata.2
  refine ⟨low, hbLow, B, hB, ?_⟩
  intro i side m hm g hg hfactor z hz hzlow R hR hstrip θ
  have hc := hspeed z hz hzlow m (W.C.cell m) (W.host m) (X.optical m)
    (!side) g hg hfactor R hR hstrip θ
  have hend : n04PositiveEndpoint i side =
      (if side then W.C.left m else W.C.right m) := by
    simpa only [hm] using (X.src i side).property
  have hsampleBound := hsample i side m (W.C.cell m) (X.cell i)
    (W.host m) hend (X.cell_mem i)
  have hEU : W.T.E0 (W.T.sample (X.cell i)) ≤ W.U.E0 (W.U.sample (X.cell i)) :=
    le_enlargedMaterialData_E0 W.T _
  have hcost := hpack (W.T.E0 (W.T.sample (W.C.cell m)))
    (W.T.E0 (W.T.sample (X.cell i))) (W.U.E0 (W.U.sample (X.cell i)))
    (W.floor _) (W.floor _) ((W.floor _).trans hEU) hEU hsampleBound
  exact controlled_odd_bound_of_speed hc.1
    (n01RootLabel_deriv_mem_quarter_four hN hflow
      (liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl)
      (hN.2.2.1.liftSectorParameter_sector z) m (!side) θ).1 hc.2 hcost

end ContinuousFlexibility.Analysis
