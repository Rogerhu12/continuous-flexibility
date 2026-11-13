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
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  refine (n01_rootSpeed_axis_rpow_material_jets_of_component_optical
    W.hS W.hT hN X.κ_pos).elim ?_
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
  have hbLow : base ≤ low := le_max_left _ _
  have hlowS : lowS ≤ low := (le_max_left _ _).trans (le_max_right _ _)
  have hlossS : lossS ≤ low := (le_max_right _ _).trans (le_max_right _ _)
  refine (retainedReference_positive_endpoint_host_sample_bound W.P W.metadata.selected
      W.metadata.first_two one_pos W.realizes W.hw W.coordinates
      W.through03.1.1.2.2.2.1 W.hT (hA 0).le).elim ?_
  intro K₁ hKdata
  refine hKdata.elim ?_
  intro A₁ hsampleData
  have hK₁ := hsampleData.1
  have hA₁ := hsampleData.2.1
  have hsample := hsampleData.2.2
  let D : ℝ := (12 * A 0 * C0 ^ (A 0)) * K₁
  have hD : 0 < D := mul_pos (mul_pos
    (mul_pos (by norm_num : (0 : ℝ) < 12) (hA 0))
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hC0) _)) hK₁
  obtain ⟨B₀, _, hpack⟩ := coefficientEnvelope_pack D A₁
  let B : ℝ := max 1 B₀
  have hB : 1 ≤ B := le_max_left _ _
  have hB₀B : B₀ ≤ B := le_max_right _ _
  refine ⟨low, hbLow, B, hB, ?_⟩
  intro i side m hm g hg hfactor z hz hzlow R hR hstrip θ
  let r := n01ComponentRoot W.C m (!side)
  let σ := n01ComponentRootOrientation (!side)
  let c : PolarPoint → ℝ := factoredCharacteristicSpeed W.D.w g
    (stateProfile W.D W.S W.C (liftSectorParameter W.S W.C z).1)
    (stateHeight W.D W.S W.C (liftSectorParameter W.S W.C z)) r σ
  let V : ℝ := C0 * W.T.E0 (W.T.sample (W.C.cell m))
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  have hV : 1 ≤ V := hfloor _
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hEU : W.T.E0 (W.T.sample (X.cell i)) ≤ E := le_enlargedMaterialData_E0 W.T _
  have hzstate := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hzsector := hN.2.2.1.liftSectorParameter_sector z
  have hzsmall : pairGrading (stateGrading W.S) realGrading lowS
      (liftSectorParameter W.S W.C z - (W.C.referenceState, 0)) ≤ 1 :=
    (controlled_sector_displacement_grade W.S W.C z lowS).trans_le
      ((sectorPairGrading_monotone W.S hlowS z).trans hzlow)
  have hzloss : pairGrading (stateGrading W.S) realGrading (0 + lossS)
      (liftSectorParameter W.S W.C z - (W.C.referenceState, 0)) ≤ 1 :=
    (controlled_sector_displacement_grade W.S W.C z (0 + lossS)).trans_le
      ((sectorPairGrading_monotone W.S (by omega) z).trans hzlow)
  have hzero : ((0, θ) : PolarPoint) ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) :=
    ⟨⟨by linarith only [hR], by linarith only [hR]⟩, mem_univ _⟩
  have hdata := hstrip (0, θ) hzero
  have hc : 0 < c (0, θ) := factoredCharacteristicSpeed_pos
    hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.1
  have hspeed : (c (0, θ))⁻¹ ≤ 2 * A 0 * V ^ (A 0) :=
    controlled_speed_inverse_zero_bound hc (hA 0).le hV hzloss
      (hinverse (liftSectorParameter W.S W.C z) hzstate hzsector hzsmall
        m (W.C.cell m) (W.host m) (X.optical m) (!side) g hg hfactor R hR hstrip θ 0)
  have hodd := controlled_root_odd_inverse hc
    (n01RootLabel_deriv_mem_quarter_four hN hflow hzstate hzsector m (!side) θ).1
  have hend : n04PositiveEndpoint i side =
      (if side then W.C.left m else W.C.right m) := by
    simpa only [hm] using (X.src i side).property
  have hsampleBound := hsample i side m (W.C.cell m) (X.cell i)
    (W.host m) hend (X.cell_mem i)
  have hcost : 12 * A 0 * V ^ (A 0) ≤ B * E ^ B := by
    calc
      _ = (12 * A 0 * C0 ^ (A 0)) * W.T.E0 (W.T.sample (W.C.cell m)) ^ (A 0) := by
        dsimp only [V]
        rw [Real.mul_rpow (zero_le_one.trans hC0) (zero_le_one.trans (W.floor _))]
        ring
      _ ≤ (12 * A 0 * C0 ^ (A 0)) *
          (K₁ * W.T.E0 (W.T.sample (X.cell i)) ^ A₁) :=
        mul_le_mul_of_nonneg_left hsampleBound
          (mul_nonneg (mul_nonneg (by norm_num) (hA 0).le)
            (Real.rpow_nonneg (zero_le_one.trans hC0) _))
      _ = D * W.T.E0 (W.T.sample (X.cell i)) ^ A₁ := by dsimp only [D]; ring
      _ ≤ D * E ^ A₁ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (zero_le_one.trans (W.floor _)) hEU hA₁) hD.le
      _ ≤ B₀ * E ^ B₀ := hpack E hE
      _ ≤ B * E ^ B := mul_le_mul hB₀B
        (Real.rpow_le_rpow_of_exponent_le hE hB₀B)
        (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  refine ⟨hodd.1, hodd.2.trans ?_⟩
  calc
    6 * (c (0, θ))⁻¹ ≤ 6 * (2 * A 0 * V ^ (A 0)) :=
      mul_le_mul_of_nonneg_left hspeed (by norm_num : (0 : ℝ) ≤ 6)
    _ = 12 * A 0 * V ^ (A 0) := by ring
    _ ≤ B * E ^ B := hcost

end ContinuousFlexibility.Analysis
