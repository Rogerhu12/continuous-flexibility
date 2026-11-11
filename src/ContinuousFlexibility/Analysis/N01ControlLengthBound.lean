import ContinuousFlexibility.Analysis.ActualRadialCellComparison
import ContinuousFlexibility.Analysis.N01TravelLowerBound
import ContinuousFlexibility.Analysis.N01RadialFlow

/-!
# A lower length bound for each actual negative component

The inverse-profile cell bound and a global first-derivative bound give
an upper bound for the actual optical speed. The frequency-one return
margin gives a lower bound for its full integral. Their combination
forces a lower interval length in every actual containing radial cell.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance : NormedSpace ℝ ℝ := NormedField.toNormedSpace

open Set MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff

theorem IsAccumulatingProfile.opticalSpeed_cell_bound
    {D : ReferenceData} (hRef : IsAccumulatingProfile D) :
    ∃ K A : ℝ, 0 < K ∧ 0 < A ∧ ∀ j r, r ∈ D.cells j →
      opticalSpeed D.w r ≤ K * radialE (D.cellIndex j) ^ A := by
  obtain ⟨B, hdata⟩ := hRef
  rcases hdata with ⟨hgeom, hpart, hB, _, _, _, _, _, _, hinv, _⟩
  have hw : ContDiff ℝ ∞ D.w := hgeom.2.2.1.1
  have hc : Continuous (fun r : ℝ => |deriv D.w r|) :=
    (hw.continuous_deriv (by simp)).abs
  obtain ⟨W, hW⟩ := (isCompact_Icc : IsCompact (Icc D.a D.b)).bddAbove_image hc.continuousOn
  let W0 := 1 + |W|
  have hW0 : 0 < W0 := by dsimp only [W0]; positivity
  let K0 := W0 * D.a⁻¹ * B 0
  have hK0 : 0 < K0 := mul_pos (mul_pos hW0 (inv_pos.mpr hgeom.1)) (hB 0)
  refine ⟨1 + K0, B 0, by linarith only [hK0], hB 0, fun j r hr => ?_⟩
  have hcore : r ∈ radialCore D := hpart.2.2.2.1 j hr
  have hrpos : 0 < r := hgeom.1.trans hcore.1
  have hwpos : 0 < D.w r := hgeom.2.2.2.2.1 r hcore
  have hwd : |deriv D.w r| ≤ W0 := by
    have hh := hW ⟨r, ⟨hcore.1.le, hcore.2.le⟩, rfl⟩
    dsimp only [W0]
    linarith only [hh, le_abs_self W]
  have hri : r⁻¹ ≤ D.a⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hgeom.1 hcore.1.le
  have hwi : (D.w r)⁻¹ ≤ B 0 * radialE (D.cellIndex j) ^ B 0 := by
    have hh : |(D.w r)⁻¹| ≤ B 0 * radialE (D.cellIndex j) ^ B 0 := by
      simpa only [radialJet] using hinv j r hr 0
    exact (le_abs_self _).trans hh
  have hE1 : 1 ≤ radialE (D.cellIndex j) ^ B 0 :=
    Real.one_le_rpow (one_le_radialE_of_nat _) (hB 0).le
  have hq : -deriv D.w r / (r * D.w r) ≤ K0 * radialE (D.cellIndex j) ^ B 0 := by
    calc
      _ ≤ |-deriv D.w r / (r * D.w r)| := le_abs_self _
      _ = |deriv D.w r| * r⁻¹ * (D.w r)⁻¹ := by
        rw [abs_div, abs_neg, abs_of_pos (mul_pos hrpos hwpos), div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ (W0 * D.a⁻¹) * (B 0 * radialE (D.cellIndex j) ^ B 0) :=
        mul_le_mul
          (mul_le_mul hwd hri (inv_pos.mpr hrpos).le hW0.le)
          hwi (inv_pos.mpr hwpos).le (mul_nonneg hW0.le (inv_pos.mpr hgeom.1).le)
      _ = _ := by dsimp only [K0]; ring
  have hQ : 0 ≤ K0 * radialE (D.cellIndex j) ^ B 0 :=
    mul_nonneg hK0.le (Real.rpow_nonneg (Real.exp_pos _).le _)
  have hsqrt : opticalSpeed D.w r ≤ 1 + K0 * radialE (D.cellIndex j) ^ B 0 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by linarith only [hQ], ?_⟩
    nlinarith only [hq, hQ, sq_nonneg (K0 * radialE (D.cellIndex j) ^ B 0)]
  calc
    _ ≤ 1 + K0 * radialE (D.cellIndex j) ^ B 0 := hsqrt
    _ ≤ radialE (D.cellIndex j) ^ B 0 + K0 * radialE (D.cellIndex j) ^ B 0 :=
      add_le_add hE1 le_rfl
    _ = _ := by ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.travel_le_actualCell_length
    (hN : N01Properties D T S C base loss ε) :
    ∃ K A : ℝ, 0 < K ∧ 0 < A ∧ ∀ m j,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      C.travel m ≤ K * radialE (D.cellIndex j) ^ A * (C.right m - C.left m) := by
  obtain ⟨K, A, hK, hA, hspeed⟩ := hN.1.1.opticalSpeed_cell_bound
  obtain ⟨_, hdata⟩ := hN.1.1
  have hgeom : RadialProfileGeometry D := hdata.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  refine ⟨K, A, hK, hA, fun m j hcell => ?_⟩
  have hab := (hcontrol.1 m).2.1
  have hl : 0 < C.left m := hgeom.1.trans (hcontrol.1 m).1
  have hwp : ∀ r ∈ Icc (C.left m) (C.right m), 0 < D.w r := by
    intro r hr
    exact hgeom.2.2.2.2.1 r
      ⟨(hcontrol.1 m).1.trans_le hr.1, hr.2.trans_lt (hcontrol.1 m).2.2⟩
  have hi : IntervalIntegrable (opticalSpeed D.w) volume (C.left m) (C.right m) :=
    (continuousOn_opticalSpeed_of_profile hgeom.2.2.1.1 hl hwp).intervalIntegrable_of_Icc hab.le
  have hb := intervalIntegral.integral_mono_on_of_le_Ioo hab.le hi
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => K * radialE (D.cellIndex j) ^ A) volume (C.left m) (C.right m))
    (fun r hr => hspeed j r (hcell hr))
  have htravel : C.travel m = ∫ r in C.left m..C.right m, opticalSpeed D.w r :=
    hcontrol.2.2.2.2.2.2.2.1 m
  rw [htravel]
  exact hb.trans_eq (by rw [intervalIntegral.integral_const, smul_eq_mul]; ring)

theorem N01Properties.travel_lower_bound_at_every_actualCell
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ m j,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      1 ≤ K * radialE (D.cellIndex j) ^ A * C.travel m := by
  obtain ⟨R, hR, hmargin⟩ := hN.actualCell_travel_lower_bound
  obtain ⟨B, hB, hcommon⟩ := material_actualCells_index_bound hT
  obtain ⟨K, A, hK, hA, htransfer⟩ := radialE_rpow_of_nat_sub_bound hR.le hB.le
  refine ⟨K, A, hK, hA, fun m j hj => ?_⟩
  obtain ⟨htravel, i, hi, hraw⟩ := hmargin m
  obtain ⟨r, hrl, hrh⟩ := exists_between (hN.2.2.2.1.1 m).2.1
  have hindex := hcommon i j r (hi ⟨hrl, hrh⟩) (hj ⟨hrl, hrh⟩)
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (htransfer (D.cellIndex i) (D.cellIndex j) hindex) htravel.le)

/-- Every actual containing cell gives a fixed-power lower length bound.
The constants are independent of the component and of its control label. -/
theorem N01Properties.actualCell_length_lower_bound
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T) :
    ∃ c R : ℝ, 0 < c ∧ 0 < R ∧ ∀ m j,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      c * radialE (D.cellIndex j) ^ (-R) ≤ C.right m - C.left m := by
  obtain ⟨K1, A1, hK1, hA1, hlower⟩ := hN.travel_lower_bound_at_every_actualCell hT
  obtain ⟨K2, A2, hK2, hA2, hupper⟩ := hN.travel_le_actualCell_length
  have hK : 0 < K1 * K2 := mul_pos hK1 hK2
  refine ⟨(K1 * K2)⁻¹, A1 + A2, inv_pos.mpr hK, add_pos_of_nonneg_of_pos hA1 hA2,
    fun m j hj => ?_⟩
  have hE : 0 < radialE (D.cellIndex j) := Real.exp_pos _
  have hbound : 1 ≤ (K1 * K2) * radialE (D.cellIndex j) ^ (A1 + A2) *
      (C.right m - C.left m) := by
    exact (hlower m j hj).trans
      ((mul_le_mul_of_nonneg_left (hupper m j hj)
        (mul_nonneg hK1.le (Real.rpow_nonneg hE.le A1))).trans_eq (by
          rw [Real.rpow_add hE A1 A2]
          ring))
  have hdiv : 1 / ((K1 * K2) * radialE (D.cellIndex j) ^ (A1 + A2)) ≤
      C.right m - C.left m := by
    apply (div_le_iff₀ (mul_pos hK (Real.rpow_pos_of_pos hE _))).mpr
    simpa only [mul_comm] using hbound
  simpa only [one_div, mul_inv_rev, Real.rpow_neg hE.le, mul_comm] using hdiv

end ContinuousFlexibility.Statements
