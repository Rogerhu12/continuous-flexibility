module

public import ContinuousFlexibility.Analysis.N04NegativeChartControlledCollar
public import ContinuousFlexibility.Analysis.N01cMaterialShiftComparison

/-! The circle label and cutoff costs at the exact selected half sample. -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements

variable (W : N04RealizationStart)

theorem negativeCircleSample_half_height (e : ℕ ≃ N04PieceIndex W.D) :
    ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧ ∀ m side,
      W.T.H (W.T.sample m) ^ (3 / 4 : ℝ) ≤
        C * W.T.E0 (W.negativeHalfSample e m side) ^ P *
          W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ) := by
  obtain ⟨J, hJ, hindex⟩ := W.through03.1.1.2.2.2.2.1
  obtain ⟨Cs, Ps, hCs, hPs, hshift⟩ :=
    materialSample_weight_bound_sameExponent W.hT W.radial.1 (3 / 4 : ℝ) 0 hJ.le
  obtain ⟨Ct, Pt, hCt, hPt, hhost⟩ :=
    n04bActualTypedAtlas_negative_host_sample_weights
      W.hT W.hS W.through03 W.field e (3 / 4 : ℝ) 0 Ps hPs.le
  have hs : ∀ j, W.T.sample j ∈ W.D.cells j := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _⟩ := W.hT
    exact hs
  refine ⟨Cs * Ct, Pt, mul_pos hCs hCt, hPt, fun m side => ?_⟩
  have h₁ := hshift m (W.C.cell m) (W.T.sample (W.C.cell m)) (hs _)
    ((abs_sub_comm _ _).trans_le (hindex m))
  have h₂ := hhost (e.symm (.inl (m, side))) m side (e.apply_symm_apply _)
    (W.C.cell m) (W.host m)
  have h₁' : W.T.H (W.T.sample m) ^ (3 / 4 : ℝ) ≤
      Cs * (W.T.H (W.T.sample (W.C.cell m)) ^ (3 / 4 : ℝ) *
        W.T.E0 (W.T.sample (W.C.cell m)) ^ Ps) := by
    simpa only [Real.rpow_zero, mul_one, mul_assoc] using h₁
  have h₂' : W.T.H (W.T.sample (W.C.cell m)) ^ (3 / 4 : ℝ) *
      W.T.E0 (W.T.sample (W.C.cell m)) ^ Ps ≤
      Ct * (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ) *
        W.T.E0 (W.negativeHalfSample e m side) ^ Pt) := by
    simpa only [Real.rpow_zero, mul_one] using h₂
  have hb := h₁'.trans (mul_le_mul_of_nonneg_left h₂' hCs.le)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hb

theorem negativeCutoff_half_material (e : ℕ ≃ N04PieceIndex W.D) (n : ℕ) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ m side r,
      |iteratedDeriv n (W.cutoff.cutoff m) r| ≤
        K * W.T.E0 (W.negativeHalfSample e m side) ^ A := by
  obtain ⟨K, hK, hcutoff⟩ := W.cutoff.cutoff_jets n
  obtain ⟨B, P, hB, hP, hrad⟩ := materialSample_radialE_power_bound W.hT W.radial.1
    (mul_nonneg W.cutoff.widthPower_pos.le (Nat.cast_nonneg n))
  obtain ⟨C, A, hC, hA, hhost⟩ :=
    n04bActualTypedAtlas_negative_host_sample_E0_power
      W.hT W.hS W.through03 W.field e P hP
  refine ⟨K * B * C, A, mul_pos (mul_pos hK hB) hC, hA, fun m side r => ?_⟩
  calc
    _ ≤ K * radialE (W.D.cellIndex (W.cutoff.cell m)) ^ (W.cutoff.widthPower * n) :=
      hcutoff m r
    _ ≤ K * (B * W.T.E0 (W.T.sample (W.cutoff.cell m)) ^ P) :=
      mul_le_mul_of_nonneg_left (hrad _) hK.le
    _ ≤ K * (B * (C * W.T.E0 (W.negativeHalfSample e m side) ^ A)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (hhost (e.symm (.inl (m, side))) m side (e.apply_symm_apply _)
          (W.cutoff.cell m) (W.cutoff.component_cell m)) hB.le) hK.le
    _ = _ := by ring

end ContinuousFlexibility.Analysis.N04RealizationStart
