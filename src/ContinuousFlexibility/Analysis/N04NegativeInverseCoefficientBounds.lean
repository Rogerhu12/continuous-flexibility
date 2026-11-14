import ContinuousFlexibility.Analysis.N04NegativeInverseReferenceBounds

/-! Uniform coefficient preparation for the actual inverse prefix. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

/-- The scalar normalization, affine target and Jacobian reciprocal
can share one envelope before the piece and its material sample are chosen. -/
theorem n04NegativeInverse_common_coefficient
    {C I L : ℝ} (hC : 0 < C) (hI : 0 < I) (hL : 0 < L) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ E : ℝ, 1 ≤ E →
      (2 + L * E ^ L) * (1 + C * E ^ C) ≤ B * E ^ B ∧
        I * E ^ I ≤ B * E ^ B ∧
        1 + L * E ^ L ≤ B * E ^ B ∧
        C * E ^ C ≤ B * E ^ B := by
  obtain ⟨D, hD, hpack⟩ := coefficientEnvelope_pack ((2 + L) * (1 + C)) (L + C)
  let B : ℝ := 1 + D + I + L
  have hB : 1 ≤ B := by dsimp only [B]; linarith
  have hDB : D ≤ B := by dsimp only [B]; linarith
  have hIB : I ≤ B := by dsimp only [B]; linarith
  refine ⟨B, hB, ?_⟩
  intro E hE
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have hEp : 0 < E := zero_lt_one.trans_le hE
  have hEL : 1 ≤ E ^ L := Real.one_le_rpow hE hL.le
  have hEC : 1 ≤ E ^ C := Real.one_le_rpow hE hC.le
  have hcost : D * E ^ D ≤ B * E ^ B :=
    mul_le_mul hDB (Real.rpow_le_rpow_of_exponent_le hE hDB)
      (Real.rpow_nonneg hE0 _) (zero_le_one.trans hB)
  have hp : (2 + L * E ^ L) * (1 + C * E ^ C) ≤ B * E ^ B := by
    calc
      _ ≤ ((2 + L) * E ^ L) * ((1 + C) * E ^ C) :=
        mul_le_mul (by nlinarith) (by nlinarith)
          (by positivity) (by positivity)
      _ = ((2 + L) * (1 + C)) * E ^ (L + C) := by
        rw [Real.rpow_add hEp]
        ring
      _ ≤ D * E ^ D := hpack E hE
      _ ≤ B * E ^ B := hcost
  refine ⟨hp, ?_, ?_, ?_⟩
  · exact mul_le_mul hIB (Real.rpow_le_rpow_of_exponent_le hE hIB)
      (Real.rpow_nonneg hE0 _) (zero_le_one.trans hB)
  · have hnonneg : 0 ≤ L * E ^ L := mul_nonneg hL.le (Real.rpow_nonneg hE0 _)
    have hc : 0 ≤ C * E ^ C := mul_nonneg hC.le (Real.rpow_nonneg hE0 _)
    exact (show 1 + L * E ^ L ≤
      (2 + L * E ^ L) * (1 + C * E ^ C) from by nlinarith).trans hp
  · have hnonneg : 0 ≤ L * E ^ L := mul_nonneg hL.le (Real.rpow_nonneg hE0 _)
    have hc : 0 ≤ C * E ^ C := mul_nonneg hC.le (Real.rpow_nonneg hE0 _)
    exact (show C * E ^ C ≤
      (2 + L * E ^ L) * (1 + C * E ^ C) from by nlinarith).trans hp

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- Extra height factors in a finite graph partition have a uniform
coefficient bound. The first parameter height factor remains explicit. -/
theorem negativeInverse_height_uniform :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ m,
      G.W.U.H (G.W.U.sample ((G.V 0).cell m)) ^ (3 / 4 : ℝ) ≤ L := by
  have hU := isMaterialData_enlargedMaterialData G.W.radial.1 G.W.hT
  obtain ⟨C, hC, hc⟩ := material_sample_height_coefficient_power_bounded
    G.W.radial.1 hU (G.V 0).cell 0 (by norm_num : (0 : ℝ) < 3 / 4)
  refine ⟨1 + C, by linarith, ?_⟩
  intro m
  have hm : G.W.U.H (G.W.U.sample ((G.V 0).cell m)) ^ (3 / 4 : ℝ) ≤ C := by
    simpa only [Real.rpow_zero, mul_one] using hc m
  exact hm.trans (le_add_of_nonneg_left zero_le_one)

end N04RealizationGauge
end ContinuousFlexibility.Analysis
