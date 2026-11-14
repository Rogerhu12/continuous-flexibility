import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Scalar envelope operations for the coordinate realization

The sample floor is explicit: coefficient and exponent constants can be
enlarged together only when the actual sampled envelope is at least one.
These lemmas contain no coordinate data or final geometric estimate.
-/

namespace ContinuousFlexibility.Analysis

/-- Add a reference jet and a height-attenuated difference jet. The
height envelope is chosen before the state displacement and sample. -/
theorem n04Realization_referenceAndDifferenceEnvelope
    {A B M : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ E H rho u v : ℝ,
      1 ≤ E → H ≤ M → 0 ≤ rho →
      |u| ≤ A * E ^ A → |v| ≤ B * E ^ B * H * rho →
      |v + u| ≤ C * E ^ C * (1 + rho) := by
  let R : ℝ := A + B
  let Q : ℝ := A + B * M
  obtain ⟨C, hC, hcost⟩ := coefficientEnvelope_pack Q R
  refine ⟨C, hC, fun E H rho u v hE hHM hrho hu hv => ?_⟩
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have hu' : |u| ≤ A * E ^ R := hu.trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_right hB)) hA)
  have hv' : |v| ≤ B * M * E ^ R * rho := by
    calc
      |v| ≤ B * E ^ B * H * rho := hv
      _ ≤ B * E ^ B * M * rho := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hHM
          (mul_nonneg hB (Real.rpow_nonneg hE0 _))) hrho
      _ = B * M * E ^ B * rho := by ring
      _ ≤ B * M * E ^ R * rho := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_left hA))
          (mul_nonneg hB hM)) hrho
  have hpositive : 0 ≤ E ^ R := Real.rpow_nonneg hE0 _
  have hmiddle : B * M * E ^ R * rho + A * E ^ R ≤ Q * E ^ R * (1 + rho) := by
    dsimp only [Q]
    nlinarith only [mul_nonneg (mul_nonneg hA hpositive) hrho,
      mul_nonneg (mul_nonneg hB hM) hpositive]
  exact ((abs_add_le v u).trans (add_le_add hv' hu')).trans
    (hmiddle.trans (mul_le_mul_of_nonneg_right (hcost E hE)
      (add_nonneg zero_le_one hrho)))

end ContinuousFlexibility.Analysis
