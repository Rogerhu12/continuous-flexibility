import ContinuousFlexibility.Radial.InnerCentralBufferData
import ContinuousFlexibility.Radial.InnerCentralFlux

/-!
# Central raw coefficient bounds with the actual density drift

One coefficient controls the full-model inverse, the two masses, the
physical velocity and the inverse square root of the drift-corrected
cut energy. It grows at most linearly in the far cut, whereas the
actual action grows quadratically in that cut. The comparison input
for the inward energy is exactly the mass/C lower bound supplied by R09.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements

def innerCentralBufferCoefficient (X₀ C : ℝ) : ℝ :=
  1 + innerCentralModelInverseConstant + (64 + 16 * centralRadiusA ^ 2) + X₀ +
    centralRadiusWeightConstant * (1 + X₀) + 2 * C

def innerCentralBufferCoefficientLinearConstant (C : ℝ) : ℝ :=
  2 + innerCentralModelInverseConstant + (64 + 16 * centralRadiusA ^ 2) +
    2 * centralRadiusWeightConstant + 2 * C

theorem innerCentralBufferCoefficient_base {X₀ C : ℝ} (hX : 0 ≤ X₀) (hC : 0 ≤ C) :
    1 + 2 * C ≤ innerCentralBufferCoefficient X₀ C ∧
      innerCentralModelInverseConstant ≤ innerCentralBufferCoefficient X₀ C ∧
      64 + 16 * centralRadiusA ^ 2 ≤ innerCentralBufferCoefficient X₀ C ∧
      X₀ ≤ innerCentralBufferCoefficient X₀ C ∧
      centralRadiusWeightConstant * (1 + X₀) ≤ innerCentralBufferCoefficient X₀ C := by
  have hB := innerCentralModelInverseConstant_pos
  have hυ : 0 ≤ centralRadiusWeightConstant * (1 + X₀) :=
    mul_nonneg centralRadiusWeightConstant_pos.le (by linarith only [hX])
  dsimp only [innerCentralBufferCoefficient]
  constructor
  · nlinarith only [hB, hX, hυ, sq_nonneg centralRadiusA]
  constructor
  · nlinarith only [hX, hυ, hC, sq_nonneg centralRadiusA]
  constructor
  · nlinarith only [hB, hX, hυ, hC]
  constructor
  · nlinarith only [hB, hυ, hC, sq_nonneg centralRadiusA]
  · nlinarith only [hB, hX, hC, sq_nonneg centralRadiusA]

theorem innerCentralBufferCoefficient_bounds {n : ℕ} (hn : 1 ≤ n)
    {X₀ C : ℝ} (hX : 8 ≤ X₀) (hC : 0 ≤ C) :
    let B := innerCentralBufferData n X₀
    let c := innerCentralBufferCoefficient X₀ C
    1 ≤ c ∧ B.B₀ ≤ c ∧ B.layerBound ≤ c ∧
      (∀ i, (B.mass i)⁻¹ ≤ c) ∧
      (∀ i, B.mass i ≤ c * (1 + 2 * n)) ∧
      centralRadiusWeightConstant * (1 + X₀) ≤ c := by
  dsimp only
  have hX0 : 0 ≤ X₀ := (by norm_num : (0 : ℝ) ≤ 8).trans hX
  have hc := innerCentralBufferCoefficient_base hX0 hC
  have hc1 : 1 ≤ innerCentralBufferCoefficient X₀ C :=
    (by linarith only [hC] : (1 : ℝ) ≤ 1 + 2 * C).trans hc.1
  have hj := innerCentralBuffer_frequency hn
  have hj0 : (0 : ℝ) ≤ 2 * n := (by norm_num : (0 : ℝ) ≤ 2).trans hj
  have hm4 := innerCentralCapMass_ge_four hj hX
  refine ⟨hc1, hc.2.1, hc.2.2.1, ?_, ?_, hc.2.2.2.2⟩
  · intro i
    apply (show (innerCentralCapMass (2 * n) X₀)⁻¹ ≤ 1 from ?_).trans hc1
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one
      ((by norm_num : (1 : ℝ) ≤ 4).trans hm4)
  · intro i
    change innerCentralCapMass (2 * n) X₀ ≤ innerCentralBufferCoefficient X₀ C * (1 + 2 * n)
    calc
      innerCentralCapMass (2 * n) X₀ ≤ X₀ * (2 * n) := by
        unfold innerCentralCapMass
        nlinarith only [mul_nonneg hj0 hX0]
      _ ≤ innerCentralBufferCoefficient X₀ C * (2 * n) :=
        mul_le_mul_of_nonneg_right hc.2.2.2.1 hj0
      _ ≤ innerCentralBufferCoefficient X₀ C * (1 + 2 * n) :=
        mul_le_mul_of_nonneg_left (by linarith) (zero_le_one.trans hc1)

/-- Both outward signs are handled by the same actual drift estimate.
The far-cut condition is chosen for the universal R09 constant C. -/
theorem innerCentralBuffer_inverse_sqrt_energy_le {n : ℕ} (hn : 1 ≤ n)
    {X₀ C α : ℝ} (hX : 8 ≤ X₀) (hC : 0 < C) (i : Fin 2)
    (hfar : 2 * C * centralRadiusA ≤ innerCentralCapMass (2 * n) X₀)
    (hα : innerCentralCapMass (2 * n) X₀ / C ≤ α) :
    (sqrt (α + bufferSign i * centralRadiusA))⁻¹ ≤ innerCentralBufferCoefficient X₀ C := by
  let mass := innerCentralCapMass (2 * n) X₀
  let k := α + bufferSign i * centralRadiusA
  have hm4 : 4 ≤ mass := innerCentralCapMass_ge_four (innerCentralBuffer_frequency hn) hX
  have hm : 0 < mass := (by norm_num : (0 : ℝ) < 4).trans_le hm4
  have hαfar : 2 * centralRadiusA ≤ α := by
    apply (show 2 * centralRadiusA ≤ mass / C from ?_).trans hα
    apply (le_div_iff₀ hC).mpr
    nlinarith only [hfar]
  have hd := innerCentral_drift_bounds i hαfar
  have hk : mass / (2 * C) ≤ k := by
    calc
      mass / (2 * C) = (mass / C) / 2 := by rw [div_div, mul_comm C 2]
      _ ≤ α / 2 := div_le_div_of_nonneg_right hα (by norm_num)
      _ ≤ k := hd.2.1
  have hi : k⁻¹ ≤ 2 * C := by
    have hrec : k⁻¹ ≤ (mass / (2 * C))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le
        (div_pos hm (mul_pos (by norm_num) hC)) hk
    have hmInv : mass⁻¹ ≤ 1 := by
      simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one
        ((by norm_num : (1 : ℝ) ≤ 4).trans hm4)
    calc
      k⁻¹ ≤ (mass / (2 * C))⁻¹ := hrec
      _ = (2 * C) * mass⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ 2 * C := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hmInv
          (mul_nonneg (by norm_num) hC.le)
  have hs : (sqrt k)⁻¹ ≤ 1 + k⁻¹ := by
    rw [← sqrt_inv k]
    exact sqrt_le_iff.mpr ⟨add_nonneg zero_le_one (inv_nonneg.mpr hd.1.le),
      by nlinarith only [inv_nonneg.mpr hd.1.le, sq_nonneg (k⁻¹)]⟩
  exact hs.trans ((add_le_add_left hi 1).trans
    (innerCentralBufferCoefficient_base (by linarith only [hX]) hC.le).1)

theorem innerCentralBufferCoefficientLinearConstant_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < innerCentralBufferCoefficientLinearConstant C := by
  unfold innerCentralBufferCoefficientLinearConstant
  have hB := innerCentralModelInverseConstant_pos
  have hυ := centralRadiusWeightConstant_pos
  nlinarith only [hB, hυ, hC, sq_nonneg centralRadiusA]

/-- Enlarging the central far cut only gives linear raw coefficient
growth, while its proved action is j*X₀²/16. -/
theorem innerCentralBufferCoefficient_le_linear {X₀ C : ℝ} (hX : 1 ≤ X₀) (hC : 0 ≤ C) :
    innerCentralBufferCoefficient X₀ C ≤ innerCentralBufferCoefficientLinearConstant C * X₀ := by
  let K : ℝ := 1 + innerCentralModelInverseConstant + (64 + 16 * centralRadiusA ^ 2) +
    centralRadiusWeightConstant + 2 * C
  have hK : 0 ≤ K := by
    dsimp only [K]
    have hB := innerCentralModelInverseConstant_pos
    have hυ := centralRadiusWeightConstant_pos
    nlinarith only [hB, hυ, hC, sq_nonneg centralRadiusA]
  have hKX : K ≤ K * X₀ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hX hK
  calc
    innerCentralBufferCoefficient X₀ C = K + (1 + centralRadiusWeightConstant) * X₀ := by
      dsimp only [innerCentralBufferCoefficient, K]
      ring
    _ ≤ K * X₀ + (1 + centralRadiusWeightConstant) * X₀ :=
      add_le_add_right hKX _
    _ = innerCentralBufferCoefficientLinearConstant C * X₀ := by
      dsimp only [innerCentralBufferCoefficientLinearConstant, K]
      ring

end ContinuousFlexibility.Radial
