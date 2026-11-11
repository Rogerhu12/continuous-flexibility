import ContinuousFlexibility.Radial.FixedCentralModelColumnCost
import ContinuousFlexibility.Radial.InnerModelCoefficientEnvelope

/-!
# A fixed quadratic frequency cost for the original central columns

All coefficients are selected before the tail and the physical
reference.  The actual R09 remainder is bounded from its mass, inverse
and velocity coefficients, without a new normalized remainder premise.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set ContinuousFlexibility.Statements
open scoped ContDiff

def fixedCentralRawCoefficient (T B₀ C : ℝ) : ℝ :=
  65 + |B₀| + |T| + 2 * |C| + centralRadiusWeightConstant * (1 + |T|)

def fixedCentralPolynomialColumnConstant (T B₀ C K : ℝ) : ℝ :=
  sqrt 12 * (centralRadiusWeightConstant * (1 + |T|)) * sqrt 2 +
    ((sqrt 12 + 1) * (2 * |K| * (1 + 2 * |C|))) *
      fixedCentralRawCoefficient T B₀ C ^ 8

theorem fixedCentralPolynomialColumnConstant_nonneg (T B₀ C K : ℝ) :
    0 ≤ fixedCentralPolynomialColumnConstant T B₀ C K := by
  unfold fixedCentralPolynomialColumnConstant
  have h := centralRadiusWeightConstant_pos
  positivity

theorem fixedCentralModelColumnEnvelope_polynomial_bound
    {B : FixedCentralBorder} {q : ℕ} {T B₀ C K : ℝ}
    (hq : 1 ≤ q) (hT : 8 ≤ T) (hC : 0 < C) (hK : 0 ≤ K)
    (hB : BufferHypotheses (B.modelBuffer q T B₀))
    (M : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K)
    (he : ∀ i, 0 < fixedCentralModelCutEnergy M i ∧
      (M.column i).inwardEnergy ≤ 2 * fixedCentralModelCutEnergy M i)
    (i : Fin 2) :
    fixedCentralModelColumnEnvelope M i ≤
      fixedCentralPolynomialColumnConstant T B₀ C K * (1 + 2 * (q : ℝ)) ^ 2 := by
  let coeff := fixedCentralRawCoefficient T B₀ C
  let j : ℝ := 2 * (q : ℝ)
  let U : ℝ := centralRadiusWeightConstant * (1 + T)
  have hT0 : 0 ≤ T := by linarith only [hT]
  have hB0 : 0 ≤ B₀ := hB.2.2.1.le
  have hU : 0 ≤ U := mul_nonneg centralRadiusWeightConstant_pos.le
    (by linarith only [hT])
  have hc : 1 ≤ coeff ∧ B₀ ≤ coeff ∧ (64 : ℝ) ≤ coeff ∧ T ≤ coeff ∧
      U ≤ coeff ∧ 1 + 2 * C ≤ coeff := by
    dsimp only [coeff, fixedCentralRawCoefficient]
    rw [abs_of_nonneg hB0, abs_of_nonneg hT0, abs_of_nonneg hC.le]
    dsimp only [U] at hU ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hB0, hT0, hC, hU]
  have hc0 : 0 ≤ coeff := zero_le_one.trans hc.1
  have hj : (2 : ℝ) ≤ j := by
    dsimp only [j]
    exact_mod_cast (by omega : 2 ≤ 2 * q)
  have hj0 : 0 ≤ j := (by norm_num : (0 : ℝ) ≤ 2).trans hj
  have hm4 : 4 ≤ centralBufferMass j T := centralBufferMass_ge_four hj hT
  have hm1 : 1 ≤ centralBufferMass j T := (by norm_num : (1 : ℝ) ≤ 4).trans hm4
  have hmpos : 0 < centralBufferMass j T := zero_lt_one.trans_le hm1
  have hmass (k : Fin 2) : 1 ≤ (B.modelBuffer q T B₀).mass k := hm1
  have hinv (k : Fin 2) : ((B.modelBuffer q T B₀).mass k)⁻¹ ≤ coeff := by
    have h := one_div_le_one_div_of_le zero_lt_one (hmass k)
    have hi : ((B.modelBuffer q T B₀).mass k)⁻¹ ≤ 1 := by
      simpa only [one_div, inv_one] using h
    exact hi.trans hc.1
  have hupper (k : Fin 2) : (B.modelBuffer q T B₀).mass k ≤ coeff * (1 + j) := by
    change j * T / 4 ≤ coeff * (1 + j)
    have hprod := mul_le_mul_of_nonneg_left hc.2.2.2.1 hj0
    have hnonneg := mul_nonneg hc0 hj0
    nlinarith only [hprod, hnonneg, hc0]
  have hk := he i
  have hmk : centralBufferMass j T / (2 * C) ≤ fixedCentralModelCutEnergy M i := by
    have h := (div_le_iff₀ hC).mp (M.column i).inward_lower
    change centralBufferMass j T ≤ (M.column i).inwardEnergy * C at h
    have h' := mul_le_mul_of_nonneg_right hk.2 hC.le
    apply (div_le_iff₀ (mul_pos (by norm_num) hC)).mpr
    nlinarith only [h, h']
  have hki : (fixedCentralModelCutEnergy M i)⁻¹ ≤ 2 * C := by
    have hr := one_div_le_one_div_of_le
      (div_pos hmpos (mul_pos (by norm_num) hC)) hmk
    have hmInv : (centralBufferMass j T)⁻¹ ≤ 1 := by
      simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hm1
    calc
      _ ≤ (centralBufferMass j T / (2 * C))⁻¹ := by simpa only [one_div] using hr
      _ = (2 * C) * (centralBufferMass j T)⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ 2 * C := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hmInv (mul_nonneg (by norm_num) hC.le)
  have hkinv : (sqrt (fixedCentralModelCutEnergy M i))⁻¹ ≤ coeff := by
    have hs : (sqrt (fixedCentralModelCutEnergy M i))⁻¹ ≤
        1 + (fixedCentralModelCutEnergy M i)⁻¹ := by
      rw [← sqrt_inv]
      exact sqrt_le_iff.mpr
        ⟨add_nonneg zero_le_one (inv_nonneg.mpr hk.1.le), by
          nlinarith only [inv_nonneg.mpr hk.1.le,
            sq_nonneg ((fixedCentralModelCutEnergy M i)⁻¹)]⟩
    exact hs.trans ((add_le_add (le_refl 1) hki).trans hc.2.2.2.2.2)
  have hrem := innerBuffer_normalized_remainder_coefficient_envelope hB
    hC.le hK hc.1 hj0 hc.2.1 hc.2.2.1 hinv hupper
    (fun k => (buffer_action_pos hB k).le)
    hU (by norm_num : (0 : ℝ) ≤ 1) hc.2.2.2.2.1 hc.1 hk.1 hkinv i
  have hratio : sqrt (M.column i).inwardEnergy /
      sqrt (fixedCentralModelCutEnergy M i) ≤ sqrt 2 := by
    apply (div_le_iff₀ (sqrt_pos.mpr hk.1)).mpr
    simpa only [sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] using sqrt_le_sqrt hk.2
  have hUm : U / (B.modelBuffer q T B₀).mass i ≤ U := by
    simpa only [div_one] using div_le_div_of_nonneg_left hU zero_lt_one (hmass i)
  have hlead : sqrt 12 * (U / (B.modelBuffer q T B₀).mass i) *
      (sqrt (M.column i).inwardEnergy / sqrt (fixedCentralModelCutEnergy M i)) ≤
        sqrt 12 * U * sqrt 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hUm (sqrt_nonneg _)) hratio
      (div_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
      (mul_nonneg (sqrt_nonneg _) hU)
  have hpoly : 1 ≤ (1 + j) ^ 2 := by nlinarith only [hj0, sq_nonneg j]
  have hlead' := (mul_le_mul_of_nonneg_left hpoly
    (mul_nonneg (mul_nonneg (sqrt_nonneg 12) hU) (sqrt_nonneg 2)))
  have h := add_le_add (hlead.trans (by simpa only [mul_one] using hlead')) hrem
  simpa only [fixedCentralModelColumnEnvelope, fixedCentralPolynomialColumnConstant,
    abs_of_nonneg hT0, abs_of_nonneg hC.le, abs_of_nonneg hK,
    neg_zero, exp_zero, mul_one, U, j, coeff, ← add_mul] using h

section Chart

variable (B : FixedCentralBorder) (D : ReferenceData)
  (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
  {n : ℕ} (G : InnerRadialChainGeometry D n) (central : Fin (n + 1))
  (q : ℕ) {T B₀ C K : ℝ} (hT : 8 ≤ T)
  (hcap : sqrt centralOscillatorA + 2 ≤ T)
  (hcolumn : referenceColumn D = fixedCentralColumn B.chi)
  (hcore : Ioo (centralRadius (-T)) (centralRadius T) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc (-T) T,
    D.w (centralRadius x) = 1 * centralDensityRoot x ^ 2 * deriv centralRadius x)
  (hleft : G.left central = centralRadius (-T))
  (hright : G.right central = centralRadius T)
  (hB : BufferHypotheses (B.modelBuffer q T B₀))
  (M : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K)

theorem fixedCentralPhysicalModelChart_polynomial_column_bound
    (hq : 1 ≤ q) (hC : 0 < C) (hK : 0 ≤ K)
    (he : ∀ i, 0 < fixedCentralModelCutEnergy M i ∧
      (M.column i).inwardEnergy ≤ 2 * fixedCentralModelCutEnergy M i)
    (i : Fin 2) :
    ‖(sqrt ((fixedCentralPhysicalModelChart B D hD hborder G central q hT hcap
        hcolumn hcore hw hleft hright hB M).kappa i))⁻¹ •
      (fixedCentralPhysicalModelChart B D hD hborder G central q hT hcap
        hcolumn hcore hw hleft hright hB M).column i‖ ≤
      fixedCentralPolynomialColumnConstant T B₀ C K * (1 + 2 * (q : ℝ)) ^ 2 := by
  have hj : 0 < 2 * (q : ℝ) := by
    exact_mod_cast (by omega : 0 < 2 * q)
  apply (fixedCentralPhysicalModelChart_column_bound B D hD hborder G central q hT hcap
    hcolumn hcore hw hleft hright hB M (fun k => (he k).1) hj i).trans
  have hmax : max 0 (max (fixedCentralModelColumnEnvelope M 0)
      (fixedCentralModelColumnEnvelope M 1)) ≤
        fixedCentralPolynomialColumnConstant T B₀ C K * (1 + 2 * (q : ℝ)) ^ 2 :=
    max_le (mul_nonneg (fixedCentralPolynomialColumnConstant_nonneg _ _ _ _) (sq_nonneg _))
      (max_le (fixedCentralModelColumnEnvelope_polynomial_bound hq hT hC hK hB M he 0)
        (fixedCentralModelColumnEnvelope_polynomial_bound hq hT hC hK hB M he 1))
  calc
    _ = max 0 (max (fixedCentralModelColumnEnvelope M 0)
        (fixedCentralModelColumnEnvelope M 1)) := by
      unfold fixedCentralModelColumnCost
      rw [abs_of_pos hj]
      field_simp [hj.ne']
    _ ≤ _ := hmax

end Chart

end ContinuousFlexibility.Radial
