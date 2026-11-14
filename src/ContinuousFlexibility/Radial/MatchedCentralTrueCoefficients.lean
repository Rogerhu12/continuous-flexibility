module

public import ContinuousFlexibility.Radial.CentralBufferGeometry
public import ContinuousFlexibility.Radial.InnerCentralBufferCoefficients
public import ContinuousFlexibility.Radial.InnerCentralCompressionConstruction
public import ContinuousFlexibility.Radial.InnerModelCoefficientEnvelope

/-!
# Coefficients of the genuine central-column buffer

The full inverse cost is the one obtained from the fixed true border.
The earlier central coefficient bound is reused at C + B₀, which
dominates this cost as well as the universal mass, velocity and drift
bounds. No temporary-column inverse is used as an analytic estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements
open scoped BigOperators

theorem matchedCentralTrueBuffer_coefficients {q : ℕ} (hq : 1 ≤ q)
    {T B₀ C : ℝ} (hT : 8 ≤ T) (hB₀ : 0 < B₀) (hC : 0 ≤ C) :
    let c := innerCentralBufferCoefficient T (C + B₀)
    1 ≤ c ∧ B₀ ≤ c ∧ (64 : ℝ) ≤ c ∧
      (centralBufferMass (2 * (q : ℝ)) T)⁻¹ ≤ c ∧
      centralBufferMass (2 * (q : ℝ)) T ≤ c * (1 + 2 * (q : ℝ)) ∧
      centralRadiusWeightConstant * (1 + T) ≤ c := by
  dsimp only
  have hCp : 0 ≤ C + B₀ := add_nonneg hC hB₀.le
  have hc := innerCentralBufferCoefficient_bounds hq hT hCp
  have hbase := innerCentralBufferCoefficient_base (show (0 : ℝ) ≤ T by linarith only [hT]) hCp
  refine ⟨hc.1, ?_, ?_, ?_, ?_, hc.2.2.2.2.2⟩
  · exact (by linarith only [hC, hB₀] : B₀ ≤ 1 + 2 * (C + B₀)).trans hbase.1
  · exact (by nlinarith only [sq_nonneg centralRadiusA] :
      (64 : ℝ) ≤ 64 + 16 * centralRadiusA ^ 2).trans hc.2.2.1
  · simpa only [innerCentralBufferData, innerCentralCapMass, centralBufferMass] using
      hc.2.2.2.1 (0 : Fin 2)
  · simpa only [innerCentralBufferData, innerCentralCapMass, centralBufferMass] using
      hc.2.2.2.2.1 (0 : Fin 2)

/-- The actual true-column buffer has at least the quadratic action
used by the previously proved uniform frequency suppression. -/
theorem matchedCentralTrueBuffer_action {q : ℕ} (hq : 1 ≤ q)
    {T : ℝ} (hT : 8 ≤ T) :
    (T ^ 2 / 16) * (2 * (q : ℝ)) ≤ centralBufferAction (2 * (q : ℝ)) T := by
  have hj := innerCentralBuffer_frequency hq
  have hT2 : (64 : ℝ) ≤ T ^ 2 := by nlinarith only [hT, sq_nonneg (T - 8)]
  have hp := mul_le_mul hj hT2 (by norm_num : (0 : ℝ) ≤ 64)
    (by linarith only [hj] : 0 ≤ 2 * (q : ℝ))
  unfold centralBufferAction
  nlinarith only [hp]

theorem matchedCentralTrue_scaledCoefficient {T B₀ C H A : ℝ}
    (hT : 1 ≤ T) (hB₀ : 0 ≤ B₀) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hA : H * innerCentralCompressionAmplitude (C + B₀) ≤ A)
    {k : ℕ} (hk : k ≤ 8) :
    H * innerCentralBufferCoefficient T (C + B₀) ^ k ≤
      A * (1 + T ^ 2) ^ 8 := by
  have h := innerCentralBufferCoefficient_pow_le hT (add_nonneg hC hB₀) (le_refl _) hk
  calc
    _ ≤ H * (innerCentralCompressionAmplitude (C + B₀) * (1 + T ^ 2) ^ 8) :=
      mul_le_mul_of_nonneg_left h hH
    _ = (H * innerCentralCompressionAmplitude (C + B₀)) * (1 + T ^ 2) ^ 8 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hA (by positivity)

section Energy

variable {q : ℕ} {T B₀ C K : ℝ} {bordered : Bool} {g : RadialL2} {f : ℝ → ℝ}
  (M : InnerBufferLocalizedData
    (centralModelBuffer (2 * (q : ℝ)) T B₀ bordered g f) C K)

/-- The actual density drift is absorbed using the original inward
energy of this same localized witness. -/
theorem matchedCentralTrueCutEnergy_bounds (hC : 0 < C)
    (hfar : 2 * C * centralRadiusA ≤ centralBufferMass (2 * (q : ℝ)) T)
    (i : Fin 2) :
    0 < (M.column i).inwardEnergy + bufferSign i * centralRadiusA ∧
      (M.column i).inwardEnergy ≤
        2 * ((M.column i).inwardEnergy + bufferSign i * centralRadiusA) := by
  have hm : 2 * centralRadiusA ≤ centralBufferMass (2 * (q : ℝ)) T / C := by
    apply (le_div_iff₀ hC).mpr
    nlinarith only [hfar]
  have hα : 2 * centralRadiusA ≤ (M.column i).inwardEnergy :=
    hm.trans (M.column i).inward_lower
  have hd := innerCentral_drift_bounds i hα
  exact ⟨hd.1, by linarith only [hd.2.1]⟩

theorem matchedCentralTrueCutEnergy_inverse_sqrt
    (hq : 1 ≤ q) (hT : 8 ≤ T) (hB₀ : 0 ≤ B₀) (hC : 0 < C)
    (hfar : 2 * C * centralRadiusA ≤ centralBufferMass (2 * (q : ℝ)) T)
    (i : Fin 2) :
    (sqrt ((M.column i).inwardEnergy + bufferSign i * centralRadiusA))⁻¹ ≤
      innerCentralBufferCoefficient T (C + B₀) := by
  have hinv := innerCentralBuffer_inverse_sqrt_energy_le hq hT hC i hfar
    (M.column i).inward_lower
  apply hinv.trans
  unfold innerCentralBufferCoefficient
  linarith only [hB₀]

end Energy

end ContinuousFlexibility.Radial
