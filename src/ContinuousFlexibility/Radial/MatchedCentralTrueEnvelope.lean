import ContinuousFlexibility.Radial.MatchedCentralTrueCoefficients

/-!
# Actual Poisson and conormal envelopes for the true central border

The original localized compression witness supplies both the normalized
Poisson remainder and the two-cut conormal error. Their bounds use only
the fixed true full-inverse cost and universal compression constants.
The later retained geometry does not enter either envelope.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements
open scoped Matrix.Norms.L2Operator

def matchedCentralTrueAmplitude (B₀ C K : ℝ) : ℝ :=
  (1 + (sqrt 12 + 1) * (2 * K * (1 + 2 * C)) + 8 * C * (1 + C ^ 2)) *
    innerCentralCompressionAmplitude (C + B₀)

theorem matchedCentralTrueAmplitude_bounds {B₀ C K : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) :
    innerCentralCompressionAmplitude (C + B₀) ≤ matchedCentralTrueAmplitude B₀ C K ∧
      ((sqrt 12 + 1) * (2 * K * (1 + 2 * C))) *
          innerCentralCompressionAmplitude (C + B₀) ≤ matchedCentralTrueAmplitude B₀ C K ∧
      (8 * C * (1 + C ^ 2)) * innerCentralCompressionAmplitude (C + B₀) ≤
        matchedCentralTrueAmplitude B₀ C K := by
  have hr : 0 ≤ (sqrt 12 + 1) * (2 * K * (1 + 2 * C)) := by positivity
  have he : 0 ≤ 8 * C * (1 + C ^ 2) := by positivity
  have ha : 0 ≤ innerCentralCompressionAmplitude (C + B₀) :=
    zero_le_one.trans (innerCentralCompressionAmplitude_ge_one _)
  unfold matchedCentralTrueAmplitude
  refine ⟨?_, ?_, ?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 1 + (sqrt 12 + 1) * (2 * K * (1 + 2 * C)) +
        8 * C * (1 + C ^ 2) by linarith only [hr, he]) ha
  · exact mul_le_mul_of_nonneg_right (by linarith only [he]) ha
  · exact mul_le_mul_of_nonneg_right (by linarith only [hr]) ha

section ActualBuffer

variable {q : ℕ} {T B₀ C K A : ℝ} {bordered : Bool} {g : RadialL2} {f : ℝ → ℝ}

local notation "B" => centralModelBuffer (2 * (q : ℝ)) T B₀ bordered g f
variable (hB : BufferHypotheses (centralModelBuffer (2 * (q : ℝ)) T B₀ bordered g f))
  (M : InnerBufferLocalizedData (centralModelBuffer (2 * (q : ℝ)) T B₀ bordered g f) C K)

/-- The same true model remainder is bounded before selecting any
physical reference containing the central patch. -/
theorem matchedCentralTrueRemainder_le_envelope (hq : 1 ≤ q) (hT : 8 ≤ T)
    (hC : 0 < C) (hK : 0 ≤ K)
    (hfar : 2 * C * centralRadiusA ≤ centralBufferMass (2 * (q : ℝ)) T)
    (hA : ((sqrt 12 + 1) * (2 * K * (1 + 2 * C))) *
      innerCentralCompressionAmplitude (C + B₀) ≤ A) (i : Fin 2) :
    (sqrt 12 * (centralRadiusWeightConstant * (1 + T)) + 1) *
      (innerBufferRemainderEnvelope B C K i /
        sqrt ((M.column i).inwardEnergy + bufferSign i * centralRadiusA)) ≤
      innerCentralCompressionEnvelope A T (2 * (q : ℝ)) := by
  have hB₀ : 0 < B₀ := hB.2.2.1
  have hc := matchedCentralTrueBuffer_coefficients hq hT hB₀ hC.le
  have hj0 : (0 : ℝ) ≤ 2 * (q : ℝ) := by positivity
  have hU : 0 ≤ centralRadiusWeightConstant * (1 + T) :=
    mul_nonneg centralRadiusWeightConstant_pos.le (by linarith only [hT])
  have hk := matchedCentralTrueCutEnergy_bounds M hC hfar i
  have hinv := matchedCentralTrueCutEnergy_inverse_sqrt M hq hT hB₀.le hC hfar i
  have hact (k : Fin 2) : (T ^ 2 / 16) * (2 * (q : ℝ)) ≤ (B).action k :=
    matchedCentralTrueBuffer_action hq hT
  have hraw := innerBuffer_normalized_remainder_coefficient_envelope hB hC.le hK
    hc.1 hj0 hc.2.1 hc.2.2.1 (fun _ => hc.2.2.2.1)
      (fun _ => hc.2.2.2.2.1) hact hU (by norm_num : (0 : ℝ) ≤ 1)
      hc.2.2.2.2.2 hc.1 hk.1 hinv i
  have hraw' :
      (sqrt 12 * (centralRadiusWeightConstant * (1 + T)) + 1) *
        (innerBufferRemainderEnvelope B C K i /
          sqrt ((M.column i).inwardEnergy + bufferSign i * centralRadiusA)) ≤
        ((sqrt 12 + 1) * (2 * K * (1 + 2 * C))) *
          innerCentralBufferCoefficient T (C + B₀) ^ 8 *
            (1 + 2 * (q : ℝ)) ^ 2 * exp (-((T ^ 2 / 16) * (2 * (q : ℝ)))) := by
    simpa only [mul_one] using hraw
  have hfactor : 0 ≤ (sqrt 12 + 1) * (2 * K * (1 + 2 * C)) := by positivity
  have hcoeff := matchedCentralTrue_scaledCoefficient
    (show (1 : ℝ) ≤ T by linarith) hB₀.le hC.le hfactor hA (le_refl 8)
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (1 + 2 * (q : ℝ))))
    (exp_pos (-((T ^ 2 / 16) * (2 * (q : ℝ))))).le
  simpa only [innerCentralCompressionEnvelope, neg_mul] using hraw'.trans hbound

/-- Both weighted signs concern the actual conormal error of this
same localized model. Height cancels in its physical normalization. -/
theorem matchedCentralTrueFluxError_le_envelope (hq : 1 ≤ q) (hT : 8 ≤ T)
    (hC : 0 < C)
    (hfar : 2 * C * centralRadiusA ≤ centralBufferMass (2 * (q : ℝ)) T)
    (hA : (8 * C * (1 + C ^ 2)) *
      innerCentralCompressionAmplitude (C + B₀) ≤ A)
    {height : ℝ} (hh : 0 < height) (sign : Bool) :
    ‖innerTwoCutWeightedError
      (innerPhysicalCutKappa height
        (fun i => centralDensityRoot (bufferCut B i))
        (fun i => (M.column i).inwardEnergy + bufferSign i * centralRadiusA))
      (fun _ => 1)
      (M.physicalFluxError height (fun i => centralDensityRoot (bufferCut B i))) sign‖ ≤
        innerCentralCompressionEnvelope A T (2 * (q : ℝ)) := by
  have hB₀ : 0 < B₀ := hB.2.2.1
  have hc := matchedCentralTrueBuffer_coefficients hq hT hB₀ hC.le
  have hcoeff0 : 0 ≤ innerCentralBufferCoefficient T (C + B₀) :=
    zero_le_one.trans hc.1
  have hj0 : (0 : ℝ) ≤ 2 * (q : ℝ) := by positivity
  have hact (k : Fin 2) : (T ^ 2 / 16) * (2 * (q : ℝ)) ≤ (B).action k :=
    matchedCentralTrueBuffer_action hq hT
  have hk := fun i => matchedCentralTrueCutEnergy_bounds M hC hfar i
  have hraw := M.physical_error_weighted_bound hB hC height
    (fun i => centralDensityRoot (bufferCut B i))
    (fun i => (M.column i).inwardEnergy + bufferSign i * centralRadiusA)
    (fun _ => 1) hh (fun _ => centralDensityRoot_pos _) (fun i => (hk i).1)
    (fun _ => by norm_num) (fun i => (hk i).2)
    (by norm_num : (0 : ℝ) ≤ 1) (fun _ _ => by norm_num)
    (fun _ => hc.2.2.2.2.1) hact sign
  have ht : 0 ≤ (T ^ 2 / 16) * (2 * (q : ℝ)) :=
    mul_nonneg (div_nonneg (sq_nonneg T) (by norm_num)) hj0
  have hexp : exp (-2 * ((T ^ 2 / 16) * (2 * (q : ℝ)))) ≤
      exp (-((T ^ 2 / 16) * (2 * (q : ℝ)))) :=
    exp_le_exp.mpr (by linarith only [ht])
  have he0 : 0 ≤ 8 * C * (1 + C ^ 2) := by positivity
  have hbase := mul_le_mul_of_nonneg_left hc.2.1
    (show 0 ≤ (8 * C * (1 + C ^ 2)) *
      innerCentralBufferCoefficient T (C + B₀) ^ 2 * (1 + 2 * (q : ℝ)) ^ 2 by positivity)
  have hpoly := mul_le_mul hbase hexp (exp_pos _).le (by positivity)
  have hpoly' : 4 * 1 * ((2 * (1 + C ^ 2)) *
      (C * B₀ * (innerCentralBufferCoefficient T (C + B₀) * (1 + 2 * (q : ℝ))) ^ 2 *
        exp (-2 * ((T ^ 2 / 16) * (2 * (q : ℝ)))))) ≤
      (8 * C * (1 + C ^ 2)) * innerCentralBufferCoefficient T (C + B₀) ^ 3 *
        (1 + 2 * (q : ℝ)) ^ 2 * exp (-((T ^ 2 / 16) * (2 * (q : ℝ)))) := by
    calc
      _ = ((8 * C * (1 + C ^ 2)) * innerCentralBufferCoefficient T (C + B₀) ^ 2 *
          (1 + 2 * (q : ℝ)) ^ 2) * B₀ *
            exp (-2 * ((T ^ 2 / 16) * (2 * (q : ℝ)))) := by ring
      _ ≤ _ := hpoly
      _ = _ := by ring
  have hcoeff := matchedCentralTrue_scaledCoefficient
    (show (1 : ℝ) ≤ T by linarith) hB₀.le hC.le he0 hA (by norm_num : 3 ≤ 8)
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (1 + 2 * (q : ℝ))))
    (exp_pos (-((T ^ 2 / 16) * (2 * (q : ℝ))))).le
  simpa only [innerCentralCompressionEnvelope, neg_mul] using
    hraw.trans (hpoly'.trans hbound)

end ActualBuffer

end ContinuousFlexibility.Radial
