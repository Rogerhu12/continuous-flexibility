module

public import ContinuousFlexibility.Radial.InnerCentralCompressionConstruction

/-!
# Closed central Poisson and conormal error envelopes

All energies and errors below come from the same actual localized R09
construction. The central density drift remains in the positive cut
energy. Its inverse square root and the physical velocity are bounded
from the raw central data, so the normalized remainder and the full
two-cut error have a common fixed-degree exponential envelope. The
final choice theorem constructs these objects and proves their
smallness, rather than assuming either normalized estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements
open scoped Matrix.Norms.L2Operator

def innerCentralModelCutEnergy {n : ℕ} {X₀ C K : ℝ}
    (M : InnerBufferLocalizedData (innerCentralBufferData n X₀) C K) (i : Fin 2) : ℝ :=
  (M.column i).inwardEnergy + bufferSign i * centralRadiusA

def innerCentralModelNormalizedRemainder {n : ℕ} {X₀ C K : ℝ}
    (M : InnerBufferLocalizedData (innerCentralBufferData n X₀) C K) (i : Fin 2) : ℝ :=
  (sqrt 12 * (centralRadiusWeightConstant * (1 + X₀)) + 1) *
    (innerBufferRemainderEnvelope (innerCentralBufferData n X₀) C K i /
      sqrt (innerCentralModelCutEnergy M i))

def innerCentralModelRemainderFactor (C K : ℝ) : ℝ :=
  (sqrt 12 + 1) * (2 * K * (1 + 2 * C))

def innerCentralModelErrorFactor (C : ℝ) : ℝ := 8 * C * (1 + C ^ 2)

def innerCentralModelAmplitude (C K : ℝ) : ℝ :=
  (1 + innerCentralModelRemainderFactor C K + innerCentralModelErrorFactor C) *
    innerCentralCompressionAmplitude C

theorem innerCentralModelAmplitude_bounds {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    innerCentralCompressionAmplitude C ≤ innerCentralModelAmplitude C K ∧
      innerCentralModelRemainderFactor C K * innerCentralCompressionAmplitude C ≤
        innerCentralModelAmplitude C K ∧
      innerCentralModelErrorFactor C * innerCentralCompressionAmplitude C ≤
        innerCentralModelAmplitude C K := by
  have hr : 0 ≤ innerCentralModelRemainderFactor C K := by
    unfold innerCentralModelRemainderFactor
    positivity
  have he : 0 ≤ innerCentralModelErrorFactor C := by
    unfold innerCentralModelErrorFactor
    positivity
  have ha : 0 ≤ innerCentralCompressionAmplitude C :=
    zero_le_one.trans (innerCentralCompressionAmplitude_ge_one C)
  unfold innerCentralModelAmplitude
  refine ⟨?_, ?_, ?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 1 + innerCentralModelRemainderFactor C K +
        innerCentralModelErrorFactor C by linarith only [hr, he]) ha
  · exact mul_le_mul_of_nonneg_right (by linarith only [he]) ha
  · exact mul_le_mul_of_nonneg_right (by linarith only [hr]) ha

private theorem scaled_coefficient_power_le {X₀ C H A : ℝ}
    (hX : 1 ≤ X₀) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hA : H * innerCentralCompressionAmplitude C ≤ A) {k : ℕ} (hk : k ≤ 8) :
    H * innerCentralBufferCoefficient X₀ C ^ k ≤ A * (1 + X₀ ^ 2) ^ 8 := by
  have h := innerCentralBufferCoefficient_pow_le hX hC (le_refl _) hk
  calc
    _ ≤ H * (innerCentralCompressionAmplitude C * (1 + X₀ ^ 2) ^ 8) :=
      mul_le_mul_of_nonneg_left h hH
    _ = (H * innerCentralCompressionAmplitude C) * (1 + X₀ ^ 2) ^ 8 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hA (by positivity)

/-- The far cut absorbs the exact density drift for every column of
the same compressed model. -/
theorem innerCentralModelCutEnergy_bounds {n : ℕ} {X₀ C K : ℝ}
    (M : InnerBufferLocalizedData (innerCentralBufferData n X₀) C K)
    (hC : 0 < C)
    (hfar : 2 * C * centralRadiusA ≤ innerCentralCapMass (2 * n) X₀) (i : Fin 2) :
    0 < innerCentralModelCutEnergy M i ∧
      (M.column i).inwardEnergy ≤ 2 * innerCentralModelCutEnergy M i := by
  have hmass : 2 * centralRadiusA ≤ innerCentralCapMass (2 * n) X₀ / C := by
    apply (le_div_iff₀ hC).mpr
    nlinarith only [hfar]
  have hα : 2 * centralRadiusA ≤ (M.column i).inwardEnergy :=
    hmass.trans (M.column i).inward_lower
  have hd := innerCentral_drift_bounds i hα
  exact ⟨hd.1, by
    dsimp only [innerCentralModelCutEnergy]
    linarith only [hd.2.1]⟩

theorem innerCentralModelNormalizedRemainder_le_envelope {n : ℕ} (hn : 1 ≤ n)
    {X₀ C K A : ℝ} (hX : 8 ≤ X₀) (hC : 0 < C) (hK : 0 ≤ K)
    (hB : BufferHypotheses (innerCentralBufferData n X₀))
    (M : InnerBufferLocalizedData (innerCentralBufferData n X₀) C K)
    (hfar : 2 * C * centralRadiusA ≤ innerCentralCapMass (2 * n) X₀)
    (hA : innerCentralModelRemainderFactor C K * innerCentralCompressionAmplitude C ≤ A)
    (i : Fin 2) :
    innerCentralModelNormalizedRemainder M i ≤ innerCentralCompressionEnvelope A X₀ (2 * n) := by
  have hc := innerCentralBufferCoefficient_bounds hn hX hC.le
  have hj0 : (0 : ℝ) ≤ 2 * n := mul_nonneg (by norm_num) (Nat.cast_nonneg n)
  have hU : 0 ≤ centralRadiusWeightConstant * (1 + X₀) :=
    mul_nonneg centralRadiusWeightConstant_pos.le (by linarith only [hX])
  have hk := innerCentralModelCutEnergy_bounds M hC hfar i
  have hinv : (sqrt (innerCentralModelCutEnergy M i))⁻¹ ≤
      innerCentralBufferCoefficient X₀ C :=
    innerCentralBuffer_inverse_sqrt_energy_le hn hX hC i hfar (M.column i).inward_lower
  have hact (k : Fin 2) : (X₀ ^ 2 / 16) * (2 * n) ≤
      (innerCentralBufferData n X₀).action k := (innerCentralBuffer_action n X₀ k).ge
  have hraw := innerBuffer_normalized_remainder_coefficient_envelope hB hC.le hK
    hc.1 hj0 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hact
      hU (by norm_num : (0 : ℝ) ≤ 1) hc.2.2.2.2.2 hc.1 hk.1 hinv i
  have hraw' : innerCentralModelNormalizedRemainder M i ≤
      innerCentralModelRemainderFactor C K * innerCentralBufferCoefficient X₀ C ^ 8 *
        (1 + (2 : ℝ) * n) ^ 2 * exp (-((X₀ ^ 2 / 16) * (2 * n))) := by
    simpa only [innerCentralModelNormalizedRemainder, innerCentralModelRemainderFactor,
      mul_one] using hraw
  have hfactor : 0 ≤ innerCentralModelRemainderFactor C K := by
    unfold innerCentralModelRemainderFactor
    positivity
  have hcoeff := scaled_coefficient_power_le
    ((by norm_num : (1 : ℝ) ≤ 8).trans hX) hC.le hfactor hA (le_refl 8)
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (1 + (2 : ℝ) * n)))
    (exp_pos (-((X₀ ^ 2 / 16) * (2 * n)))).le
  simpa only [innerCentralCompressionEnvelope, neg_mul] using hraw'.trans hbound

/-- The full two-cut error of the actual model, normalized by the
physical kappa including drift. The middle weight is one for both signs. -/
theorem innerCentralModelFluxError_le_envelope {n : ℕ} (hn : 1 ≤ n)
    {X₀ C K A : ℝ} (hX : 8 ≤ X₀) (hC : 0 < C)
    (hB : BufferHypotheses (innerCentralBufferData n X₀))
    (M : InnerBufferLocalizedData (innerCentralBufferData n X₀) C K)
    (hfar : 2 * C * centralRadiusA ≤ innerCentralCapMass (2 * n) X₀)
    (hA : innerCentralModelErrorFactor C * innerCentralCompressionAmplitude C ≤ A)
    {height : ℝ} (hh : 0 < height) (sign : Bool) :
    ‖innerTwoCutWeightedError
      (innerPhysicalCutKappa height
        (fun i => centralDensityRoot (bufferCut (innerCentralBufferData n X₀) i))
        (innerCentralModelCutEnergy M)) (fun _ => 1)
      (M.physicalFluxError height
        (fun i => centralDensityRoot (bufferCut (innerCentralBufferData n X₀) i))) sign‖ ≤
      innerCentralCompressionEnvelope A X₀ (2 * n) := by
  have hc := innerCentralBufferCoefficient_bounds hn hX hC.le
  have hcoeff0 : 0 ≤ innerCentralBufferCoefficient X₀ C := zero_le_one.trans hc.1
  have hj0 : (0 : ℝ) ≤ 2 * n := mul_nonneg (by norm_num) (Nat.cast_nonneg n)
  have hact (k : Fin 2) : (X₀ ^ 2 / 16) * (2 * n) ≤
      (innerCentralBufferData n X₀).action k := (innerCentralBuffer_action n X₀ k).ge
  have hk := fun i => innerCentralModelCutEnergy_bounds M hC hfar i
  have hraw := M.physical_error_weighted_bound hB hC height
    (fun i => centralDensityRoot (bufferCut (innerCentralBufferData n X₀) i))
    (innerCentralModelCutEnergy M) (fun _ => 1) hh
    (fun _ => centralDensityRoot_pos _) (fun i => (hk i).1)
    (fun _ => by norm_num) (fun i => (hk i).2)
    (by norm_num : (0 : ℝ) ≤ 1) (fun _ _ => by norm_num) hc.2.2.2.2.1 hact sign
  have ht : 0 ≤ (X₀ ^ 2 / 16) * (2 * n) :=
    mul_nonneg (div_nonneg (sq_nonneg X₀) (by norm_num)) hj0
  have hexp : exp (-2 * ((X₀ ^ 2 / 16) * (2 * n))) ≤
      exp (-((X₀ ^ 2 / 16) * (2 * n))) := exp_le_exp.mpr (by linarith only [ht])
  have he0 : 0 ≤ innerCentralModelErrorFactor C := by
    unfold innerCentralModelErrorFactor
    positivity
  have hbase := mul_le_mul_of_nonneg_left hc.2.1
    (show 0 ≤ innerCentralModelErrorFactor C * innerCentralBufferCoefficient X₀ C ^ 2 *
      (1 + (2 : ℝ) * n) ^ 2 by positivity)
  have hpoly := mul_le_mul hbase hexp (exp_pos _).le (by positivity)
  have hpoly' : 4 * 1 * ((2 * (1 + C ^ 2)) *
      (C * (innerCentralBufferData n X₀).B₀ *
        (innerCentralBufferCoefficient X₀ C * (1 + (2 : ℝ) * n)) ^ 2 *
          exp (-2 * ((X₀ ^ 2 / 16) * (2 * n))))) ≤
      innerCentralModelErrorFactor C * innerCentralBufferCoefficient X₀ C ^ 3 *
        (1 + (2 : ℝ) * n) ^ 2 * exp (-((X₀ ^ 2 / 16) * (2 * n))) := by
    calc
      _ = (innerCentralModelErrorFactor C * innerCentralBufferCoefficient X₀ C ^ 2 *
          (1 + (2 : ℝ) * n) ^ 2) * (innerCentralBufferData n X₀).B₀ *
          exp (-2 * ((X₀ ^ 2 / 16) * (2 * n))) := by
        unfold innerCentralModelErrorFactor
        ring
      _ ≤ _ := hpoly
      _ = _ := by ring
  have hcoeff := scaled_coefficient_power_le
    ((by norm_num : (1 : ℝ) ≤ 8).trans hX) hC.le he0 hA (by norm_num : 3 ≤ 8)
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (1 + (2 : ℝ) * n)))
    (exp_pos (-((X₀ ^ 2 / 16) * (2 * n)))).le
  simpa only [innerCentralCompressionEnvelope, neg_mul] using
    hraw.trans (hpoly'.trans hbound)

/-- The real central compression, its two normalized flux signs, and
its frequency-small normalized remainder are chosen together. The
same M appears in every conclusion. -/
theorem exists_innerCentralModelChoices (hR09 : R09Statement) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ A : ℝ, innerCentralModelAmplitude C K ≤ A →
      ∀ η : ℝ, 0 < η → ∀ initial : ℝ, ∃ X₀ : ℝ,
        initial ≤ X₀ ∧ 8 ≤ X₀ ∧
        (∀ j : ℝ, 2 ≤ j → 2 * C * centralRadiusA ≤ innerCentralCapMass j X₀) ∧
        ∀ n : ℕ, 1 ≤ n →
          BufferHypotheses (innerCentralBufferData n X₀) ∧
          ∃ M : InnerBufferLocalizedData (innerCentralBufferData n X₀) C K,
            (∀ i, 0 < innerCentralModelCutEnergy M i ∧
              (M.column i).inwardEnergy ≤ 2 * innerCentralModelCutEnergy M i) ∧
            (∀ i, innerCentralModelNormalizedRemainder M i < min 1 η / (2 * n)) ∧
            ∀ height : ℝ, 0 < height → ∀ sign : Bool,
              ‖innerTwoCutWeightedError
                (innerPhysicalCutKappa height
                  (fun i => centralDensityRoot (bufferCut (innerCentralBufferData n X₀) i))
                  (innerCentralModelCutEnergy M)) (fun _ => 1)
                (M.physicalFluxError height
                  (fun i => centralDensityRoot (bufferCut (innerCentralBufferData n X₀) i))) sign‖ < η := by
  obtain ⟨C, K, ε, hC, hK, _hε, hchoice⟩ := exists_innerCentralLocalizedChoices hR09
  refine ⟨C, K, hC, hK, ?_⟩
  intro A hA η hη initial
  have hfactor := innerCentralModelAmplitude_bounds hC.le hK.le
  obtain ⟨X₀, hinit, hX, hfar, hmodels⟩ := hchoice A (hfactor.1.trans hA)
    (min 1 η) (lt_min zero_lt_one hη) initial
  refine ⟨X₀, hinit, hX, hfar, ?_⟩
  intro n hn
  obtain ⟨hB, ⟨M⟩, _henv, hfreq⟩ := hmodels n hn
  have hj := innerCentralBuffer_frequency hn
  have hjpos : (0 : ℝ) < 2 * n := (by norm_num : (0 : ℝ) < 2).trans_le hj
  have hmass := hfar (2 * n) hj
  have henv : innerCentralCompressionEnvelope A X₀ (2 * n) < η :=
    _henv.trans_le (min_le_right 1 η)
  refine ⟨hB, M, (fun i => innerCentralModelCutEnergy_bounds M hC hmass i), ?_, ?_⟩
  · intro i
    apply (lt_div_iff₀ hjpos).mpr
    have hrem := innerCentralModelNormalizedRemainder_le_envelope hn hX hC hK.le hB M
      hmass (hfactor.2.1.trans hA) i
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left hrem hjpos.le).trans_lt hfreq
  · intro height hh sign
    exact (innerCentralModelFluxError_le_envelope hn hX hC hB M hmass
      (hfactor.2.2.trans hA) hh sign).trans_lt henv

end ContinuousFlexibility.Radial
