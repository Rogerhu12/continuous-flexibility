module

public import ContinuousFlexibility.Radial.MatchedCentralTrueChoices
public import ContinuousFlexibility.Radial.FixedCentralModelSmallError

/-!
# The actual fixed central models with frequency-normalized remainders

This is the original fixed-border buffer and localized model. Its radius
is chosen before the selected family and retained geometry. The same
chosen witnesses carry the conormal errors used by the regional factory
and the sharper remainder used by the weighted Poisson estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Matrix.Norms.L2Operator

theorem FixedCentralBorder.exists_frequency_normalized_model_buffers
    (B : FixedCentralBorder) (hR09 : R09Statement) (Tmin : ℝ) :
    ∃ C K B₀ T : ℝ, 0 < C ∧ 0 < K ∧ 0 < B₀ ∧ 8 ≤ T ∧ Tmin ≤ T ∧
      sqrt centralOscillatorA + 2 ≤ T ∧
      (∀ j : ℝ, 2 ≤ j → 2 * C * centralRadiusA ≤ centralBufferMass j T) ∧
      ∃ models : ∀ q : ℕ, 1 ≤ q → InnerBufferLocalizedData (B.modelBuffer q T B₀) C K,
        (∀ q : ℕ, 1 ≤ q → BufferHypotheses (B.modelBuffer q T B₀)) ∧
        (∀ q : ℕ, ∀ hq : 1 ≤ q, ∀ i,
          0 < fixedCentralModelCutEnergy (models q hq) i ∧
          ((models q hq).column i).inwardEnergy ≤
            2 * fixedCentralModelCutEnergy (models q hq) i) ∧
        (∀ q : ℕ, ∀ hq : 1 ≤ q, ∀ i,
          (sqrt 12 * (centralRadiusWeightConstant * (1 + T)) + 1) *
            (innerBufferRemainderEnvelope (B.modelBuffer q T B₀) C K i /
              sqrt (fixedCentralModelCutEnergy (models q hq) i)) ≤
                1 / (2 * (q : ℝ))) ∧
        ∀ q : ℕ, ∀ hq : 1 ≤ q, ∀ height : ℝ, 0 < height → ∀ sign : Bool,
          ‖innerTwoCutWeightedError
            (innerPhysicalCutKappa height
              (fun i => centralDensityRoot (bufferCut (B.modelBuffer q T B₀) i))
              (fixedCentralModelCutEnergy (models q hq)))
            (fun _ => 1)
            ((models q hq).physicalFluxError height
              (fun i => centralDensityRoot (bufferCut (B.modelBuffer q T B₀) i))) sign‖ ≤
                (1 : ℝ) / 8 := by
  classical
  obtain ⟨C, K, B₀, hC, hK, hB₀, hchoice⟩ := exists_matchedCentralTrueModelChoices hR09 B
  obtain ⟨T, hmin, hT, _hsupport, _hwindow, hfar, hmodels⟩ :=
    hchoice (1 / 8) (by norm_num) (max Tmin (sqrt centralOscillatorA + 2))
  have hlocal (q : ℕ) (hq : 1 ≤ q) :
      BufferHypotheses (B.modelBuffer q T B₀) ∧
      ∃ M : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K,
        (∀ i, 0 < fixedCentralModelCutEnergy M i ∧
          (M.column i).inwardEnergy ≤ 2 * fixedCentralModelCutEnergy M i) ∧
        (∀ i, (sqrt 12 * (centralRadiusWeightConstant * (1 + T)) + 1) *
          (innerBufferRemainderEnvelope (B.modelBuffer q T B₀) C K i /
            sqrt (fixedCentralModelCutEnergy M i)) ≤ 1 / (2 * (q : ℝ))) ∧
        ∀ height : ℝ, 0 < height → ∀ sign : Bool,
          ‖innerTwoCutWeightedError
            (innerPhysicalCutKappa height
              (fun i => centralDensityRoot (bufferCut (B.modelBuffer q T B₀) i))
              (fixedCentralModelCutEnergy M))
            (fun _ => 1)
            (M.physicalFluxError height
              (fun i => centralDensityRoot (bufferCut (B.modelBuffer q T B₀) i))) sign‖ ≤
                (1 : ℝ) / 8 := by
    obtain ⟨hB, M, henergy, hrem, herror⟩ := hmodels q hq
    refine ⟨hB, M, henergy, ?_, fun height hh sign => (herror height hh sign).le⟩
    intro i
    have hj : (0 : ℝ) < 2 * (q : ℝ) :=
      (by norm_num : (0 : ℝ) < 2).trans_le (innerCentralBuffer_frequency hq)
    exact (hrem i).le.trans
      (div_le_div_of_nonneg_right (min_le_left 1 (1 / 8 : ℝ)) hj.le)
  choose hbuffers models henergy hrem herror using hlocal
  exact ⟨C, K, B₀, T, hC, hK, hB₀, hT, (le_max_left _ _).trans hmin,
    (le_max_right _ _).trans hmin, hfar, models, hbuffers, henergy, hrem, herror⟩

end ContinuousFlexibility.Radial
