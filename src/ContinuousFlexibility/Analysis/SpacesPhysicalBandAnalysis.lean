module

public import ContinuousFlexibility.Analysis.SpacesPhysicalBandEstimates
public import ContinuousFlexibility.Analysis.SpacesPhysicalLocalization
public import ContinuousFlexibility.Analysis.SpacesLpFamilyBounds

/-!
# The actual physical shell analysis map

Localize the common weak-jet representative, take the joint material and
Fourier band in each integer cell, and retain the original cylinder L²
classes. The complete family estimate has fixed loss zero.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

include hT

include hT in
private theorem spacesPhysicalBandAnalysis_M_one_le (x : ℝ) : 1 ≤ T.M (T.radius x) :=
  (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 x).1).2.2.2

theorem spacesPhysicalCellBand_zero_norm_le (n : ℤ) (k : ℕ) (u : CylinderL2) :
    ‖spacesPhysicalCellBand n (T.M (T.radius n)) k 0 0 u‖ ≤
      (6 * Real.pi) ^ (1 / 2 : ℝ) * ‖u‖ := by
  simpa only [pow_zero, one_smul, Nat.cast_zero, zero_mul, Real.exp_zero, mul_one] using
    spacesPhysicalCellBand_weighted_norm_le n (T.M (T.radius n)) (spacesPhysicalBandAnalysis_M_one_le hT n)
      k 0 0 0 0 (by omega) u

def spacesPhysicalBandFamily (k : ℕ) :
    lp (fun _ : ℤ => CylinderL2) 2 →L[ℝ] lp (fun _ : ℤ => CylinderL2) 2 :=
  lpSpectralDiagonal (fun n => spacesPhysicalCellBand n (T.M (T.radius n)) k 0 0)
    (C := (6 * Real.pi) ^ (1 / 2 : ℝ)) (by positivity)
    (fun n u => spacesPhysicalCellBand_zero_norm_le hT n k u)

theorem spacesPhysicalBandFamily_apply (k : ℕ) (f : lp (fun _ : ℤ => CylinderL2) 2) (n : ℤ) :
    spacesPhysicalBandFamily hT k f n = spacesPhysicalCellBand n (T.M (T.radius n)) k 0 0 (f n) := rfl

/-- The shell coefficients in the integer-indexed fixed cylinder Hilbert sum. -/
def spacesPhysicalBandAnalysis (k : ℕ) :
    PhysicalJetProjectiveLimit hT →L[ℝ] lp (fun _ : ℤ => CylinderL2) 2 :=
  (spacesPhysicalBandFamily hT k).comp (spacesPhysicalLocalizedJetFamily hT 0 0 0)

theorem spacesPhysicalBandAnalysis_apply (k : ℕ) (u : PhysicalJetProjectiveLimit hT) (n : ℤ) :
    spacesPhysicalBandAnalysis hT k u n = spacesPhysicalCellBand n (T.M (T.radius n)) k 0 0
      (spacesPhysicalLocalizedJetFamily hT 0 0 0 u n) := rfl

theorem spacesPhysicalBandAnalysis_row_bound (s k : ℕ) (u : PhysicalJetProjectiveLimit hT) (n : ℤ) :
    ‖Real.exp ((s : ℝ) * (k : ℝ)) • spacesPhysicalBandAnalysis hT k u n‖ ≤
      (6 * Real.pi) ^ (1 / 2 : ℝ) *
        (‖spacesPhysicalLocalizedJetFamily hT 0 0 s u n‖ +
          ‖spacesPhysicalLocalizedJetFamily hT s 0 0 u n‖ +
          ‖spacesPhysicalLocalizedJetFamily hT 0 s 0 u n‖) := by
  have hzero : (spacesPhysicalLocalizedJetFamily hT 0 0 0 u n : PolarPoint → ℝ)
      =ᵐ[materialCylinderMeasure] spacesPhysicalLocalizedRepresentative hT n u := by
    simpa only [pow_zero, one_mul, spaces_mixedDerivative_zero] using
      spacesPhysicalLocalizedJetFamily_ae hT 0 0 0 u n
  have hr : (spacesPhysicalLocalizedJetFamily hT s 0 0 u n : PolarPoint → ℝ)
      =ᵐ[materialCylinderMeasure] mixedDerivative s 0 (spacesPhysicalLocalizedRepresentative hT n u) := by
    simpa only [pow_zero, one_mul] using spacesPhysicalLocalizedJetFamily_ae hT s 0 0 u n
  have hθ : (spacesPhysicalLocalizedJetFamily hT 0 s 0 u n : PolarPoint → ℝ)
      =ᵐ[materialCylinderMeasure] mixedDerivative 0 s (spacesPhysicalLocalizedRepresentative hT n u) := by
    simpa only [pow_zero, one_mul] using spacesPhysicalLocalizedJetFamily_ae hT 0 s 0 u n
  rw [spacesPhysicalBandAnalysis_apply]
  have hb := spacesPhysicalCellBand_analysis_bound n (T.M (T.radius n))
    (spacesPhysicalBandAnalysis_M_one_le hT n) k s
    (spacesPhysicalLocalizedRepresentative_isCylinderTest hT n u)
    (spacesPhysicalLocalizedRepresentative_eq_zero hT n u) hzero hr hθ
  rwa [← spacesPhysicalLocalizedJetFamily_weight hT s u n] at hb

def spacesPhysicalBandAnalysisConstant (s : ℕ) : ℝ :=
  (6 * Real.pi) ^ (1 / 2 : ℝ) *
    (spacesPhysicalLocalizationConstant hT 0 s +
      spacesPhysicalLocalizationConstant hT s 0 + spacesPhysicalLocalizationConstant hT 0 0)

theorem spacesPhysicalBandAnalysisConstant_nonneg (s : ℕ) :
    0 ≤ spacesPhysicalBandAnalysisConstant hT s :=
  mul_nonneg (by positivity) (add_nonneg
    (add_nonneg (spacesPhysicalLocalizationConstant_nonneg hT 0 s)
      (spacesPhysicalLocalizationConstant_nonneg hT s 0))
    (spacesPhysicalLocalizationConstant_nonneg hT 0 0))

/-- The physical analysis estimate in the prescribed grading, with loss zero. -/
theorem spacesPhysicalBandAnalysis_bound (s k : ℕ) (u : PhysicalJetProjectiveLimit hT) :
    ‖Real.exp ((s : ℝ) * (k : ℝ)) • spacesPhysicalBandAnalysis hT k u‖ ≤
      spacesPhysicalBandAnalysisConstant hT s * spacesPhysicalGrading hT s u := by
  have hb := spaces_lp_norm_le_three
    (Real.exp ((s : ℝ) * (k : ℝ)) • spacesPhysicalBandAnalysis hT k u)
    (spacesPhysicalLocalizedJetFamily hT 0 0 s u)
    (spacesPhysicalLocalizedJetFamily hT s 0 0 u)
    (spacesPhysicalLocalizedJetFamily hT 0 s 0 u)
    (C := (6 * Real.pi) ^ (1 / 2 : ℝ)) (by positivity)
    (fun n => spacesPhysicalBandAnalysis_row_bound hT s k u n)
  apply hb.trans
  unfold spacesPhysicalBandAnalysisConstant
  rw [mul_assoc, add_mul, add_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (add_le_add
    (spacesPhysicalLocalizedJetFamily_norm_le hT 0 0 s s (by omega) u)
    (spacesPhysicalLocalizedJetFamily_norm_le hT s 0 0 s (by omega) u))
    (spacesPhysicalLocalizedJetFamily_norm_le hT 0 s 0 s (by omega) u)

end ContinuousFlexibility.Statements
