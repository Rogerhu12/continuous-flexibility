module

public import ContinuousFlexibility.Analysis.SpacesPhysicalCellBands

/-!
# Analysis decay of the actual physical Fourier bands

Three pure order-`s` jets control a band: the material weight, the radial
derivative, and the angular derivative. Parseval and the exact physical
Fourier symbols give the estimate with no derivative loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false

local instance spacesPhysicalBandEstimatesCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem spacesTorusPhysicalBand_analysis_bound (M : ℝ) (hM : 1 ≤ M) (k s : ℕ)
    (f dr dθ : SpacesTorusRealL2)
    (hr : ∀ j, spacesTorusRealFourier dr j =
      spacesPhysicalFourierSymbol s 0 j * spacesTorusRealFourier f j)
    (hθ : ∀ j, spacesTorusRealFourier dθ j =
      spacesPhysicalFourierSymbol 0 s j * spacesTorusRealFourier f j) :
    ‖Real.exp ((s : ℝ) * (k : ℝ)) • spacesTorusRealCut (spacesPhysicalFrequencyBand M k)
      (spacesPhysicalFourierSymbol 0 0) f‖ ≤ ‖M ^ s • f‖ + ‖dr‖ + ‖dθ‖ := by
  let v : lp (fun _ : SpacesTorusFrequency => ℝ) 2 :=
    lp.toNorm (spacesTorusRealFourier (M ^ s • f)) +
      lp.toNorm (spacesTorusRealFourier dr) + lp.toNorm (spacesTorusRealFourier dθ)
  have hv (j : SpacesTorusFrequency) : ‖v j‖ =
      ‖spacesTorusRealFourier (M ^ s • f) j‖ +
        ‖spacesTorusRealFourier dr j‖ + ‖spacesTorusRealFourier dθ j‖ := by
    change ‖‖spacesTorusRealFourier (M ^ s • f) j‖ +
      ‖spacesTorusRealFourier dr j‖ + ‖spacesTorusRealFourier dθ j‖‖ = _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hnorm :
      ‖spacesTorusRealFourier (Real.exp ((s : ℝ) * (k : ℝ)) •
        spacesTorusRealCut (spacesPhysicalFrequencyBand M k) (spacesPhysicalFourierSymbol 0 0) f)‖ ≤
        ‖v‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro j
    rw [spacesTorusRealFourier.map_smul]
    change ‖Real.exp ((s : ℝ) * (k : ℝ)) •
      spacesTorusRealFourier (spacesTorusRealCut (spacesPhysicalFrequencyBand M k)
        (spacesPhysicalFourierSymbol 0 0) f) j‖ ≤ ‖v j‖
    rw [spacesTorusRealCut_fourier _ (spacesPhysicalFrequencyBand_neg hM k) _
      (spacesPhysicalFourierSymbol_neg 0 0), spacesTorusCoefficientCut_apply]
    by_cases hj : j ∈ spacesPhysicalFrequencyBand M k
    · rw [ite_eq_left hj, spacesPhysicalFourierSymbol_zero, one_mul, norm_smul,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hv j]
      calc
        Real.exp ((s : ℝ) * (k : ℝ)) * ‖spacesTorusRealFourier f j‖ ≤
            (M ^ s + (Real.pi / 3 * |(j 0 : ℝ)|) ^ s + (2 * |(j 1 : ℝ)|) ^ s) *
              ‖spacesTorusRealFourier f j‖ :=
          mul_le_mul_of_nonneg_right (spacesPhysicalFrequencyBand_analysis_bound hM hj s)
            (norm_nonneg _)
        _ = _ := by
          rw [spacesTorusRealFourier.map_smul (M ^ s) f, hr j, hθ j]
          simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (pow_nonneg (zero_le_one.trans hM) s), norm_mul,
            spacesPhysicalFourierSymbol_norm, pow_zero, mul_one, one_mul]
          ring
    · simp only [ite_eq_right hj, smul_zero, norm_zero, norm_nonneg]
  calc
    _ = ‖spacesTorusRealFourier (Real.exp ((s : ℝ) * (k : ℝ)) •
        spacesTorusRealCut (spacesPhysicalFrequencyBand M k) (spacesPhysicalFourierSymbol 0 0) f)‖ :=
      (spacesTorusRealFourier_norm _).symm
    _ ≤ ‖v‖ := hnorm
    _ ≤ ‖lp.toNorm (spacesTorusRealFourier (M ^ s • f))‖ +
        ‖lp.toNorm (spacesTorusRealFourier dr)‖ + ‖lp.toNorm (spacesTorusRealFourier dθ)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖M ^ s • f‖ + ‖dr‖ + ‖dθ‖ := by
      simp only [lp.norm_toNorm, spacesTorusRealFourier_norm]

theorem spacesPhysicalCellToTorusL2_fourier_of_ae (n : ℤ) (u : CylinderL2)
    {v : PolarPoint → ℝ} (hu : (u : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure] v)
    (j : SpacesTorusFrequency) :
    spacesTorusRealFourier (spacesPhysicalCellToTorusL2 n u) j =
      UnitAddTorus.mFourierCoeff (fun t => (v (spacesPhysicalCellChart n t) : ℂ)) j := by
  have huc : (u : PolarPoint → ℝ) =ᵐ[spacesPhysicalCellMeasure n] v :=
    hu.filter_mono (ae_mono (spacesPhysicalCellMeasure_le_cylinder n))
  have ht := (spacesPhysicalCellChart_preserving n).quasiMeasurePreserving.ae_eq_comp huc
  rw [spacesTorusRealFourier_apply, spacesTorusFourier_coefficient,
    UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourierCoeff]
  apply integral_congr_ae
  filter_upwards [spacesLpComplexification_ae volume (spacesPhysicalCellToTorusL2 n u),
    spacesPhysicalCellToTorusL2_ae n u, ht] with t hc hu hv
  rw [hc, hu, hv]
  rfl

/-- Actual localized derivatives give the needed coefficient identities. -/
theorem spacesPhysicalCellToTorusL2_fourier_derivative (n : ℤ) (a b : ℕ)
    {u d : CylinderL2} {v : PolarPoint → ℝ} (hv : IsCylinderTest v)
    (hz : ∀ p : PolarPoint, 1 ≤ |p.1 - n| → v p = 0)
    (hu : (u : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure] v)
    (hd : (d : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure] mixedDerivative a b v)
    (j : SpacesTorusFrequency) :
    spacesTorusRealFourier (spacesPhysicalCellToTorusL2 n d) j =
      spacesPhysicalFourierSymbol a b j *
        spacesTorusRealFourier (spacesPhysicalCellToTorusL2 n u) j := by
  rw [spacesPhysicalCellToTorusL2_fourier_of_ae n d hd,
    spacesPhysicalCellToTorusL2_fourier_of_ae n u hu,
    spacesPhysicalCell_coefficient_mixedDerivative n j hv hz a b]
  rfl

/-- The cylinder band estimate, in the actual measure and original jets. -/
theorem spacesPhysicalCellBand_analysis_bound (n : ℤ) (M : ℝ) (hM : 1 ≤ M) (k s : ℕ)
    {u dr dθ : CylinderL2} {v : PolarPoint → ℝ} (hv : IsCylinderTest v)
    (hz : ∀ p : PolarPoint, 1 ≤ |p.1 - n| → v p = 0)
    (hu : (u : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure] v)
    (hr : (dr : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure] mixedDerivative s 0 v)
    (hθ : (dθ : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure] mixedDerivative 0 s v) :
    ‖Real.exp ((s : ℝ) * (k : ℝ)) • spacesPhysicalCellBand n M k 0 0 u‖ ≤
      (6 * Real.pi) ^ (1 / 2 : ℝ) * (‖M ^ s • u‖ + ‖dr‖ + ‖dθ‖) := by
  have hb := spacesTorusPhysicalBand_analysis_bound M hM k s
    (spacesPhysicalCellToTorusL2 n u) (spacesPhysicalCellToTorusL2 n dr)
    (spacesPhysicalCellToTorusL2 n dθ)
    (spacesPhysicalCellToTorusL2_fourier_derivative n s 0 hv hz hu hr)
    (spacesPhysicalCellToTorusL2_fourier_derivative n 0 s hv hz hu hθ)
  rw [spacesPhysicalCellBand, spacesPhysicalCellJet_apply, ← map_smul, ← map_smul]
  calc
    _ ≤ (6 * Real.pi) ^ (1 / 2 : ℝ) *
        ‖spacesTorusToPhysicalCell ℝ n (Real.exp ((s : ℝ) * (k : ℝ)) •
          spacesTorusRealCut (spacesPhysicalFrequencyBand M k) (spacesPhysicalFourierSymbol 0 0)
            (spacesPhysicalCellToTorusL2 n u))‖ := spacesPhysicalCellToCylinder_norm_le ℝ n _
    _ = (6 * Real.pi) ^ (1 / 2 : ℝ) *
        ‖Real.exp ((s : ℝ) * (k : ℝ)) • spacesTorusRealCut (spacesPhysicalFrequencyBand M k)
          (spacesPhysicalFourierSymbol 0 0) (spacesPhysicalCellToTorusL2 n u)‖ :=
      congrArg ((6 * Real.pi) ^ (1 / 2 : ℝ) * ·) ((spacesTorusToPhysicalCell ℝ n).norm_map _)
    _ ≤ (6 * Real.pi) ^ (1 / 2 : ℝ) *
        (‖M ^ s • spacesPhysicalCellToTorusL2 n u‖ +
          ‖spacesPhysicalCellToTorusL2 n dr‖ + ‖spacesPhysicalCellToTorusL2 n dθ‖) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ _ := by
      rw [← map_smul]
      exact mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (spacesPhysicalCellToTorusL2_norm_le n _)
          (spacesPhysicalCellToTorusL2_norm_le n dr)) (spacesPhysicalCellToTorusL2_norm_le n dθ))
        (by positivity)

end ContinuousFlexibility.Statements
