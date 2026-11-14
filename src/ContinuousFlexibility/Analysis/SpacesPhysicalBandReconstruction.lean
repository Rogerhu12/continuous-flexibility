module

public import ContinuousFlexibility.Analysis.SpacesPhysicalBandAnalysis

/-!
# Exact reconstruction by the physical Fourier bands

The zero-order bands are genuine spectral projections. Their series recovers
each localized cylinder class, and the order-one analysis estimate promotes
the coordinate identities to convergence in the full Hilbert sum of cells.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal BigOperators ComplexConjugate ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance spacesBandReconstructionCircleMeasure : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance spacesBandReconstructionFrequencyDecidable : DecidableEq SpacesTorusFrequency :=
  Classical.decEq _

theorem spacesTorusPhysicalBand_hasSum (M : ℝ) (hM : 1 ≤ M)
    (u : SpacesTorusRealL2) :
    HasSum (fun k => spacesTorusRealCut (spacesPhysicalFrequencyBand M k)
      (spacesPhysicalFourierSymbol 0 0) u) u := by
  have hcut (k : ℕ) :
      spacesTorusCoefficientCut (spacesPhysicalFrequencyBand M k)
        (spacesPhysicalFourierSymbol 0 0) (spacesTorusRealFourier u) =
      lpSpectralBand (spectralLogBand (spacesPhysicalFrequencySize M)) k
        (spacesTorusRealFourier u) := by
    apply lp.ext
    funext j
    simp only [spacesTorusCoefficientCut_apply, spacesPhysicalFrequencyBand_mem hM,
      spacesPhysicalFourierSymbol_zero, one_mul, lpSpectralBand_apply]
  have h := ((spacesLpRealPart (volume : Measure SpacesTorus)).comp
    spacesTorusFourierInverse).hasSum
    (hasSum_lpSpectralBand (spectralLogBand (spacesPhysicalFrequencySize M))
      (spacesTorusRealFourier u))
  have hv : spacesLpRealPart (volume : Measure SpacesTorus)
      (spacesTorusFourierInverse (spacesTorusRealFourier u)) = u := by
    rw [spacesTorusRealFourier_apply, spacesTorusFourierInverse_fourier,
      spacesLpRealPart_complexification]
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [hv] at h
  simpa only [spacesTorusRealCut_apply, hcut] using h

theorem spacesTorusPhysicalBand_comp_zero (M : ℝ) (hM : 1 ≤ M) (k a b : ℕ)
    (u : SpacesTorusRealL2) :
    spacesTorusRealCut (spacesPhysicalFrequencyBand M k) (spacesPhysicalFourierSymbol a b)
      (spacesTorusRealCut (spacesPhysicalFrequencyBand M k)
        (spacesPhysicalFourierSymbol 0 0) u) =
    spacesTorusRealCut (spacesPhysicalFrequencyBand M k) (spacesPhysicalFourierSymbol a b) u := by
  rw [spacesTorusRealCut_apply, spacesTorusRealCut_fourier _
    (spacesPhysicalFrequencyBand_neg hM k) _ (spacesPhysicalFourierSymbol_neg 0 0),
    spacesTorusRealCut_apply]
  congr 2
  apply lp.ext
  funext j
  simp only [spacesTorusCoefficientCut_apply, spacesPhysicalFourierSymbol_zero]
  split_ifs <;> simp only [one_mul]

theorem spacesPhysicalCellToTorusL2_jet (n : ℤ) (S : Finset SpacesTorusFrequency)
    (a b : ℕ) (u : CylinderL2) :
    spacesPhysicalCellToTorusL2 n (spacesPhysicalCellJet n S a b u) =
      spacesTorusRealCut S (spacesPhysicalFourierSymbol a b) (spacesPhysicalCellToTorusL2 n u) := by
  rw [spacesPhysicalCellToTorusL2_apply, spacesPhysicalCellJet_apply,
    spacesCylinderToPhysicalCell_leftInverse, spacesPhysicalCellToTorus_leftInverse]

/-- Reapplying the zero-order band preserves every physical derivative band. -/
theorem spacesPhysicalCellBand_comp_zero (n : ℤ) (M : ℝ) (hM : 1 ≤ M)
    (k a b : ℕ) (u : CylinderL2) :
    spacesPhysicalCellBand n M k a b (spacesPhysicalCellBand n M k 0 0 u) =
      spacesPhysicalCellBand n M k a b u := by
  simp only [spacesPhysicalCellBand, spacesPhysicalCellJet_apply,
    spacesPhysicalCellToTorusL2_apply, spacesCylinderToPhysicalCell_leftInverse,
    spacesPhysicalCellToTorus_leftInverse, spacesTorusPhysicalBand_comp_zero M hM]

theorem spacesPhysicalCellBand_hasSum (n : ℤ) (M : ℝ) (hM : 1 ≤ M) (u : CylinderL2) :
    HasSum (fun k => spacesPhysicalCellBand n M k 0 0 u)
      (spacesPhysicalCellToCylinder ℝ n (spacesCylinderToPhysicalCell ℝ n u)) := by
  have h := ((spacesPhysicalCellToCylinder ℝ n).comp
    (spacesTorusToPhysicalCell ℝ n).toContinuousLinearMap).hasSum
      (spacesTorusPhysicalBand_hasSum M hM (spacesPhysicalCellToTorusL2 n u))
  simpa only [ContinuousLinearMap.comp_apply, spacesPhysicalCellBand,
    spacesPhysicalCellJet_apply, spacesPhysicalCellToTorusL2_apply,
    LinearIsometry.coe_toContinuousLinearMap, spacesTorusToPhysicalCell_leftInverse] using h

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

theorem spacesPhysicalLocalizedJetFamily_cell_restore (u : PhysicalJetProjectiveLimit hT) (n : ℤ) :
    spacesPhysicalCellToCylinder ℝ n (spacesCylinderToPhysicalCell ℝ n
      (spacesPhysicalLocalizedJetFamily hT 0 0 0 u n)) =
        spacesPhysicalLocalizedJetFamily hT 0 0 0 u n := by
  have hu := spacesPhysicalLocalizedJetFamily_zero_ae hT u n
  have hr := (spacesCylinderToPhysicalCell_ae ℝ n
    (spacesPhysicalLocalizedJetFamily hT 0 0 0 u n)).trans
    (hu.filter_mono (ae_mono (spacesPhysicalCellMeasure_le_cylinder n)))
  have he := spacesPhysicalCellToCylinder_ae_of_ae ℝ n _ _ hr
  apply Lp.ext
  filter_upwards [he, hu] with p hp hu
  rw [hp, hu]
  by_cases hm : p ∈ spacesPhysicalCellRadialSet n
  · exact indicator_of_mem hm _
  · rw [indicator_of_notMem hm]
    symm
    have hp : p.1 ∉ Ioc ((n : ℝ) - 3) (n + 3) := fun h => hm ⟨h, mem_univ _⟩
    simpa only [spaces_mixedDerivative_zero] using spaces_mixedDerivative_cell_support n
      (spacesPhysicalLocalizedRepresentative_eq_zero hT n u) 0 0 p hp

theorem spacesPhysicalBandAnalysis_row_hasSum (u : PhysicalJetProjectiveLimit hT) (n : ℤ) :
    HasSum (fun k => spacesPhysicalBandAnalysis hT k u n)
      (spacesPhysicalLocalizedJetFamily hT 0 0 0 u n) := by
  have hM : 1 ≤ T.M (T.radius n) :=
    (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 n).1).2.2.2
  simpa only [spacesPhysicalBandAnalysis_apply,
    spacesPhysicalLocalizedJetFamily_cell_restore hT u n] using
      spacesPhysicalCellBand_hasSum n (T.M (T.radius n)) hM
        (spacesPhysicalLocalizedJetFamily hT 0 0 0 u n)

theorem spacesPhysicalBandAnalysis_summable (u : PhysicalJetProjectiveLimit hT) :
    Summable (fun k => spacesPhysicalBandAnalysis hT k u) := by
  apply (Real.summable_exp_neg_nat.mul_right
    (spacesPhysicalBandAnalysisConstant hT 1 * spacesPhysicalGrading hT 1 u)).of_norm_bounded
  intro k
  have h := spacesPhysicalBandAnalysis_bound hT 1 k u
  simp only [Nat.cast_one, one_mul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at h
  have he : Real.exp (-(k : ℝ)) * Real.exp (k : ℝ) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(k : ℝ))).le
  simpa only [← mul_assoc, he, one_mul] using hh

/-- The bands reconstruct the entire localized integer family in its `l²` norm. -/
theorem spacesPhysicalBandAnalysis_hasSum (u : PhysicalJetProjectiveLimit hT) :
    HasSum (fun k => spacesPhysicalBandAnalysis hT k u)
      (spacesPhysicalLocalizedJetFamily hT 0 0 0 u) := by
  have h := spacesPhysicalBandAnalysis_summable hT u
  have he : (∑' k, spacesPhysicalBandAnalysis hT k u) =
      spacesPhysicalLocalizedJetFamily hT 0 0 0 u := by
    apply lp.ext
    funext n
    exact ((lp.evalCLM ℝ (fun _ : ℤ => CylinderL2) 2 n).hasSum h.hasSum).unique
      (spacesPhysicalBandAnalysis_row_hasSum hT u n)
  exact he ▸ h.hasSum

end ContinuousFlexibility.Statements
