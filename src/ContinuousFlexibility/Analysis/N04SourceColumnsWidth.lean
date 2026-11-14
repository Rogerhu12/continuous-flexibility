module

public import ContinuousFlexibility.Analysis.N04SourceColumnsGeometry
public import ContinuousFlexibility.Analysis.N04SourceColumnsData
public import ContinuousFlexibility.Analysis.N04SourceColumnsScalarLinear

/-! The stored physical-to-canonical width ratio has a reference envelope. -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

namespace N04RealizationGauge

variable (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)

/-- Both lengths are among the frozen static reference atoms. Their
zeroth reference bounds control the coefficient in the inverse determinant. -/
theorem sourceColumns_widthRatio_bound
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    ∃ B : ℝ, 0 < B ∧ ∀ m, |G.sourceColumnsWidthRatio η m| ≤
      B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  have hs := href.2 0
  have hpack := coefficientEnvelope_pack (hs.choose * hs.choose) (hs.choose + hs.choose)
  have hE := (G.cost_nonneg η).2.2
  have hmid : ((1 / 2 : ℝ), (0 : ℝ)) ∈ unitStrip := by
    refine ⟨?_, mem_univ _⟩
    norm_num
  refine ⟨hpack.choose, hpack.choose_spec.1, fun m => ?_⟩
  have hphysicalValue : |mixedDerivative 0 0
      (atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)
        (G.ref η) m .physicalLength) ((1 / 2 : ℝ), (0 : ℝ))| =
      |(G.V η).physicalRight m - (G.V η).physicalLeft m| := by
    simp only [spaces_mixedDerivative_zero, atom]
  have hphysical : |(G.V η).physicalRight m - (G.V η).physicalLeft m| ≤
      hs.choose * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ hs.choose :=
    hphysicalValue.symm.trans_le (hs.choose_spec.2 m .physicalLength _ hmid 0 0 (by omega))
  have hcanonicalValue : |mixedDerivative 0 0
      (atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)
        (G.ref η) m .canonicalLengthInverse) ((1 / 2 : ℝ), (0 : ℝ))| =
      |((G.V η).right m - (G.V η).left m)⁻¹| := by
    simp only [spaces_mixedDerivative_zero, atom]
  have hcanonical : |((G.V η).right m - (G.V η).left m)⁻¹| ≤
      hs.choose * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ hs.choose :=
    hcanonicalValue.symm.trans_le
      (hs.choose_spec.2 m .canonicalLengthInverse _ hmid 0 0 (by omega))
  calc
    |G.sourceColumnsWidthRatio η m| =
        |(G.V η).physicalRight m - (G.V η).physicalLeft m| *
          |((G.V η).right m - (G.V η).left m)⁻¹| := by
      rw [sourceColumnsWidthRatio, div_eq_mul_inv, abs_mul]
    _ ≤ (hs.choose * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ hs.choose) *
        (hs.choose * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ hs.choose) :=
      mul_le_mul hphysical hcanonical (abs_nonneg _)
        (mul_nonneg hs.choose_spec.1.le
          (Real.rpow_nonneg (zero_le_one.trans (hE m)) _))
    _ = (hs.choose * hs.choose) *
        G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ (hs.choose + hs.choose) := by
      rw [Real.rpow_add (zero_lt_one.trans_le (hE m))]
      ring
    _ ≤ _ := hpack.choose_spec.2 _ (hE m)

theorem sourceColumns_widthRatio_reference
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    N04SourceReferenceData G.W.U (G.V η).cell
      (fun m _ => G.sourceColumnsWidthRatio η m) :=
  n04SourceColumns_reference_const (G.cost_nonneg η).2.2
    (G.sourceColumnsWidthRatio η) (G.sourceColumns_widthRatio_bound η href)

end N04RealizationGauge

end ContinuousFlexibility.Analysis
