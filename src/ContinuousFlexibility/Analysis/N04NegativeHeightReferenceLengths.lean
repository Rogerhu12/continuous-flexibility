import ContinuousFlexibility.Analysis.N04NegativeHeightReferenceData
import ContinuousFlexibility.Analysis.N04NegativeHeightBasicData
import ContinuousFlexibility.Analysis.ActualNegativeLengthMaterialBounds

/-!
# The fixed canonical scale in the negative-height numerator

The retained root chart has canonical left endpoint zero. Its actual
canonical length has the original material estimate at the stored half
sample, and hence supplies a fixed spatial factor in the current calculus.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationGauge

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

variable (G : N04RealizationGauge)
  (η : (G.W.S.height (3 / 4 : ℝ)).Space)

theorem negative_canonicalLeft_zero (m : ℕ) (hm : G.Neg η m) :
    (G.V η).left m = 0 := by
  obtain ⟨j, hi⟩ := (G.neg_iff_inl η m).mp hm
  have hf := G.negative_fields η (G.W.C.referenceState, 0) m j hi
  rw [hf.1]
  simp only [N04RealizationStart.A, n04bActualTypedAtlas, n04bTypedAtlasData_left]

theorem negative_canonicalLength_pos (m : ℕ) (hm : G.Neg η m) :
    0 < (G.V η).right m - (G.V η).left m := by
  obtain ⟨j, hi⟩ := (G.neg_iff_inl η m).mp hm
  have hf := G.negative_fields η (G.W.C.referenceState, 0) m j hi
  have hA := n04b_actualTypedAtlas_partA
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀
  rw [hf.1, hf.2.1]
  exact sub_pos.mpr (hA.referenceBounds (G.negativeIndex j)).2.1

theorem negative_canonicalLength_referenceData :
    N04HeightReferenceDataOn G.W.U (G.V η).cell (G.Neg η)
      (fun m _ => (G.V η).right m - (G.V η).left m) := by
  obtain ⟨A, P, hA, hP, hb⟩ :=
    n04bActualTypedAtlas_negative_length_material_bounds
      G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack A P
  apply n04HeightReferenceDataOn_pieceConstant
    (fun m => (G.V η).right m - (G.V η).left m) (G.cost_nonneg η).2.2
  refine ⟨B, hB, ?_⟩
  intro m hm
  obtain ⟨j, hi⟩ := (G.neg_iff_inl η m).mp hm
  have hk : G.X.e₀ (G.negativeIndex j) = .inl (j.1, j.2) :=
    G.X.e₀.apply_symm_apply _
  have hf := G.negative_fields η (G.W.C.referenceState, 0) m j hi
  have hraw : (G.V η).right m - (G.V η).left m ≤
      A * G.W.T.E0 (G.W.T.sample ((G.V η).cell m)) ^ P := by
    rw [hf.1, hf.2.1, hf.2.2.2.2.2.1]
    exact (hb (G.negativeIndex j) j.1 j.2 hk).2.2.2
  have hraise : G.W.T.E0 (G.W.T.sample ((G.V η).cell m)) ^ P ≤
      G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ P :=
    Real.rpow_le_rpow (zero_le_one.trans (G.W.floor _))
      (le_enlargedMaterialData_E0 G.W.T _) hP
  rw [abs_of_pos (G.negative_canonicalLength_pos η m hm)]
  exact (hraw.trans (mul_le_mul_of_nonneg_left hraise hA.le)).trans
    (hpack _ ((G.cost_nonneg η).2.2 m))

end ContinuousFlexibility.Analysis.N04RealizationGauge

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negative_canonicalLength_referenceData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negative_canonicalLength_referenceData
