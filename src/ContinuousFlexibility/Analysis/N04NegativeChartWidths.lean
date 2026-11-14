import ContinuousFlexibility.Analysis.N04NegativeChartReindex
import ContinuousFlexibility.Analysis.ActualNegativeLengthMaterialBounds
import ContinuousFlexibility.Analysis.N04SourceColumnsScalarLinear

/-!
# Forward normalization at the original negative half sample

The determinant normalization is the canonical width divided by the
physical width. Both widths come from the retained typed atlas. Its
proved length bounds therefore control this coefficient at exactly the
sample used by current chart data, also after material enlargement.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationGauge

open Set ContinuousFlexibility.Statements CanonicalGeometry

variable (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)

def negativeChartWidthRatio (m : ℕ) : ℝ :=
  ((G.V η).right m - (G.V η).left m) /
    ((G.V η).physicalRight m - (G.V η).physicalLeft m)

/-- One coefficient envelope controls every retained half, with no
change of the material cell used to sample it. -/
theorem negativeChart_widthRatio_material :
    ∃ B : ℝ, 0 < B ∧ ∀ m, G.Neg η m →
      |G.negativeChartWidthRatio η m| ≤
        B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  obtain ⟨C, P, hC, hP, hlength⟩ :=
    n04bActualTypedAtlas_negative_length_material_bounds
      G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (C * C) (P + P)
  refine ⟨B, hB, fun m hm => ?_⟩
  obtain ⟨j, hi⟩ := (G.neg_iff_inl η m).mp hm
  let k : ℕ := G.negativeIndex j
  have hk : G.X.e₀ k = .inl (j.1, j.2) := G.X.e₀.apply_symm_apply _
  have hf := G.negative_fields η (G.W.C.referenceState, 0) m j hi
  have hb := hlength k j.1 j.2 hk
  have hA := n04b_actualTypedAtlas_partA
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀
  let K := G.W.A G.X.e₀
  let E : ℝ := G.W.T.E0 (G.W.T.sample (K.cell k))
  have hE : 1 ≤ E := G.W.floor _
  have hE₀ : 0 ≤ E := zero_le_one.trans hE
  have hp : 0 < K.physicalRight k - K.physicalLeft k :=
    sub_pos.mpr (hA.referenceBounds k).1
  have hc : 0 < K.right k - K.left k := sub_pos.mpr (hA.referenceBounds k).2.1
  have hratio : |G.negativeChartWidthRatio η m| ≤ B * E ^ B := by
    change |((G.V η).right m - (G.V η).left m) /
      ((G.V η).physicalRight m - (G.V η).physicalLeft m)| ≤ _
    rw [hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1]
    rw [div_eq_mul_inv, abs_mul, abs_of_pos hc, abs_of_pos (inv_pos.mpr hp)]
    calc
      _ ≤ (C * E ^ P) * (C * E ^ P) :=
        mul_le_mul hb.2.2.2 hb.1 (inv_pos.mpr hp).le
          (mul_nonneg hC.le (Real.rpow_nonneg hE₀ P))
      _ = (C * C) * E ^ (P + P) := by
        rw [Real.rpow_add (zero_lt_one.trans_le hE)]
        ring
      _ ≤ B * E ^ B := hpack E hE
  have hcell : (G.V η).cell m = K.cell k := hf.2.2.2.2.2.1
  have hEnlarge : E ≤ G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) := by
    rw [hcell]
    exact le_enlargedMaterialData_E0 G.W.T _
  exact hratio.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hE₀ hEnlarge hB.le) hB.le)

/-- The same envelope on the enumeration required by scalar calculus. -/
theorem negativeChart_widthRatio_enumerated :
    ∃ B : ℝ, 0 < B ∧ ∀ n,
      |G.negativeChartWidthRatio η (G.negativeChartPiece n)| ≤
        B * G.W.U.E0
          (G.W.U.sample (((G.V η).cell ∘ G.negativeChartPiece) n)) ^ B := by
  obtain ⟨B, hB, hbound⟩ := G.negativeChart_widthRatio_material η
  exact ⟨B, hB, fun n => hbound (G.negativeChartPiece n)
    (G.negativeChartPiece_negative η n)⟩

end ContinuousFlexibility.Analysis.N04RealizationGauge

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeChart_widthRatio_material' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeChart_widthRatio_material
