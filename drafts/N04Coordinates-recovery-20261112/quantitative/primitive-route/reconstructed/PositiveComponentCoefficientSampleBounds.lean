import ContinuousFlexibility.Analysis.PositiveComponentMaterialDecay
import ContinuousFlexibility.Analysis.N01CoefficientDifferenceFlatExtension

/-!
# Actual N01 differences at one whole-positive sample

The reference midpoint chooses the material cell before the order and
state. The true N01 pointwise coefficient bound then retains any fixed
positive sample-height exponent below three quarters. Its original
spatial loss and paired state grading are unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

theorem exists_wholePositive_coefficientDifference_sample_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hN : N01Properties D T S C base loss ε) :
    ∃ cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ,
      (∀ j, n04PositiveMidpoint j ∈ D.cells (cell j)) ∧
      (∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ j r,
        r ∈ Icc (n04PositiveLeft j) (n04PositiveRight j) → r ∈ Ioo D.a D.b →
        T.H r / T.H (T.sample (cell j)) ≤ B * T.E0 r ^ A) ∧
      (∀ R : ℝ, 0 ≤ R → ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ j r,
        r ∈ Icc (n04PositiveLeft j) (n04PositiveRight j) → r ∈ Ioo D.a D.b →
        T.E0 (T.sample (cell j)) ^ R ≤ B * T.E0 r ^ A) ∧
      ∀ β : ℝ, 0 < β → β < (3 / 4 : ℝ) → ∀ s : ℕ,
        ∃ K : ℝ, 0 < K ∧ ∀ j i a b (p : PolarPoint),
          a + b ≤ s → p.1 ∈ Icc (n04PositiveLeft j) (n04PositiveRight j) →
          p ∈ annularOpen D → ∀ z ∈ stateNeighborhood S C base ε,
          |mixedDerivative a b (n01OriginalCoefficientDifference D S C z i) p| ≤
            K * T.H (T.sample (cell j)) ^ β *
              (1 + pairGrading (stateGrading S) realGrading (s + loss)
                (z - (C.referenceState, 0))) := by
  obtain ⟨cell, hcell, hnormalizer, hsample, hdecay⟩ :=
    exists_wholePositive_midpoint_material_decay hT hN.1.1
  refine ⟨cell, hcell, hnormalizer, hsample, ?_⟩
  intro β hβ hβtop s
  obtain ⟨K, A, hK, _, hpoint⟩ :=
    n01OriginalCoefficientDifference_point_weight_bound hT hN s
  obtain ⟨B, hB, hb⟩ := hdecay (3 / 4 : ℝ) β A hβ hβtop
  refine ⟨K * B, mul_pos hK hB, ?_⟩
  intro j i a b p hab hpj hp z hz
  let W : ℝ := 1 + pairGrading (stateGrading S) realGrading (s + loss)
    (z - (C.referenceState, 0))
  have hW : 0 ≤ W := add_nonneg zero_le_one (apply_nonneg _ _)
  calc
    _ ≤ K * T.H p.1 ^ (3 / 4 : ℝ) * T.E0 p.1 ^ A * W :=
      hpoint i a b p hab hp z hz
    _ = K * (T.H p.1 ^ (3 / 4 : ℝ) * T.E0 p.1 ^ A) * W := by ring
    _ ≤ K * (B * T.H (T.sample (cell j)) ^ β) * W :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb j p.1 hpj hp.1) hK.le) hW
    _ = _ := by dsimp only [W]; ring

end ContinuousFlexibility.Analysis
