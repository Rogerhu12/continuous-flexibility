import ContinuousFlexibility.Analysis.N05CanonicalEmbeddings
import ContinuousFlexibility.Scalar.WeightedReferenceCoefficients

/-!
# Physical coefficient factors are absorbed by the canonical sample weights

A fixed coefficient power costs one actual material factor at the chosen
cell sample. Every positive endpoint exponent absorbs that material factor
and every prescribed material order, uniformly in the canonical piece.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

theorem n05_canonicalSample_square_weight (T : MaterialData) (S : PhysicalSpacesData)
    (K : CanonicalData S) (γ t : ℝ) (m : ℕ)
    (hM : 0 < T.M (T.sample (K.cell m))) (hH : 0 < T.H (T.sample (K.cell m))) :
    T.M (T.sample (K.cell m)) * (n05CanonicalSampleWeight T S K γ t m) ^ 2 =
      n05CanonicalSampleWeight T S K (2 * γ) (2 * t - 1) m := by
  let M := T.M (T.sample (K.cell m))
  let H := T.H (T.sample (K.cell m))
  change M * (M ^ (-t) * H ^ γ) ^ 2 = M ^ (-(2 * t - 1)) * H ^ (2 * γ)
  calc
    M * (M ^ (-t) * H ^ γ) ^ 2 =
        (M ^ (1 : ℝ) * M ^ (-t) * M ^ (-t)) * (H ^ γ * H ^ γ) := by
      rw [Real.rpow_one]
      ring
    _ = M ^ ((1 : ℝ) + -t + -t) * H ^ (γ + γ) := by
      rw [← Real.rpow_add hM, ← Real.rpow_add hM, ← Real.rpow_add hH]
    _ = _ := by congr 2 <;> ring

/-- Every fixed coefficient loss is uniformly absorbed by the square of
the actual positive endpoint sample weight. -/
theorem n05_canonicalSample_coefficient_square_bound
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (S : PhysicalSpacesData) (K : CanonicalData S)
    {γ A : ℝ} (hγ : 0 < γ) (hA : 0 ≤ A) (t : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m,
      radialE (D.cellIndex (K.cell m)) ^ A *
        (n05CanonicalSampleWeight T S K γ t m) ^ 2 ≤ B := by
  obtain ⟨C, hC, hcoeff⟩ := referenceCellCoefficient_le_materialM hD hT hA
  have hPart : RadialPartition D := hD.choose_spec.2.1
  obtain ⟨B, hB, hweight⟩ := n05_materialSampleWeight_bound hT hPart
    (show 0 < 2 * γ by linarith) (2 * t - 1) K.cell
  have hsample : ∀ m, T.sample m ∈ D.cells m := by
    rcases hT with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _⟩
    exact hsample
  refine ⟨C * B, mul_pos hC hB, fun m => ?_⟩
  have hr := materialSample_mem_radialCore hT hPart (K.cell m)
  have hM : 0 < T.M (T.sample (K.cell m)) :=
    zero_lt_one.trans_le (hT.2.1 _ hr).2.2.2
  have hH : 0 < T.H (T.sample (K.cell m)) := (hT.2.1 _ hr).2.1
  calc
    _ ≤ (C * T.M (T.sample (K.cell m))) *
        (n05CanonicalSampleWeight T S K γ t m) ^ 2 :=
      mul_le_mul_of_nonneg_right (hcoeff _ _ (hsample (K.cell m))) (sq_nonneg _)
    _ = C * n05CanonicalSampleWeight T S K (2 * γ) (2 * t - 1) m := by
      rw [mul_assoc, n05_canonicalSample_square_weight T S K γ t m hM hH]
    _ ≤ C * B := mul_le_mul_of_nonneg_left (hweight m) hC.le

end ContinuousFlexibility.Statements

