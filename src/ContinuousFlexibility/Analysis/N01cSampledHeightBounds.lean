import ContinuousFlexibility.Analysis.N01cPhysicalHeightBounds
import ContinuousFlexibility.Analysis.N01cMaterialShiftComparison

/-!
# Physical height jets at the actual cell samples

The pointwise physical estimate is transferred to the prescribed material
sample of the cell. The power of H stays exactly γ, and the input grading
retains its fixed two-derivative loss.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

/-- Uniform sampled-weight control of every physical mixed height jet of
total order at most s, for the original decoded Sobolev height. -/
theorem sobolevModel_physicalMixedJets_le_sampledE0_grading
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (hM : IsSobolevModel D T γ M) (s : ℕ) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ u : M.Space, ∀ a b m : ℕ, a + b ≤ s →
      ∀ p : PolarPoint, p.1 ∈ D.cells m →
        |mixedDerivative a b (M.decode u) p| ≤
          C * T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ A *
            M.grading (s + 2) u := by
  obtain ⟨C₀, A₀, hC₀, _, hbound⟩ :=
    sobolevModel_physicalMixedJets_le_E0_grading hT hM s
  obtain ⟨C₁, A, hC₁, hA, hcompare⟩ :=
    materialCell_weight_comparison hT hRef γ A₀
  obtain ⟨_, hRefBounds⟩ := hRef
  have hPart := hRefBounds.2.1
  refine ⟨C₀ * C₁ + 1, A, by positivity, hA,
    fun u a b m hab p hp => ?_⟩
  have hr : p.1 ∈ Ioo D.a D.b := hPart.2.2.2.1 m hp
  have hs := materialSample_mem_radialCore hT hPart m
  have hH : 0 ≤ T.H (T.sample m) ^ γ :=
    Real.rpow_nonneg (hT.2.1 _ hs).2.1.le _
  have hE : 0 ≤ T.E0 (T.sample m) ^ A :=
    Real.rpow_nonneg (hT.2.1 _ hs).2.2.1.le _
  have hg : 0 ≤ M.grading (s + 2) u := apply_nonneg _ _
  calc
    |mixedDerivative a b (M.decode u) p| ≤
        C₀ * T.E0 p.1 ^ A₀ * T.H p.1 ^ γ * M.grading (s + 2) u :=
      hbound u a b hab p ⟨hr, mem_univ _⟩
    _ = C₀ * (T.H p.1 ^ γ * T.E0 p.1 ^ A₀) * M.grading (s + 2) u := by ring
    _ ≤ C₀ * (C₁ * T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ A) *
        M.grading (s + 2) u :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcompare m p.1 hp).1 hC₀) hg
    _ = (C₀ * C₁) * T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ A *
        M.grading (s + 2) u := by ring
    _ ≤ (C₀ * C₁ + 1) * T.H (T.sample m) ^ γ * T.E0 (T.sample m) ^ A *
        M.grading (s + 2) u :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith) hH) hE) hg

end ContinuousFlexibility.Statements
