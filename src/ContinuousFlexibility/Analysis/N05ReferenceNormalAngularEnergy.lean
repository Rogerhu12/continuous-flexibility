module

public import ContinuousFlexibility.Analysis.N05ReferenceNormalHighBlocks
public import ContinuousFlexibility.Analysis.N05ReferenceAngularSourceSobolev

/-!
# Every angular energy of the actual physical normal derivative

The two consecutive actual source jets supply the spectral square sums.
The singleton first-normal estimate then sums with the angular power.
The same normal derivative and material exponents serve every order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

theorem n05_referenceNormal_highAngular_summable_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M0 M1 MN : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M0 M1 G)
    (hN : FirstNormalInverseEstimate D γ M0 MN G) :
    ∃ C : ℝ, 0 < C ∧ ∀ F, SourceMember D γ M0 F →
      ∀ ur : PolarPoint → ℝ, WeakNormalDerivative D (G F).1 ur →
      OutputRealization D γ MN 0 (ur, 0) → ∀ (j : ℕ) (d e : PolarPoint → ℝ),
      SourceDerivativeMember D γ M0 d → SourceDerivativeMember D γ M0 e →
      n05_weakReferenceAngularJet D F.1 d j →
      n05_weakReferenceAngularJet D F.1 e (j + 1) →
      Summable (fun n => (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * j)) *
        n05_referenceHighOutputSquare D γ MN (ur, 0) n) ∧
      (∑' n, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * j)) *
        n05_referenceHighOutputSquare D γ MN (ur, 0) n) ≤
        C ^ 2 * (sourceNormSquare D γ M0 (d, 0) + sourceNormSquare D γ M0 (e, 0)) := by
  obtain ⟨C, hC, hblocks⟩ := n05_referenceNormal_highBlock_bound hD hborder hγ hG hN
  refine ⟨C, hC, fun F hF ur hur hUr j d e hd he hwd hwe => ?_⟩
  have hab := hD.choose_spec.1.2.1.le
  obtain ⟨hsd, hbd⟩ := n05_referenceHighWeakJet_source_summable_bound hD hγ hF hd hwd
  obtain ⟨hse, hbe⟩ := n05_referenceHighWeakJet_source_summable_bound hD hγ hF he hwe
  have hnonneg (n : ℕ) :
      0 ≤ (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * j)) *
        n05_referenceHighOutputSquare D γ MN (ur, 0) n :=
    mul_nonneg (by positivity)
      (outputNormSquare_nonneg hab (hblocks F hF ur hur hUr n).1)
  have hbound (n : ℕ) :
      (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * j)) *
          n05_referenceHighOutputSquare D γ MN (ur, 0) n ≤
        C ^ 2 * ((((2 * (n + 2) : ℕ) : ℝ) ^ (2 * j)) *
            n05_referenceHighSourceSquare D γ M0 F n +
          (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * (j + 1))) *
            n05_referenceHighSourceSquare D γ M0 F n) := by
    calc
      _ ≤ (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * j)) *
          (C ^ 2 * (1 + (((2 * (n + 2) : ℕ) : ℝ) ^ 2)) *
            n05_referenceHighSourceSquare D γ M0 F n) :=
        mul_le_mul_of_nonneg_left (hblocks F hF ur hur hUr n).2 (by positivity)
      _ = _ := by
        rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
        ring
  have hmajorant := (hsd.add hse).mul_left (C ^ 2)
  have hsout := hmajorant.of_nonneg_of_le hnonneg hbound
  refine ⟨hsout, ?_⟩
  calc
    _ ≤ ∑' n, C ^ 2 * ((((2 * (n + 2) : ℕ) : ℝ) ^ (2 * j)) *
          n05_referenceHighSourceSquare D γ M0 F n +
        (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * (j + 1))) *
          n05_referenceHighSourceSquare D γ M0 F n) :=
      hsout.tsum_le_tsum hbound hmajorant
    _ = C ^ 2 * ((∑' n, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * j)) *
        n05_referenceHighSourceSquare D γ M0 F n) +
      ∑' n, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * (j + 1))) *
        n05_referenceHighSourceSquare D γ M0 F n) := by
      rw [tsum_mul_left, hsd.tsum_add hse]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hbd hbe) (sq_nonneg C)

end ContinuousFlexibility.Radial
