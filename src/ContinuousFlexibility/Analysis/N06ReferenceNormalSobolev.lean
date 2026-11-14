module

public import ContinuousFlexibility.Analysis.N06ReferenceAngularNormalBounds
public import ContinuousFlexibility.Analysis.N05ReferenceAngularSourceSobolev
public import ContinuousFlexibility.Analysis.N05ReferenceFullAngularSobolev

/-!
# All angular orders of the actual physical normal derivative

The original first-normal estimate chooses one weak radial derivative of
the same physical inverse. Its frequency estimates give weighted square
summability from actual source derivatives of two consecutive orders.
The existing weighted Fourier reconstruction produces the genuine weak
angular derivative of that normal field. Adding back the two low modes
retains the original material exponents at every order.

No canonical coordinate, radial smoothness of the source, or spectral
summability assumption is introduced.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- Actual weak source jets imply the high normal jet estimate. The same
normal field is fixed before its angular order is selected. -/
theorem n06_referenceInverse_highAngularNormalSobolev_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hN : FirstNormalInverseEstimate D γ M₀ M₁ G) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ F, SourceMember D γ M₀ F →
      ∀ ur : PolarPoint → ℝ, WeakNormalDerivative D (G F).1 ur →
      OutputRealization D γ M₁ 0 (ur, 0) → ∀ b : ℕ,
      ∀ fb fb₁ : PolarPoint → ℝ,
      SourceDerivativeMember D γ M₀ fb → SourceDerivativeMember D γ M₀ fb₁ →
      n05_weakReferenceAngularJet D F.1 fb b →
      n05_weakReferenceAngularJet D F.1 fb₁ (b + 1) →
      ∃ d : PolarPoint → ℝ,
        n05_weakReferenceAngularJet D (n05_referenceHighPart ur) d b ∧
        MemLp d 2 (referenceWeightedMeasure D γ (-M₁)) ∧
        outputNormSquare D γ M₁ 0 (d, 0) ≤
          C0 ^ 2 * (sourceNormSquare D γ M₀ (fb, 0) +
            sourceNormSquare D γ M₀ (fb₁, 0)) ∧
        Function.Periodic d (0, Real.pi) := by
  obtain ⟨C0, hC0, hmode⟩ :=
    n06_referenceInverse_highNormal_mode_bound hD hborder hγ hG hN
  refine ⟨C0, hC0, fun F hF ur hweak hreal b fb fb₁ hfb hfb₁ hwb hwb₁ => ?_⟩
  obtain ⟨hs, hb⟩ := n05_referenceHighWeakJet_source_summable_bound hD hγ hF hfb hwb
  obtain ⟨hs₁, hb₁⟩ := n05_referenceHighWeakJet_source_summable_bound hD hγ hF hfb₁ hwb₁
  have hnonneg (n : ℕ) :
      0 ≤ (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
        n05_referenceHighOutputSquare D γ M₁ (ur, 0) n :=
    mul_nonneg (by positivity) (hmode F hF ur hweak hreal n).1
  have hle (n : ℕ) :
      (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
          n05_referenceHighOutputSquare D γ M₁ (ur, 0) n ≤
        C0 ^ 2 *
          ((((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
              n05_referenceHighSourceSquare D γ M₀ F n +
            (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * (b + 1))) *
              n05_referenceHighSourceSquare D γ M₀ F n) := by
    calc
      _ ≤ (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
          (C0 ^ 2 * (1 + (((2 * (n + 2) : ℕ) : ℝ) ^ 2)) *
            n05_referenceHighSourceSquare D γ M₀ F n) :=
        mul_le_mul_of_nonneg_left (hmode F hF ur hweak hreal n).2 (by positivity)
      _ = _ := by
        rw [show 2 * (b + 1) = 2 * b + 2 by omega, pow_add]
        ring
  have hsC := (hs.add hs₁).mul_left (C0 ^ 2)
  have hout := hsC.of_nonneg_of_le hnonneg hle
  have hbound :
      (∑' n, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
        n05_referenceHighOutputSquare D γ M₁ (ur, 0) n) ≤
      C0 ^ 2 * (sourceNormSquare D γ M₀ (fb, 0) +
        sourceNormSquare D γ M₀ (fb₁, 0)) := by
    calc
      _ ≤ ∑' n, C0 ^ 2 *
          ((((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
              n05_referenceHighSourceSquare D γ M₀ F n +
            (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * (b + 1))) *
              n05_referenceHighSourceSquare D γ M₀ F n) :=
        Summable.tsum_le_tsum hle hout hsC
      _ = C0 ^ 2 *
          ((∑' n, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
            n05_referenceHighSourceSquare D γ M₀ F n) +
            ∑' n, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * (b + 1))) *
              n05_referenceHighSourceSquare D γ M₀ F n) := by
        rw [tsum_mul_left, hs.tsum_add hs₁]
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hb hb₁) (sq_nonneg C0)
  obtain ⟨d, hwd, hd, he, hp⟩ :=
    n05_referenceOutput_highWeakAngularJet hD hborder hγ hreal b hout
  exact ⟨d, hwd, hd, he.le.trans hbound, hp⟩

/-- The physical inverse has one true weak normal derivative with all
positive angular orders. The zero order is the separately displayed
original first-normal bound. Both material exponents are unchanged. -/
theorem n06_referenceInverse_allAngularNormalSobolev_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hN : FirstNormalInverseEstimate D γ M₀ M₁ G) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ F fθ,
      SourceMember D γ M₀ F → WeakAngularDerivative D F.1 fθ →
      SourceDerivativeMember D γ M₀ fθ →
      ∃ ur : PolarPoint → ℝ, WeakNormalDerivative D (G F).1 ur ∧
        OutputRealization D γ M₁ 0 (ur, 0) ∧
        outputNormSquare D γ M₁ 0 (ur, 0) ≤
          C0 ^ 2 * (sourceNormSquare D γ M₀ F + sourceNormSquare D γ M₀ (fθ, 0)) ∧
        ∀ b : ℕ, 0 < b → ∀ fb fb₁ : PolarPoint → ℝ,
          SourceDerivativeMember D γ M₀ fb → SourceDerivativeMember D γ M₀ fb₁ →
          n05_weakReferenceAngularJet D F.1 fb b →
          n05_weakReferenceAngularJet D F.1 fb₁ (b + 1) →
          ∃ d : PolarPoint → ℝ,
            n05_weakReferenceAngularJet D ur d b ∧
            MemLp d 2 (referenceWeightedMeasure D γ (-M₁)) ∧
            outputNormSquare D γ M₁ 0 (d, 0) ≤ C0 ^ 2 *
              (sourceNormSquare D γ M₀ (fb, 0) + sourceNormSquare D γ M₀ (fb₁, 0) +
                (2 : ℝ) ^ (2 * b) *
                  (sourceNormSquare D γ M₀ F + sourceNormSquare D γ M₀ (fθ, 0))) ∧
            Function.Periodic d (0, Real.pi) := by
  obtain ⟨Ch, hCh, hhigh⟩ :=
    n06_referenceInverse_highAngularNormalSobolev_bound hD hborder hγ hG hN
  obtain ⟨Cn, hCn, hnormal⟩ := hN
  let C0 : ℝ := 2 * (Ch + Cn)
  have hC0 : 0 < C0 := by dsimp only [C0]; positivity
  have hChC : 2 * Ch ^ 2 ≤ C0 ^ 2 := by
    dsimp only [C0]
    nlinarith only [sq_nonneg Ch, sq_nonneg Cn, mul_nonneg hCh.le hCn.le]
  have hCnC : 2 * Cn ^ 2 ≤ C0 ^ 2 := by
    dsimp only [C0]
    nlinarith only [sq_nonneg Ch, sq_nonneg Cn, mul_nonneg hCh.le hCn.le]
  have hCnC₁ : Cn ^ 2 ≤ C0 ^ 2 := by nlinarith only [sq_nonneg Cn, hCnC]
  refine ⟨C0, hC0, fun F fθ hF hfθ hθ => ?_⟩
  obtain ⟨ur, hwr, hreal, hbase⟩ := hnormal F fθ hF hfθ hθ
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hpart : RadialPartition D := hD.choose_spec.2.1
  have hSF : 0 ≤ sourceNormSquare D γ M₀ F := sourceNormSquare_nonneg hab hF
  have hSθ : 0 ≤ sourceNormSquare D γ M₀ (fθ, 0) :=
    add_nonneg (sq_nonneg _) (tsum_nonneg (sourceCellSquare_nonneg hab γ M₀ hθ.1))
  refine ⟨ur, hwr, hreal,
    hbase.trans (mul_le_mul_of_nonneg_right hCnC₁ (add_nonneg hSF hSθ)),
    fun b hb fb fb₁ hfb hfb₁ hwb hwb₁ => ?_⟩
  obtain ⟨d, hwd, hd, hbd, hdperiodic⟩ :=
    hhigh F hF ur hwr hreal b fb fb₁ hfb hfb₁ hwb hwb₁
  obtain ⟨he, hbe⟩ := n05_referenceLowAngularJet_output_bound hab hpart hreal hb
  obtain ⟨_, _, hphysical⟩ := n05_referenceWeighted_physical_square_bound hD hγ (-M₁)
  have hdp := (hphysical d hd).1
  have hep := (hphysical (n05_referenceLowAngularJet b ur) he).1
  have hur : MemLp ur 2 (radialPhysicalMeasure D) := by
    simpa only [n06_outputRemainder_zero] using r11b_outputRemainder_memLp hD hγ hreal
  have huProd : MemLp ur 2 ((volume.restrict (radialCore D)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [radialPhysicalMeasure_eq_prod] using hur
  have hlow : MemLp (referenceBasisProjection {0, 1} ur) 2 (radialPhysicalMeasure D) := by
    simpa only [radialPhysicalMeasure_eq_prod] using
      memLp_referenceBasisProjection_prod huProd {0, 1}
  have hwhole := n05_weakReferenceAngularJet_add hab (hur.sub hlow) hlow hdp hep hwd
    (n05_referenceLowAngularJet_weak D ur b)
  have hw : n05_weakReferenceAngularJet D ur (d + n05_referenceLowAngularJet b ur) b := by
    simpa only [n05_referenceHighPart, sub_add_cancel] using hwhole
  refine ⟨d + n05_referenceLowAngularJet b ur, hw, hd.add he, ?_,
    hdperiodic.add (n05_referenceLowAngularJet_periodic b ur)⟩
  have hSb : 0 ≤ sourceNormSquare D γ M₀ (fb, 0) :=
    add_nonneg (sq_nonneg _) (tsum_nonneg (sourceCellSquare_nonneg hab γ M₀ hfb.1))
  have hSb₁ : 0 ≤ sourceNormSquare D γ M₀ (fb₁, 0) :=
    add_nonneg (sq_nonneg _) (tsum_nonneg (sourceCellSquare_nonneg hab γ M₀ hfb₁.1))
  have hp : 0 ≤ (2 : ℝ) ^ (2 * b) := by positivity
  calc
    _ ≤ 2 * (outputNormSquare D γ M₁ 0 (d, 0) +
        outputNormSquare D γ M₁ 0 (n05_referenceLowAngularJet b ur, 0)) :=
      n05_referenceZeroOutputNormSquare_add_le hab hpart hd he
    _ ≤ 2 *
        (Ch ^ 2 * (sourceNormSquare D γ M₀ (fb, 0) + sourceNormSquare D γ M₀ (fb₁, 0)) +
          (2 : ℝ) ^ (2 * b) *
            (Cn ^ 2 * (sourceNormSquare D γ M₀ F + sourceNormSquare D γ M₀ (fθ, 0)))) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hbd (hbe.trans (mul_le_mul_of_nonneg_left hbase hp))) (by norm_num)
    _ = (2 * Ch ^ 2) *
        (sourceNormSquare D γ M₀ (fb, 0) + sourceNormSquare D γ M₀ (fb₁, 0)) +
        (2 * Cn ^ 2) * ((2 : ℝ) ^ (2 * b) *
          (sourceNormSquare D γ M₀ F + sourceNormSquare D γ M₀ (fθ, 0))) := by ring
    _ ≤ C0 ^ 2 *
        (sourceNormSquare D γ M₀ (fb, 0) + sourceNormSquare D γ M₀ (fb₁, 0)) +
        C0 ^ 2 * ((2 : ℝ) ^ (2 * b) *
          (sourceNormSquare D γ M₀ F + sourceNormSquare D γ M₀ (fθ, 0))) :=
      add_le_add (mul_le_mul_of_nonneg_right hChC (add_nonneg hSb hSb₁))
        (mul_le_mul_of_nonneg_right hCnC (mul_nonneg hp (add_nonneg hSF hSθ)))
    _ = _ := by ring

end ContinuousFlexibility.Radial
