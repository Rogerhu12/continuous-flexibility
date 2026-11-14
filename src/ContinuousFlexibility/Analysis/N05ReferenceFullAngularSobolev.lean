module

public import ContinuousFlexibility.Analysis.N05ReferenceAngularSobolev
public import ContinuousFlexibility.Analysis.N05ReferenceLowAngularEnergy
public import ContinuousFlexibility.Analysis.N05ReferenceLowAngularWeak

/-!
# Positive angular Sobolev estimates for the same full reference inverse

The high jet and the actual derivative of the two low modes add to a weak
derivative of the original output. The material exponents stay fixed. The
only order dependent factor is the elementary contribution of frequency two.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

theorem n05_referenceZeroOutputNormSquare_eq_integral {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D) {γ M : ℝ}
    {u : PolarPoint → ℝ} (hu : MemLp u 2 (referenceWeightedMeasure D γ (-M))) :
    outputNormSquare D γ M 0 (u, 0) =
      ∫ x, u x ^ 2 ∂referenceWeightedMeasure D γ (-M) := by
  obtain ⟨hc, hs⟩ := (memLp_referenceWeightedMeasure_iff hab hpart).mp hu
  rw [n05_zeroOutputNormSquare_eq_sourceNormSquare_neg]
  simpa only [sourceNormSquare, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using
    (integral_sq_referenceWeightedMeasure_eq hab hpart hc hs).symm

theorem n05_referenceZeroOutputNormSquare_add_le {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D) {γ M : ℝ}
    {u v : PolarPoint → ℝ}
    (hu : MemLp u 2 (referenceWeightedMeasure D γ (-M)))
    (hv : MemLp v 2 (referenceWeightedMeasure D γ (-M))) :
    outputNormSquare D γ M 0 (u + v, 0) ≤
      2 * (outputNormSquare D γ M 0 (u, 0) + outputNormSquare D γ M 0 (v, 0)) := by
  rw [n05_referenceZeroOutputNormSquare_eq_integral hab hpart (hu.add hv),
    n05_referenceZeroOutputNormSquare_eq_integral hab hpart hu,
    n05_referenceZeroOutputNormSquare_eq_integral hab hpart hv]
  calc
    (∫ x, (u + v) x ^ 2 ∂referenceWeightedMeasure D γ (-M)) ≤
        ∫ x, 2 * u x ^ 2 + 2 * v x ^ 2 ∂referenceWeightedMeasure D γ (-M) := by
      apply integral_mono (hu.add hv).integrable_sq
        ((hu.integrable_sq.const_mul 2).add (hv.integrable_sq.const_mul 2))
      intro x
      simp only [Pi.add_apply]
      nlinarith only [sq_nonneg (u x - v x)]
    _ = _ := by
      rw [integral_add (hu.integrable_sq.const_mul 2) (hv.integrable_sq.const_mul 2),
        integral_const_mul, integral_const_mul]
      ring

theorem n05_referenceInverse_positiveAngularSobolev_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ F, SourceMember D γ M₀ F →
      ∀ (b : ℕ), 0 < b → ∀ fder : PolarPoint → ℝ,
      SourceDerivativeMember D γ M₀ fder →
      n05_weakReferenceAngularJet D F.1 fder b →
      ∃ uder : PolarPoint → ℝ,
        n05_weakReferenceAngularJet D (G F).1 uder b ∧
        MemLp uder 2 (referenceWeightedMeasure D γ (-M₁)) ∧
        outputNormSquare D γ M₁ 0 (uder, 0) ≤ C ^ 2 *
          (sourceNormSquare D γ M₀ (fder, 0) +
            (2 : ℝ) ^ (2 * b) * sourceNormSquare D γ M₀ F) ∧
        Function.Periodic uder (0, Real.pi) := by
  obtain ⟨Ch, hCh, hhigh⟩ := n05_referenceInverse_highAngularSobolev_bound hD hborder hγ hG
  obtain ⟨Cg, hCg, hbase⟩ := hG.2.2.2
  let C : ℝ := 2 * (Ch + Cg)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hChC : 2 * Ch ^ 2 ≤ C ^ 2 := by
    dsimp only [C]
    nlinarith only [sq_nonneg Ch, sq_nonneg Cg, mul_nonneg hCh.le hCg.le]
  have hCgC : 2 * Cg ^ 2 ≤ C ^ 2 := by
    dsimp only [C]
    nlinarith only [sq_nonneg Ch, sq_nonneg Cg, mul_nonneg hCh.le hCg.le]
  refine ⟨C, hC, fun F hF b hb fder hfd hweak => ?_⟩
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  have hpart : RadialPartition D := hD.choose_spec.2.1
  obtain ⟨d, hwd, hd, hbd, hdperiodic⟩ := hhigh F hF b fder hfd hweak
  obtain ⟨a, hU, hbU⟩ := hbase F hF
  obtain ⟨he, hbe⟩ := n05_referenceLowAngularJet_output_bound hab hpart hU hb
  obtain ⟨_, _, hphysical⟩ := n05_referenceWeighted_physical_square_bound hD hγ (-M₁)
  have hdp := (hphysical d hd).1
  have hep := (hphysical (n05_referenceLowAngularJet b (G F).1) he).1
  have hu : MemLp (G F).1 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hborder hγ ⟨a, hU⟩
  have hprod : MemLp (G F).1 2 ((volume.restrict (radialCore D)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [radialPhysicalMeasure_eq_prod] using hu
  have hlow : MemLp (referenceBasisProjection {0, 1} (G F).1) 2
      (radialPhysicalMeasure D) := by
    simpa only [radialPhysicalMeasure_eq_prod] using
      memLp_referenceBasisProjection_prod hprod {0, 1}
  have hwhole := n05_weakReferenceAngularJet_add hab (hu.sub hlow) hlow hdp hep hwd
    (n05_referenceLowAngularJet_weak D (G F).1 b)
  have hw : n05_weakReferenceAngularJet D (G F).1
      (d + n05_referenceLowAngularJet b (G F).1) b := by
    simpa only [n05_referenceHighPart, sub_add_cancel] using hwhole
  refine ⟨d + n05_referenceLowAngularJet b (G F).1, hw, hd.add he, ?_,
    hdperiodic.add (n05_referenceLowAngularJet_periodic b (G F).1)⟩
  have hSF := sourceNormSquare_nonneg hab hF
  have hSD : 0 ≤ sourceNormSquare D γ M₀ (fder, 0) :=
    add_nonneg (sq_nonneg _) (tsum_nonneg (sourceCellSquare_nonneg hab γ M₀ hfd.1))
  have hp : 0 ≤ (2 : ℝ) ^ (2 * b) := by positivity
  calc
    _ ≤ 2 * (outputNormSquare D γ M₁ 0 (d, 0) +
        outputNormSquare D γ M₁ 0 (n05_referenceLowAngularJet b (G F).1, 0)) :=
      n05_referenceZeroOutputNormSquare_add_le hab hpart hd he
    _ ≤ 2 * (Ch ^ 2 * sourceNormSquare D γ M₀ (fder, 0) +
        (2 : ℝ) ^ (2 * b) * (Cg ^ 2 * sourceNormSquare D γ M₀ F)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hbd (hbe.trans (mul_le_mul_of_nonneg_left hbU hp))) (by norm_num)
    _ = (2 * Ch ^ 2) * sourceNormSquare D γ M₀ (fder, 0) +
        (2 * Cg ^ 2) * ((2 : ℝ) ^ (2 * b) * sourceNormSquare D γ M₀ F) := by ring
    _ ≤ C ^ 2 * sourceNormSquare D γ M₀ (fder, 0) +
        C ^ 2 * ((2 : ℝ) ^ (2 * b) * sourceNormSquare D γ M₀ F) :=
      add_le_add (mul_le_mul_of_nonneg_right hChC hSD)
        (mul_le_mul_of_nonneg_right hCgC (mul_nonneg hp hSF))
    _ = _ := by ring

end ContinuousFlexibility.Radial
