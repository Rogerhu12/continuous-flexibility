module

public import ContinuousFlexibility.Analysis.N05ReferenceNormalAngularEnergy
public import ContinuousFlexibility.Analysis.N05ReferenceOutputAngularSobolev
public import ContinuousFlexibility.Radial.R11bAngularFrequencySource

/-!
# Angular regularity of the same actual physical normal derivative

One first-normal derivative is selected before the angular order. Its
positive angular weak jets are reconstructed from consecutive source
jets, retaining the same material exponent and the original physical
normal weak identity. Low modes cost only their fixed frequency power.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

theorem n05_referenceNormal_allAngular_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M0 M1 MN : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M0 M1 G)
    (hN : FirstNormalInverseEstimate D γ M0 MN G) :
    ∃ C : ℝ, 0 < C ∧ ∀ F, SourceMember D γ M0 F →
      ∀ fθ : PolarPoint → ℝ, SourceDerivativeMember D γ M0 fθ →
      WeakAngularDerivative D F.1 fθ →
      ∃ ur : PolarPoint → ℝ, WeakNormalDerivative D (G F).1 ur ∧
        OutputRealization D γ MN 0 (ur, 0) ∧
        outputNormSquare D γ MN 0 (ur, 0) ≤
          C ^ 2 * (sourceNormSquare D γ M0 F + sourceNormSquare D γ M0 (fθ, 0)) ∧
        ∀ (j : ℕ), 0 < j → ∀ d e : PolarPoint → ℝ,
          SourceDerivativeMember D γ M0 d → SourceDerivativeMember D γ M0 e →
          n05_weakReferenceAngularJet D F.1 d j →
          n05_weakReferenceAngularJet D F.1 e (j + 1) →
          ∃ v : PolarPoint → ℝ, n05_weakReferenceAngularJet D ur v j ∧
            MemLp v 2 (referenceWeightedMeasure D γ (-MN)) ∧
            outputNormSquare D γ MN 0 (v, 0) ≤
              C ^ 2 * (sourceNormSquare D γ M0 (d, 0) + sourceNormSquare D γ M0 (e, 0) +
                (2 : ℝ) ^ (2 * j) *
                  (sourceNormSquare D γ M0 F + sourceNormSquare D γ M0 (fθ, 0))) ∧
            Function.Periodic v (0, Real.pi) := by
  obtain ⟨CB, hCB, hb⟩ := n05_referenceNormal_highAngular_summable_bound hD hborder hγ hG hN
  obtain ⟨CN, hCN, hn⟩ := hN
  let C : ℝ := 2 * (CN + CB)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCNle : 2 * CN ^ 2 ≤ C ^ 2 := by
    dsimp only [C]
    nlinarith only [sq_nonneg CN, sq_nonneg CB, mul_nonneg hCN.le hCB.le]
  have hCBle : 2 * CB ^ 2 ≤ C ^ 2 := by
    dsimp only [C]
    nlinarith only [sq_nonneg CN, sq_nonneg CB, mul_nonneg hCN.le hCB.le]
  have hCNle' : CN ^ 2 ≤ C ^ 2 := (by nlinarith only [sq_nonneg CN, hCNle])
  refine ⟨C, hC, fun F hF fθ hfθ hwθ => ?_⟩
  have hab := hD.choose_spec.1.2.1.le
  have hnS (f : PolarPoint → ℝ) : 0 ≤ sourceNormSquare D γ M0 (f, 0) :=
    r11b_sourceNormSquare_nonneg hab γ M0 (f, 0)
  have hbase : 0 ≤ sourceNormSquare D γ M0 F + sourceNormSquare D γ M0 (fθ, 0) :=
    add_nonneg (sourceNormSquare_nonneg hab hF) (hnS fθ)
  obtain ⟨ur, hur, hUr, hUrbound⟩ := hn F fθ hF hwθ hfθ
  refine ⟨ur, hur, hUr,
    hUrbound.trans (mul_le_mul_of_nonneg_right hCNle' hbase), ?_⟩
  intro j hj d e hd he hwd hwe
  obtain ⟨hs, hsum⟩ := hb F hF ur hur hUr j d e hd he hwd hwe
  obtain ⟨v, hv, hvLp, hvbound, hvp⟩ :=
    n05_referenceOutput_positiveAngular_bound hD hborder hγ hUr hj hs
  refine ⟨v, hv, hvLp, ?_, hvp⟩
  have hp : 0 ≤ (2 : ℝ) ^ (2 * j) := by positivity
  calc
    _ ≤ 2 * (CB ^ 2 * (sourceNormSquare D γ M0 (d, 0) + sourceNormSquare D γ M0 (e, 0)) +
        (2 : ℝ) ^ (2 * j) *
          (CN ^ 2 * (sourceNormSquare D γ M0 F + sourceNormSquare D γ M0 (fθ, 0)))) :=
      hvbound.trans (mul_le_mul_of_nonneg_left
        (add_le_add hsum (mul_le_mul_of_nonneg_left hUrbound hp)) (by norm_num))
    _ = (2 * CB ^ 2) * (sourceNormSquare D γ M0 (d, 0) + sourceNormSquare D γ M0 (e, 0)) +
        (2 * CN ^ 2) * ((2 : ℝ) ^ (2 * j) *
          (sourceNormSquare D γ M0 F + sourceNormSquare D γ M0 (fθ, 0))) := by ring
    _ ≤ C ^ 2 * (sourceNormSquare D γ M0 (d, 0) + sourceNormSquare D γ M0 (e, 0)) +
        C ^ 2 * ((2 : ℝ) ^ (2 * j) *
          (sourceNormSquare D γ M0 F + sourceNormSquare D γ M0 (fθ, 0))) :=
      add_le_add (mul_le_mul_of_nonneg_right hCBle (add_nonneg (hnS d) (hnS e)))
        (mul_le_mul_of_nonneg_right hCNle (mul_nonneg hp hbase))
    _ = _ := by ring

end ContinuousFlexibility.Radial
