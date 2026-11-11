import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# Strict exponent embeddings for the reference inverse

A strict increase of the attenuation exponent dominates every fixed change of
the coefficient exponent.  The estimates below apply to the actual cell
squares and preserve the representative and the left constant.  In particular,
they transport a maximum weak graph into a lower-exponent graph, so that the
latter graph's uniqueness applies without changing its output exponent.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real MeasureTheory
open ContinuousFlexibility.Statements

theorem r11b_referenceCellSquare_nonneg {D : ReferenceData} (hab : D.a ≤ D.b)
    (m : ℕ) (f : PolarPoint → ℝ) : 0 ≤ referenceCellSquare D m f := by
  unfold referenceCellSquare
  apply intervalIntegral.integral_nonneg hab
  intro r _
  unfold radialAngularMean
  apply mul_nonneg
  · positivity
  · exact intervalIntegral.integral_nonneg (by positivity)
      (fun θ _ => sq_nonneg (D.localizer m r * f (r, θ)))

/-- The embedding constant is independent of the cell and is at least one. -/
theorem r11b_exp_weight_le (a b γlo γhi : ℝ) (hγ : γlo < γhi) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ,
      exp (a * radialQ n + 2 * γlo * radialS n) ≤
        K * exp (b * radialQ n + 2 * γhi * radialS n) := by
  obtain ⟨C, hC⟩ := absorb_radialQ (a - b) (2 * (γhi - γlo)) (by linarith)
  have hQ0 : radialQ 0 = 0 := by norm_num [radialQ]
  refine ⟨exp C + 1, by linarith [exp_pos C], fun n => ?_⟩
  have hn := hC 0 n
  rw [hQ0, sub_zero, radialS_zero, zero_sub, abs_neg,
    abs_of_nonneg (radialS_nonneg n)] at hn
  have hexp : exp (a * radialQ n + 2 * γlo * radialS n) ≤
      exp C * exp (b * radialQ n + 2 * γhi * radialS n) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    nlinarith
  exact hexp.trans (mul_le_mul_of_nonneg_right
    (by linarith : exp C ≤ exp C + 1) (exp_pos _).le)

/-- A nonnegative cell-square series transfers through a pointwise weight bound. -/
theorem r11b_weighted_tsum_le (w v x : ℕ → ℝ) {K : ℝ}
    (hw : ∀ m, 0 ≤ w m) (hx : ∀ m, 0 ≤ x m)
    (hweight : ∀ m, w m ≤ K * v m) (hs : Summable (fun m => v m * x m)) :
    Summable (fun m => w m * x m) ∧
      (∑' m, w m * x m) ≤ K * ∑' m, v m * x m := by
  have hbound : ∀ m, w m * x m ≤ K * (v m * x m) := by
    intro m
    calc w m * x m ≤ (K * v m) * x m :=
        mul_le_mul_of_nonneg_right (hweight m) (hx m)
      _ = K * (v m * x m) := mul_assoc _ _ _
  have hmajor := hs.mul_left K
  have hminor : Summable (fun m => w m * x m) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (hw m) (hx m)) hbound hmajor
  refine ⟨hminor, ?_⟩
  calc (∑' m, w m * x m) ≤ ∑' m, K * (v m * x m) :=
      Summable.tsum_le_tsum hbound hminor hmajor
    _ = K * ∑' m, v m * x m := tsum_mul_left

/-- A strict exponent margin absorbs arbitrary source coefficient weights. -/
theorem r11b_source_embedding {D : ReferenceData} (hab : D.a ≤ D.b)
    (Mlo Mhi γlo γhi : ℝ) (hγ : γlo < γhi) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ F : RadialSource, SourceMember D γhi Mhi F →
      SourceMember D γlo Mlo F ∧
        sourceNormSquare D γlo Mlo F ≤ K * sourceNormSquare D γhi Mhi F := by
  obtain ⟨K, hK, hweight⟩ := r11b_exp_weight_le (2 * Mlo) (2 * Mhi) γlo γhi hγ
  refine ⟨K, hK, fun F hF => ?_⟩
  obtain ⟨hs, hnorm⟩ := r11b_weighted_tsum_le
    (fun m => exp (2 * Mlo * radialQ (D.cellIndex m) + 2 * γlo * radialS (D.cellIndex m)))
    (fun m => exp (2 * Mhi * radialQ (D.cellIndex m) + 2 * γhi * radialS (D.cellIndex m)))
    (fun m => referenceCellSquare D m F.1)
    (fun _ => (exp_pos _).le) (fun m => r11b_referenceCellSquare_nonneg hab m F.1)
    (fun m => hweight (D.cellIndex m)) hF.2.1
  refine ⟨⟨hF.1, hs, hF.2.2⟩, ?_⟩
  have hscalar : F.2 ^ 2 ≤ K * F.2 ^ 2 :=
    le_mul_of_one_le_left (sq_nonneg _) hK
  change F.2 ^ 2 + (∑' m, sourceCellSquare D γlo Mlo F.1 m) ≤
    K * (F.2 ^ 2 + ∑' m, sourceCellSquare D γhi Mhi F.1 m)
  change (∑' m, sourceCellSquare D γlo Mlo F.1 m) ≤
    K * ∑' m, sourceCellSquare D γhi Mhi F.1 m at hnorm
  nlinarith

theorem r11b_sourceMember_of_lt {D : ReferenceData} (hab : D.a ≤ D.b)
    {Mlo Mhi γlo γhi : ℝ} (hγ : γlo < γhi) {F : RadialSource}
    (hF : SourceMember D γhi Mhi F) : SourceMember D γlo Mlo F := by
  obtain ⟨_, _, h⟩ := r11b_source_embedding hab Mlo Mhi γlo γhi hγ
  exact (h F hF).1

/-- The same left constant realizes the output in every strictly lower exponent. -/
theorem r11b_output_embedding {D : ReferenceData} (hab : D.a ≤ D.b)
    (Mlo Mhi γlo γhi : ℝ) (hγ : γlo < γhi) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (aL : ℝ) (U : RadialUnknown),
      OutputRealization D γhi Mhi aL U →
        OutputRealization D γlo Mlo aL U ∧
          outputNormSquare D γlo Mlo aL U ≤ K * outputNormSquare D γhi Mhi aL U := by
  obtain ⟨K, hK, hweight⟩ := r11b_exp_weight_le (-2 * Mlo) (-2 * Mhi) γlo γhi hγ
  refine ⟨K, hK, fun aL U hU => ?_⟩
  obtain ⟨hs, hnorm⟩ := r11b_weighted_tsum_le
    (fun m => exp (-2 * Mlo * radialQ (D.cellIndex m) + 2 * γlo * radialS (D.cellIndex m)))
    (fun m => exp (-2 * Mhi * radialQ (D.cellIndex m) + 2 * γhi * radialS (D.cellIndex m)))
    (fun m => referenceCellSquare D m (outputRemainder D aL U))
    (fun _ => (exp_pos _).le)
    (fun m => r11b_referenceCellSquare_nonneg hab m (outputRemainder D aL U))
    (fun m => hweight (D.cellIndex m)) hU.2.1
  refine ⟨⟨hU.1, hs, hU.2.2⟩, ?_⟩
  have hscalar : aL ^ 2 + U.2 ^ 2 ≤ K * (aL ^ 2 + U.2 ^ 2) :=
    le_mul_of_one_le_left (add_nonneg (sq_nonneg _) (sq_nonneg _)) hK
  change aL ^ 2 + U.2 ^ 2 +
      (∑' m, outputCellSquare D γlo Mlo (outputRemainder D aL U) m) ≤
    K * (aL ^ 2 + U.2 ^ 2 +
      ∑' m, outputCellSquare D γhi Mhi (outputRemainder D aL U) m)
  change (∑' m, outputCellSquare D γlo Mlo (outputRemainder D aL U) m) ≤
    K * ∑' m, outputCellSquare D γhi Mhi (outputRemainder D aL U) m at hnorm
  nlinarith

theorem r11b_outputRealization_of_lt {D : ReferenceData} (hab : D.a ≤ D.b)
    {Mlo Mhi γlo γhi aL : ℝ} (hγ : γlo < γhi) {U : RadialUnknown}
    (hU : OutputRealization D γhi Mhi aL U) : OutputRealization D γlo Mlo aL U := by
  obtain ⟨_, _, h⟩ := r11b_output_embedding hab Mlo Mhi γlo γhi hγ
  exact (h aL U hU).1

theorem r11b_outputMember_of_lt {D : ReferenceData} (hab : D.a ≤ D.b)
    {Mlo Mhi γlo γhi : ℝ} (hγ : γlo < γhi) {U : RadialUnknown}
    (hU : OutputMember D γhi Mhi U) : OutputMember D γlo Mlo U := by
  obtain ⟨aL, haL⟩ := hU
  exact ⟨aL, r11b_outputRealization_of_lt hab hγ haL⟩

/-- The weak equation and border row do not depend on the weight exponents. -/
theorem r11b_referenceGraph_of_lt {D : ReferenceData} (hab : D.a ≤ D.b)
    {M₀lo M₀hi M₁lo M₁hi γlo γhi : ℝ} (hγ : γlo < γhi)
    {U : RadialUnknown} {F : RadialSource}
    (h : ReferenceGraph D γhi M₀hi M₁hi U F) :
    ReferenceGraph D γlo M₀lo M₁lo U F :=
  ⟨r11b_outputMember_of_lt hab hγ h.1, r11b_sourceMember_of_lt hab hγ h.2.1, h.2.2⟩

/-- Uniqueness remains available after an arbitrary coefficient-weight change
when the new attenuation exponent lies strictly above the old one. -/
theorem r11b_unique_of_lower_exponent {D : ReferenceData} (hab : D.a ≤ D.b)
    {M₀lo M₀hi M₁lo M₁hi γlo γhi : ℝ} (hγ : γlo < γhi)
    {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γlo M₀lo M₁lo G)
    {U : RadialUnknown} {F : RadialSource}
    (h : ReferenceGraph D γhi M₀hi M₁hi U F) :
    RadialRepresentativeEq D (G F) U :=
  hG.2.1 U F (r11b_referenceGraph_of_lt hab hγ h)

end ContinuousFlexibility.Radial
