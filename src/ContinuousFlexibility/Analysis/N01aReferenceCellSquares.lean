module

public import ContinuousFlexibility.Analysis.N01aReferencePureRow
public import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# Removing a positive reference weight from cell squares

The attenuation exponent dominates every fixed multiple of the coefficient
exponent.  Thus a positive reference weight controls the unweighted sum of
the actual localized square integrals, for sources and outputs alike.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators

theorem radialAngularMean_nonneg {f : ℝ → ℝ} (hf : ∀ θ, 0 ≤ f θ) :
    0 ≤ radialAngularMean f := by
  unfold radialAngularMean
  exact mul_nonneg (inv_nonneg.mpr (by positivity))
    (intervalIntegral.integral_nonneg (by positivity) (fun θ _ => hf θ))

theorem n01a_referenceCellSquare_nonneg {D : ReferenceData} (hab : D.a ≤ D.b)
    (m : ℕ) (f : PolarPoint → ℝ) : 0 ≤ referenceCellSquare D m f := by
  apply intervalIntegral.integral_nonneg hab
  intro r _
  exact radialAngularMean_nonneg fun θ => sq_nonneg _

theorem n01a_sourceCellSquare_nonneg {D : ReferenceData} (hab : D.a ≤ D.b)
    (γ M : ℝ) (f : PolarPoint → ℝ) (m : ℕ) : 0 ≤ sourceCellSquare D γ M f m :=
  mul_nonneg (Real.exp_pos _).le (n01a_referenceCellSquare_nonneg hab m f)

theorem n01a_outputCellSquare_nonneg {D : ReferenceData} (hab : D.a ≤ D.b)
    (γ M : ℝ) (f : PolarPoint → ℝ) (m : ℕ) : 0 ≤ outputCellSquare D γ M f m :=
  mul_nonneg (Real.exp_pos _).le (n01a_referenceCellSquare_nonneg hab m f)

/-- Any positive attenuation exponent absorbs either sign of the fixed
coefficient loss, uniformly over all physical cell indices. -/
theorem exists_reference_weight_lower_bound {γ : ℝ} (hγ : 0 < γ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      1 ≤ C * Real.exp (2 * M * radialQ n + 2 * γ * radialS n) := by
  obtain ⟨A, hA⟩ := Radial.absorb_radialQ (-2 * M) γ hγ
  refine ⟨Real.exp A, Real.exp_pos _, fun n => ?_⟩
  have h := hA 0 n
  have hQ0 : radialQ 0 = 0 := by simp [radialQ]
  rw [hQ0, sub_zero, Radial.radialS_zero, zero_sub, abs_neg,
    abs_of_nonneg (Radial.radialS_nonneg n)] at h
  have hS := mul_nonneg hγ.le (Radial.radialS_nonneg n)
  rw [← Real.exp_add]
  exact Real.one_le_exp_iff.mpr (by linarith only [h, hS])

/-- A source's summable weighted cell squares control their unweighted sum. -/
theorem exists_source_cell_square_bound {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ : ℝ} (hγ : 0 < γ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : PolarPoint → ℝ,
      Summable (sourceCellSquare D γ M f) →
      Summable (fun m => referenceCellSquare D m f) ∧
        (∑' m, referenceCellSquare D m f) ≤ C * ∑' m, sourceCellSquare D γ M f m := by
  obtain ⟨C, hC, hw⟩ := exists_reference_weight_lower_bound hγ M
  refine ⟨C, hC, fun f hf => ?_⟩
  have hb (m : ℕ) : referenceCellSquare D m f ≤ C * sourceCellSquare D γ M f m := by
    have h := mul_le_mul_of_nonneg_right (hw (D.cellIndex m))
      (n01a_referenceCellSquare_nonneg hab m f)
    simpa only [one_mul, sourceCellSquare, mul_assoc] using h
  have hs : Summable (fun m => referenceCellSquare D m f) :=
    Summable.of_nonneg_of_le (fun m => n01a_referenceCellSquare_nonneg hab m f) hb
      (hf.mul_left C)
  refine ⟨hs, ?_⟩
  simpa only [tsum_mul_left] using hs.tsum_le_tsum hb (hf.mul_left C)

/-- The output convention has the opposite coefficient sign, which is
already included in the same numerical comparison. -/
theorem exists_output_cell_square_bound {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ : ℝ} (hγ : 0 < γ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : PolarPoint → ℝ,
      Summable (outputCellSquare D γ M f) →
      Summable (fun m => referenceCellSquare D m f) ∧
        (∑' m, referenceCellSquare D m f) ≤ C * ∑' m, outputCellSquare D γ M f m := by
  have he (f : PolarPoint → ℝ) :
      sourceCellSquare D γ (-M) f = outputCellSquare D γ M f := by
    funext m
    unfold sourceCellSquare outputCellSquare
    congr 2
    ring
  obtain ⟨C, hC, hb⟩ := exists_source_cell_square_bound hab hγ (-M)
  refine ⟨C, hC, fun f hf => ?_⟩
  have h := hb f
  rw [he f] at h
  exact h hf

end ContinuousFlexibility.Statements
