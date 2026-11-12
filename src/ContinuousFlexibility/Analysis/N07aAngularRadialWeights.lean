import ContinuousFlexibility.Analysis.N07aAngularMaterialWeights
import ContinuousFlexibility.Radial.R11bWeightedCellClosure

/-!
# Genuine physical decay implies the reference weighted cell graph norms

The original nonnegative partition of one controls the sum of its squared
localizers. Thus a uniform weighted pointwise bound yields a summable
reference cell-square series, without any bound on the number of cells
with one index. The final comparison applies to arbitrary material data.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory Real ContinuousFlexibility.Radial
open scoped BigOperators

theorem n07a_reference_cells_of_weighted_bound {D : ReferenceData}
    (hpart : RadialPartition D) (hab : D.a ≤ D.b)
    {f : PolarPoint → ℝ} (hf : AEStronglyMeasurable f (radialPhysicalMeasure D))
    (γ A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ m p, p.1 ∈ D.cells m →
      Real.exp (γ * radialS (D.cellIndex m)) * |f p| ≤ A) :
    RadialCellIntegrable D f ∧ Summable (sourceCellSquare D γ 0 f) ∧
      (∑' m, sourceCellSquare D γ 0 f m) ≤
        (2 * Real.pi)⁻¹ * ∫ _ : PolarPoint, A ^ 2 ∂radialPhysicalMeasure D := by
  classical
  let : IsFiniteMeasure (radialPhysicalMeasure D) :=
    ⟨r11b_radialPhysicalMeasure_finite D⟩
  let w : ℕ → ℝ := fun m => Real.exp (γ * radialS (D.cellIndex m))
  have hw (m : ℕ) : 0 < w m := Real.exp_pos _
  have hcell : RadialCellIntegrable D f := by
    intro m
    apply MemLp.of_bound
      (((hpart.1 m).continuous.comp continuous_fst).aestronglyMeasurable.mul hf) (A / w m)
    apply Eventually.of_forall
    intro p
    rw [Real.norm_eq_abs]
    simp only [Pi.mul_apply, Function.comp_apply]
    by_cases hχ : D.localizer m p.1 = 0
    · simp only [hχ, zero_mul, abs_zero]
      exact div_nonneg hA (hw m).le
    · have hb := hbound m p (hpart.2.2.1 m hχ)
      have hχb := profile_localizer_bounds hpart m p.1
      apply (le_div_iff₀ (hw m)).mpr
      rw [abs_mul, abs_of_nonneg hχb.1]
      calc
        D.localizer m p.1 * |f p| * w m = D.localizer m p.1 * (w m * |f p|) := by ring
        _ ≤ D.localizer m p.1 * A := mul_le_mul_of_nonneg_left hb hχb.1
        _ ≤ A := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hχb.2 hA
  let q : ℕ → PolarPoint → ℝ := fun m p => (w m * (D.localizer m p.1 * f p)) ^ 2
  have hq (m : ℕ) : Integrable (q m) (radialPhysicalMeasure D) :=
    ((hcell m).const_mul (w m)).integrable_sq
  have hcell_eq (m : ℕ) : sourceCellSquare D γ 0 f m =
      (2 * Real.pi)⁻¹ * ∫ p, q m p ∂radialPhysicalMeasure D := by
    have he : Real.exp (2 * γ * radialS (D.cellIndex m)) = (w m) ^ 2 := by
      dsimp only [w]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simp only [sourceCellSquare, mul_zero, zero_mul, zero_add,
      r11b_referenceCellSquare_eq_integral hab hcell m, he, q, mul_pow,
      integral_const_mul]
    ring
  have hpoint (s : Finset ℕ) (p : PolarPoint) : (∑ m ∈ s, q m p) ≤ A ^ 2 := by
    have hterm (m : ℕ) : q m p ≤ A ^ 2 * (D.localizer m p.1) ^ 2 := by
      by_cases hχ : D.localizer m p.1 = 0
      · simp only [q, hχ, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0), le_refl]
      · have hb := hbound m p (hpart.2.2.1 m hχ)
        have hsq := pow_le_pow_left₀ (mul_nonneg (hw m).le (abs_nonneg _)) hb 2
        calc
          q m p = (w m * |f p|) ^ 2 * (D.localizer m p.1) ^ 2 := by
            simp only [q, mul_pow, sq_abs]
            ring
          _ ≤ A ^ 2 * (D.localizer m p.1) ^ 2 :=
            mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    calc
      (∑ m ∈ s, q m p) ≤ ∑ m ∈ s, A ^ 2 * (D.localizer m p.1) ^ 2 :=
        Finset.sum_le_sum (fun m _ => hterm m)
      _ = A ^ 2 * ∑ m ∈ s, (D.localizer m p.1) ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ A ^ 2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (profile_localizer_sq_sum_le_one hpart s p.1) (sq_nonneg A)
  have hfinite (s : Finset ℕ) : (∑ m ∈ s, sourceCellSquare D γ 0 f m) ≤
      (2 * Real.pi)⁻¹ * ∫ _ : PolarPoint, A ^ 2 ∂radialPhysicalMeasure D := by
    simp_rw [hcell_eq]
    rw [← Finset.mul_sum, ← integral_finsetSum s (fun m _ => hq m)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact integral_mono_ae (integrable_finsetSum s (fun m _ => hq m))
      (integrable_const _) (Eventually.of_forall (hpoint s))
  have hnonneg (m : ℕ) : 0 ≤ sourceCellSquare D γ 0 f m :=
    mul_nonneg (Real.exp_pos _).le (r11b_referenceCellSquare_nonneg hab m f)
  exact ⟨hcell, summable_of_sum_le hnonneg hfinite,
    Real.tsum_le_of_sum_le hnonneg hfinite⟩

/-- Pointwise decay supplied by physical transport gives the actual
weighted reference source and output series at every lower exponent. -/
theorem n07a_material_decay_reference_cells {D : ReferenceData} {T : MaterialData}
    (hpart : RadialPartition D) (hab : D.a ≤ D.b) (hT : IsMaterialData D T)
    {γ β : ℝ} (hβ : 0 < β) (hγβ : γ < β) (q : ℝ)
    {f : PolarPoint → ℝ} (hf : AEStronglyMeasurable f (radialPhysicalMeasure D))
    {A : ℝ} (hA : 0 ≤ A)
    (hdecay : ∀ p ∈ annularOpen D, |f p| ≤ A * T.H p.1 ^ β * T.M p.1 ^ q) :
    RadialCellIntegrable D f ∧ Summable (sourceCellSquare D γ 0 f) ∧
      Summable (outputCellSquare D γ 0 f) := by
  obtain ⟨C, hC, hweight⟩ := n07a_material_reference_weight_with_M hpart hT hβ hγβ q
  have hb (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ D.cells m) :
      Real.exp (γ * radialS (D.cellIndex m)) * |f p| ≤ A * C := by
    calc
      _ ≤ Real.exp (γ * radialS (D.cellIndex m)) *
          (A * T.H p.1 ^ β * T.M p.1 ^ q) := mul_le_mul_of_nonneg_left
        (hdecay p ⟨hpart.2.2.2.1 m hp, mem_univ _⟩) (Real.exp_pos _).le
      _ = A * (Real.exp (γ * radialS (D.cellIndex m)) * T.H p.1 ^ β * T.M p.1 ^ q) := by ring
      _ ≤ A * C := mul_le_mul_of_nonneg_left (hweight m p.1 hp) hA
  obtain ⟨hcell, hs, _⟩ := n07a_reference_cells_of_weighted_bound hpart hab hf γ
    (A * C) (mul_nonneg hA hC.le) hb
  refine ⟨hcell, hs, ?_⟩
  have he : outputCellSquare D γ 0 f = sourceCellSquare D γ 0 f := by
    funext m
    simp only [sourceCellSquare, outputCellSquare, mul_zero, zero_mul, zero_add]
  rw [he]
  exact hs

end ContinuousFlexibility.Statements
