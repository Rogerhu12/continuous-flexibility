import ContinuousFlexibility.Radial.R11bCellBessel

/-!
# Finite angular projection preserves every weighted cell square bound

Projection commutes pointwise with each radial localizer. The physical
contraction therefore applies before summing any nonnegative cell weights.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open scoped BigOperators
open ContinuousFlexibility.Statements

theorem r11bFiniteProjection_radial_mul {ι : Type*} (s : Finset ι)
    (e : ι → ℝ → ℝ) (a : ℝ → ℝ) (f : PolarPoint → ℝ) :
    r11bFiniteProjection s e (fun x => a x.1 * f x) =
      fun x => a x.1 * r11bFiniteProjection s e f x := by
  funext x
  simp only [r11bFiniteProjection, finiteAngularProjection, r11b_angularPairing_const_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem r11b_finiteProjection_cell_bound {D : ReferenceData} (hab : D.a ≤ D.b)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℝ → ℝ)
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f)
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0) :
    RadialCellIntegrable D (r11bFiniteProjection s e f) ∧
      ∀ m, referenceCellSquare D m (r11bFiniteProjection s e f) ≤
        referenceCellSquare D m f := by
  have hp : RadialCellIntegrable D (r11bFiniteProjection s e f) := by
    intro m
    have h := r11b_finiteProjection_memLp s e (hf m) he
    rw [r11bFiniteProjection_radial_mul s e (D.localizer m) f] at h
    exact h
  refine ⟨hp, fun m => ?_⟩
  have h := r11b_finiteProjection_square_integral_le s e (hf m) he horth
  rw [r11bFiniteProjection_radial_mul s e (D.localizer m) f] at h
  rw [r11b_referenceCellSquare_eq_integral hab hp m,
    r11b_referenceCellSquare_eq_integral hab hf m]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem r11b_finiteProjection_weighted_bound {D : ReferenceData} (hab : D.a ≤ D.b)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℝ → ℝ)
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f)
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0)
    (w : ℕ → ℝ) (hw : ∀ m, 0 ≤ w m)
    (hs : Summable (fun m => w m * referenceCellSquare D m f)) :
    RadialCellIntegrable D (r11bFiniteProjection s e f) ∧
      Summable (fun m => w m * referenceCellSquare D m (r11bFiniteProjection s e f)) ∧
      (∑' m, w m * referenceCellSquare D m (r11bFiniteProjection s e f)) ≤
        ∑' m, w m * referenceCellSquare D m f := by
  obtain ⟨hp, hcell⟩ := r11b_finiteProjection_cell_bound hab s e hf he horth
  have hnonneg (m : ℕ) :
      0 ≤ w m * referenceCellSquare D m (r11bFiniteProjection s e f) :=
    mul_nonneg (hw m) (r11b_referenceCellSquare_nonneg hab m _)
  have hle (m : ℕ) :
      w m * referenceCellSquare D m (r11bFiniteProjection s e f) ≤
        w m * referenceCellSquare D m f :=
    mul_le_mul_of_nonneg_left (hcell m) (hw m)
  have hpsum : Summable (fun m => w m *
      referenceCellSquare D m (r11bFiniteProjection s e f)) :=
    Summable.of_nonneg_of_le hnonneg hle hs
  exact ⟨hp, hpsum, Summable.tsum_le_tsum hle hpsum hs⟩

end ContinuousFlexibility.Radial
