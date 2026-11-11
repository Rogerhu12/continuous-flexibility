import ContinuousFlexibility.Radial.R11bCellBessel

/-!
# Weighted Bessel bounds for the original modal coefficients

A finite family of coefficient-square series is controlled directly by the
weighted cell-square series of the physical field. The output specialization
retains the actual remainder and its original output norm.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open scoped BigOperators
open ContinuousFlexibility.Statements

theorem r11b_weighted_finset_tsum_bound {ι : Type*}
    (s : Finset ι) (a : ι → ℕ → ℝ) (b w : ℕ → ℝ)
    (ha : ∀ i ∈ s, ∀ m, 0 ≤ a i m) (hw : ∀ m, 0 ≤ w m)
    (hcell : ∀ m, (∑ i ∈ s, a i m) ≤ b m)
    (hs : Summable (fun m => w m * b m)) :
    (∀ i ∈ s, Summable (fun m => w m * a i m)) ∧
      (∑ i ∈ s, ∑' m, w m * a i m) ≤ ∑' m, w m * b m := by
  have hsi (i : ι) (hi : i ∈ s) : Summable (fun m => w m * a i m) := by
    apply Summable.of_nonneg_of_le (fun m => mul_nonneg (hw m) (ha i hi m)) _ hs
    intro m
    exact mul_le_mul_of_nonneg_left
      ((Finset.single_le_sum (fun j hj => ha j hj m) hi).trans (hcell m)) (hw m)
  refine ⟨hsi, ?_⟩
  rw [← Summable.tsum_finsetSum hsi]
  apply Summable.tsum_le_tsum _ (summable_sum hsi) hs
  intro m
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hcell m) (hw m)

theorem r11b_weighted_cell_finite_bessel {D : ReferenceData} (hab : D.a ≤ D.b)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℝ → ℝ)
    {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f)
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0)
    (w : ℕ → ℝ) (hw : ∀ m, 0 ≤ w m)
    (hs : Summable (fun m => w m * referenceCellSquare D m f)) :
    (∀ i ∈ s, Summable (fun m => w m *
      ∫ r, (D.localizer m r * angularPairing (fun θ => f (r, θ)) (e i)) ^ 2
        ∂volume.restrict (radialCore D))) ∧
      (∑ i ∈ s, ∑' m, w m *
        ∫ r, (D.localizer m r * angularPairing (fun θ => f (r, θ)) (e i)) ^ 2
          ∂volume.restrict (radialCore D)) ≤
        ∑' m, w m * referenceCellSquare D m f := by
  apply r11b_weighted_finset_tsum_bound s
    (fun i m => ∫ r,
      (D.localizer m r * angularPairing (fun θ => f (r, θ)) (e i)) ^ 2
        ∂volume.restrict (radialCore D))
    (fun m => referenceCellSquare D m f) w
    (fun i _ m => integral_nonneg (fun r => sq_nonneg _)) hw _ hs
  exact r11b_cell_finite_bessel hab s e hf he horth

theorem r11b_output_weighted_finite_bessel {D : ReferenceData} (hab : D.a ≤ D.b)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℝ → ℝ)
    {γ M a : ℝ} {U : RadialUnknown} (hU : OutputRealization D γ M a U)
    (he : ∀ i ∈ s, MemLp (e i) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then 1 else 0) :
    (∀ i ∈ s, Summable (fun m =>
      exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        ∫ r, (D.localizer m r *
          angularPairing (fun θ => outputRemainder D a U (r, θ)) (e i)) ^ 2
            ∂volume.restrict (radialCore D))) ∧
      (∑ i ∈ s, ∑' m,
        exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          ∫ r, (D.localizer m r *
            angularPairing (fun θ => outputRemainder D a U (r, θ)) (e i)) ^ 2
              ∂volume.restrict (radialCore D)) ≤ outputNormSquare D γ M a U := by
  obtain ⟨hsi, hbound⟩ := r11b_weighted_cell_finite_bessel hab s e hU.1 he horth
    (fun m => exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)))
    (fun m => (exp_pos _).le) hU.2.1
  refine ⟨hsi, hbound.trans ?_⟩
  change (∑' m, outputCellSquare D γ M (outputRemainder D a U) m) ≤
    a ^ 2 + U.2 ^ 2 + ∑' m, outputCellSquare D γ M (outputRemainder D a U) m
  nlinarith only [sq_nonneg a, sq_nonneg U.2]

end ContinuousFlexibility.Radial
