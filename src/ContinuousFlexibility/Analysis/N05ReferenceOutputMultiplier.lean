import ContinuousFlexibility.Radial.R11bPhysicalPairing
import ContinuousFlexibility.Radial.ReferenceCellAlgebra

/-!
# Coefficient multipliers in the actual reference output norm

A multiplier with a fixed exponential cell bound shifts the material
exponent by exactly half that bound's exponent. Every integral and square
sum here is the original physical localized norm, with no parity premise.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements

theorem n05_referenceCell_multiplier_square {D : ReferenceData}
    (hab : D.a ≤ D.b) {a f : PolarPoint → ℝ}
    (ha : AEStronglyMeasurable a (radialPhysicalMeasure D))
    (hf : RadialCellIntegrable D f) {A : ℕ → ℝ} (hA : ∀ m, 0 ≤ A m)
    (hbound : ∀ m, ∀ᵐ p ∂radialPhysicalMeasure D,
      D.localizer m p.1 ≠ 0 → |a p| ^ 2 ≤ A m) :
    RadialCellIntegrable D (fun p => a p * f p) ∧
      ∀ m, referenceCellSquare D m (fun p => a p * f p) ≤ A m * referenceCellSquare D m f := by
  have hm (m : ℕ) : AEStronglyMeasurable
      (fun p => D.localizer m p.1 * (a p * f p)) (radialPhysicalMeasure D) := by
    apply (ha.mul (hf m).aestronglyMeasurable).congr
    exact Eventually.of_forall fun p => mul_left_comm (a p) (D.localizer m p.1) (f p)
  have hb (m : ℕ) : ∀ᵐ p ∂radialPhysicalMeasure D,
      (D.localizer m p.1 * (a p * f p)) ^ 2 ≤ A m * (D.localizer m p.1 * f p) ^ 2 := by
    filter_upwards [hbound m] with p hp
    by_cases hz : D.localizer m p.1 = 0
    · simp only [hz, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, le_refl]
    · have ha2 : a p ^ 2 ≤ A m := by simpa only [sq_abs] using hp hz
      calc
        _ = a p ^ 2 * (D.localizer m p.1 * f p) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right ha2 (sq_nonneg _)
  have hmajor (m : ℕ) : Integrable
      (fun p => A m * (D.localizer m p.1 * f p) ^ 2) (radialPhysicalMeasure D) :=
    (hf m).integrable_sq.const_mul (A m)
  have hi (m : ℕ) : Integrable
      (fun p => (D.localizer m p.1 * (a p * f p)) ^ 2) (radialPhysicalMeasure D) := by
    apply (hmajor m).mono ((hm m).pow 2)
    filter_upwards [hb m] with p hp
    change ‖(D.localizer m p.1 * (a p * f p)) ^ 2‖ ≤
      ‖A m * (D.localizer m p.1 * f p) ^ 2‖
    rw [Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (mul_nonneg (hA m) (sq_nonneg _))]
    exact hp
  have hcell : RadialCellIntegrable D (fun p => a p * f p) :=
    fun m => (memLp_two_iff_integrable_sq (hm m)).mpr (hi m)
  refine ⟨hcell, fun m => ?_⟩
  rw [r11b_referenceCellSquare_eq_integral hab hcell m,
    r11b_referenceCellSquare_eq_integral hab hf m]
  have hI := integral_mono_ae (hi m) (hmajor m) (hb m)
  rw [integral_const_mul] at hI
  exact (mul_le_mul_of_nonneg_left hI (by positivity)).trans_eq (by ring)

theorem n05_referenceOutput_multiplier_bound {D : ReferenceData}
    (hab : D.a ≤ D.b) {a : PolarPoint → ℝ}
    (ha : AEStronglyMeasurable a (radialPhysicalMeasure D))
    {C L : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ m, ∀ᵐ p ∂radialPhysicalMeasure D, D.localizer m p.1 ≠ 0 →
      |a p| ^ 2 ≤ C * Real.exp (L * radialQ (D.cellIndex m)))
    (γ M : ℝ) {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f)
    (hs : Summable (outputCellSquare D γ M f)) :
    RadialCellIntegrable D (fun p => a p * f p) ∧
      Summable (outputCellSquare D γ (M + L / 2) (fun p => a p * f p)) ∧
      (∑' m, outputCellSquare D γ (M + L / 2) (fun p => a p * f p) m) ≤
        C * ∑' m, outputCellSquare D γ M f m := by
  obtain ⟨hcell, hsq⟩ := n05_referenceCell_multiplier_square hab ha hf
    (fun m => mul_nonneg hC (Real.exp_pos _).le) hbound
  have hw (m : ℕ) :
      outputCellSquare D γ (M + L / 2) (fun p => a p * f p) m ≤
        C * outputCellSquare D γ M f m := by
    unfold outputCellSquare
    calc
      _ ≤ Real.exp (-2 * (M + L / 2) * radialQ (D.cellIndex m) +
          2 * γ * radialS (D.cellIndex m)) *
        ((C * Real.exp (L * radialQ (D.cellIndex m))) * referenceCellSquare D m f) :=
        mul_le_mul_of_nonneg_left (hsq m) (Real.exp_pos _).le
      _ = C * (Real.exp (-2 * (M + L / 2) * radialQ (D.cellIndex m) +
          2 * γ * radialS (D.cellIndex m)) * Real.exp (L * radialQ (D.cellIndex m))) *
            referenceCellSquare D m f := by ring
      _ = _ := by
        rw [← Real.exp_add, show
          (-2 * (M + L / 2) * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) +
            L * radialQ (D.cellIndex m) =
          -2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m) by ring]
        ring
  have hsum := (hs.mul_left C).of_nonneg_of_le
    (fun m => outputCellSquare_nonneg hab γ (M + L / 2) hcell m) hw
  refine ⟨hcell, hsum, ?_⟩
  calc
    _ ≤ ∑' m, C * outputCellSquare D γ M f m := hsum.tsum_le_tsum hw (hs.mul_left C)
    _ = _ := tsum_mul_left

end ContinuousFlexibility.Radial
