module

public import ContinuousFlexibility.Radial.R11bPhysicalPairing
public import ContinuousFlexibility.Radial.R11bPartitionMultiplier

/-!
# Exponentially bounded cell multipliers in the physical measure

Every strictly positive attenuation absorbs a fixed coefficient exponent.
Together with finite overlap, this gives a physical L² estimate for an
unbounded multiplier whose square has a fixed exponential bound on each
localized cell. The estimate does not count cells of a given index.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open ContinuousFlexibility.Statements

theorem r11b_cell_multiplier_L2_bound {D : ReferenceData}
    (hpart : RadialPartition D) (hab : D.a ≤ D.b)
    (a : PolarPoint → ℝ) (ha : AEStronglyMeasurable a (radialPhysicalMeasure D))
    (C L A γ : ℝ) (hC : 0 ≤ C) (hγ : 0 < γ)
    (hbound : ∀ m, ∀ᵐ x ∂radialPhysicalMeasure D, D.localizer m x.1 ≠ 0 →
      |a x| ^ 2 ≤ C * exp (L * radialQ (D.cellIndex m))) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : PolarPoint → ℝ, RadialCellIntegrable D f →
      Summable (fun m => exp (A * radialQ (D.cellIndex m) +
        2 * γ * radialS (D.cellIndex m)) * referenceCellSquare D m f) →
      MemLp (fun x => a x * f x) 2 (radialPhysicalMeasure D) ∧
        (∫ x, (a x * f x) ^ 2 ∂radialPhysicalMeasure D) ≤
          K * ∑' m, exp (A * radialQ (D.cellIndex m) +
            2 * γ * radialS (D.cellIndex m)) * referenceCellSquare D m f := by
  obtain ⟨B, hB⟩ := hpart.2.2.2.2.2
  obtain ⟨E, hE, hweight⟩ := r11b_exp_weight_le L A 0 γ hγ
  have hweight' : ∀ m, exp (L * radialQ (D.cellIndex m)) ≤ E *
      exp (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) := by
    intro m
    simpa only [mul_zero, zero_mul, add_zero] using hweight (D.cellIndex m)
  let K₀ : ℝ := (B : ℝ) * (C * (2 * Real.pi)) * E
  have hK₀ : 0 ≤ K₀ := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg B) (mul_nonneg hC (by positivity)))
    (zero_le_one.trans hE)
  refine ⟨K₀ + 1, by linarith, fun f hf hs => ?_⟩
  obtain ⟨hs0, hnorm⟩ := r11b_weighted_tsum_le
    (fun m => exp (L * radialQ (D.cellIndex m)))
    (fun m => exp (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)))
    (fun m => referenceCellSquare D m f)
    (fun m => (exp_pos _).le) (fun m => r11b_referenceCellSquare_nonneg hab m f)
    hweight' hs
  have hint (m : ℕ) :
      (∫ x, (D.localizer m x.1 * f x) ^ 2 ∂radialPhysicalMeasure D) =
        (2 * Real.pi) * referenceCellSquare D m f := by
    rw [r11b_referenceCellSquare_eq_integral hab hf m]
    have hπ : 2 * Real.pi ≠ 0 := by positivity
    field_simp
  have hterm (m : ℕ) :
      (C * exp (L * radialQ (D.cellIndex m))) *
          (∫ x, (D.localizer m x.1 * f x) ^ 2 ∂radialPhysicalMeasure D) =
        (C * (2 * Real.pi)) *
          (exp (L * radialQ (D.cellIndex m)) * referenceCellSquare D m f) := by
    rw [hint]
    ring
  have hsI : Summable (fun m => (C * exp (L * radialQ (D.cellIndex m))) *
      ∫ x, (D.localizer m x.1 * f x) ^ 2 ∂radialPhysicalMeasure D) :=
    (hs0.mul_left (C * (2 * Real.pi))).congr (fun m => (hterm m).symm)
  have hsum : ∀ᵐ x ∂radialPhysicalMeasure D,
      (∑' m, D.localizer m x.1) = 1 := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with x hx
    exact (hpart.2.2.2.2.1 x.1 hx.1).2
  obtain ⟨haf, hI⟩ := r11b_memLp_mul_of_localized_square_bound
    (fun (m : ℕ) (x : PolarPoint) => D.localizer m x.1) f a
    (fun m => C * exp (L * radialQ (D.cellIndex m))) hf ha
    (fun m => mul_nonneg hC (exp_pos _).le) hbound
    (Filter.Eventually.of_forall fun x => (hB x.1).1)
    (Filter.Eventually.of_forall fun x => (hB x.1).2) hsum hsI
  refine ⟨haf, ?_⟩
  have hsum0 : 0 ≤ ∑' m, exp (A * radialQ (D.cellIndex m) +
      2 * γ * radialS (D.cellIndex m)) * referenceCellSquare D m f :=
    tsum_nonneg (fun m => mul_nonneg (exp_pos _).le
      (r11b_referenceCellSquare_nonneg hab m f))
  calc (∫ x, (a x * f x) ^ 2 ∂radialPhysicalMeasure D)
      ≤ (B : ℝ) * ∑' m, (C * exp (L * radialQ (D.cellIndex m))) *
          ∫ x, (D.localizer m x.1 * f x) ^ 2 ∂radialPhysicalMeasure D := hI
    _ = (B : ℝ) * ((C * (2 * Real.pi)) *
        ∑' m, exp (L * radialQ (D.cellIndex m)) * referenceCellSquare D m f) := by
      simp_rw [hterm]
      rw [tsum_mul_left]
    _ ≤ (B : ℝ) * ((C * (2 * Real.pi)) * (E * ∑' m,
        exp (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          referenceCellSquare D m f)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hnorm (mul_nonneg hC (by positivity)))
        (Nat.cast_nonneg B)
    _ = K₀ * ∑' m, exp (A * radialQ (D.cellIndex m) +
        2 * γ * radialS (D.cellIndex m)) * referenceCellSquare D m f := by
      dsimp [K₀]
      ring
    _ ≤ (K₀ + 1) * ∑' m, exp (A * radialQ (D.cellIndex m) +
        2 * γ * radialS (D.cellIndex m)) * referenceCellSquare D m f :=
      mul_le_mul_of_nonneg_right (by linarith) hsum0

end ContinuousFlexibility.Radial
