module

public import ContinuousFlexibility.Radial.R11bPartitionL2
public import ContinuousFlexibility.Radial.R11bWeightEmbedding
public import ContinuousFlexibility.Radial.ProfileScalarSquares

/-!
# Ordinary L2 control from output-weighted localized squares

The lower bound for the output weight uses the positive attenuation
exponent. Its constant is uniform in the scalar field, the partition, and
any Fourier mode. No count of cells with the same index is needed.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped BigOperators ContDiff

theorem r11b_memLp_of_weighted_localized_square_summable
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (χ : ℕ → α → ℝ) (f : α → ℝ) (w : ℕ → ℝ) {B : ℕ} {K : ℝ}
    (hweight : ∀ m, 1 ≤ K * w m)
    (hlocal : ∀ m, MemLp (fun x => χ m x * f x) 2 μ)
    (hfinite : ∀ᵐ x ∂μ, (Function.support (fun m => χ m x)).Finite)
    (hcard : ∀ᵐ x ∂μ, (Function.support (fun m => χ m x)).ncard ≤ B)
    (hsum : ∀ᵐ x ∂μ, (∑' m, χ m x) = 1)
    (hs : Summable (fun m => w m * ∫ x, (χ m x * f x) ^ 2 ∂μ)) :
    MemLp f 2 μ ∧ (∫ x, f x ^ 2 ∂μ) ≤
      (B : ℝ) * K * ∑' m, w m * ∫ x, (χ m x * f x) ^ 2 ∂μ := by
  obtain ⟨hs₀, hb₀⟩ := r11b_weighted_tsum_le
    (fun _ => 1) w (fun m => ∫ x, (χ m x * f x) ^ 2 ∂μ)
    (fun _ => zero_le_one)
    (fun m => integral_nonneg (fun x => sq_nonneg (χ m x * f x)))
    hweight hs
  simp only [one_mul] at hs₀ hb₀
  obtain ⟨hf, hb⟩ := r11b_memLp_of_localized_square_summable
    χ f hlocal hfinite hcard hsum hs₀
  refine ⟨hf, hb.trans ?_⟩
  calc
    (B : ℝ) * (∑' m, ∫ x, (χ m x * f x) ^ 2 ∂μ) ≤
        (B : ℝ) * (K * ∑' m, w m * ∫ x, (χ m x * f x) ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left hb₀ (Nat.cast_nonneg B)
    _ = _ := (mul_assoc _ _ _).symm

/-- The constant precedes all choices of partition and field. Thus the
ordinary L2 bound remains uniform when it is summed over Fourier modes. -/
theorem r11b_output_weighted_square_controls_L2 (γ M : ℝ) (hγ : 0 < γ) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {α : Type*} [MeasurableSpace α] (μ : Measure α)
        (index : ℕ → ℕ) (χ : ℕ → α → ℝ) (f : α → ℝ) (B : ℕ),
      (∀ m, MemLp (fun x => χ m x * f x) 2 μ) →
      (∀ᵐ x ∂μ, (Function.support (fun m => χ m x)).Finite) →
      (∀ᵐ x ∂μ, (Function.support (fun m => χ m x)).ncard ≤ B) →
      (∀ᵐ x ∂μ, (∑' m, χ m x) = 1) →
      Summable (fun m =>
        exp (-2 * M * radialQ (index m) + 2 * γ * radialS (index m)) *
          ∫ x, (χ m x * f x) ^ 2 ∂μ) →
      MemLp f 2 μ ∧ (∫ x, f x ^ 2 ∂μ) ≤
        (B : ℝ) * K * ∑' m,
          exp (-2 * M * radialQ (index m) + 2 * γ * radialS (index m)) *
            ∫ x, (χ m x * f x) ^ 2 ∂μ := by
  obtain ⟨K, hK, hw⟩ := r11b_exp_weight_le 0 (-2 * M) 0 γ hγ
  refine ⟨K, hK, ?_⟩
  intro α inst μ index χ f B hlocal hfinite hcard hsum hs
  apply r11b_memLp_of_weighted_localized_square_summable
    χ f (fun m => exp (-2 * M * radialQ (index m) + 2 * γ * radialS (index m)))
    ?_ hlocal hfinite hcard hsum hs
  intro m
  simpa only [mul_zero, zero_mul, zero_add, add_zero, exp_zero] using hw (index m)

/-- Profile-specific form with the partition overlap absorbed into one
constant chosen before the scalar field. -/
theorem profile_output_weighted_square_controls_L2
    {D : ReferenceData} (hpart : RadialPartition D) (γ M : ℝ) (hγ : 0 < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ℝ → ℝ,
      (∀ m, MemLp (fun r => D.localizer m r * f r) 2
        (volume.restrict (radialCore D))) →
      Summable (fun m =>
        exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          profileScalarCellSquare D f m) →
      MemLp f 2 (volume.restrict (radialCore D)) ∧
      (∫ r in radialCore D, f r ^ 2) ≤ K * ∑' m,
        exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          profileScalarCellSquare D f m := by
  obtain ⟨E, hE, hl2⟩ := r11b_output_weighted_square_controls_L2 γ M hγ
  obtain ⟨B, hB⟩ := hpart.2.2.2.2.2
  have hBE : 0 ≤ (B : ℝ) * E :=
    mul_nonneg (Nat.cast_nonneg B) (zero_le_one.trans hE)
  refine ⟨(B : ℝ) * E + 1, by linarith, ?_⟩
  intro f hlocal hs
  have hsum : ∀ᵐ r ∂volume.restrict (radialCore D),
      (∑' m, D.localizer m r) = 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (hpart.2.2.2.2.1 r hr).2
  obtain ⟨hf, hb⟩ := hl2 (volume.restrict (radialCore D))
    D.cellIndex D.localizer f B hlocal
    (Eventually.of_forall fun r => (hB r).1)
    (Eventually.of_forall fun r => (hB r).2) hsum hs
  refine ⟨hf, hb.trans ?_⟩
  apply mul_le_mul_of_nonneg_right (by linarith)
  exact tsum_nonneg (fun m => mul_nonneg (exp_pos _).le
    (profileScalarCellSquare_nonneg D f m))

/-- The actual first derivative is in ordinary L2 once its weighted
localized square series is summable; no derivative measurability or
ordinary L2 premise is added. -/
theorem profile_weighted_derivative_controls_L2
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (γ M : ℝ) (hγ : 0 < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ → ℝ,
      ContDiffOn ℝ 1 u (radialCore D) →
      Summable (fun m =>
        exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          profileScalarCellSquare D (deriv u) m) →
      MemLp (deriv u) 2 (volume.restrict (radialCore D)) ∧
      (∫ r in radialCore D, deriv u r ^ 2) ≤ K * ∑' m,
        exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
          profileScalarCellSquare D (deriv u) m := by
  obtain ⟨C, h⟩ := hD
  obtain ⟨K, hK, hb⟩ := profile_output_weighted_square_controls_L2 h.2.1 γ M hγ
  refine ⟨K, hK, ?_⟩
  intro u hu hs
  exact hb (deriv u) (profile_memLp_localizer_deriv h hu) hs


end ContinuousFlexibility.Radial
