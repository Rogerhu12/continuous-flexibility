module

public import ContinuousFlexibility.Radial.SelectedStateMargin

/-!
# The selected angle at the inner edge of the actual short join

The existing radial ODE estimate controls the maximum norm of a pair.
Here that estimate is converted to the Euclidean lengths in the frozen
angle definition, for both solutions at once. The reverse ODE estimate
also proves that the transported states remain nonzero. The same theorem
works in either direction along the interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

theorem selectedState_norm_le_length (v : ℝ × ℝ) :
    ‖v‖ ≤ sqrt (v.1 ^ 2 + v.2 ^ 2) := by
  rw [norm_prod_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
    rw [sq_abs, sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    linarith only [sq_nonneg v.2]
  · apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
    rw [sq_abs, sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    linarith only [sq_nonneg v.1]

theorem selectedState_length_le_two_norm (v : ℝ × ℝ) :
    sqrt (v.1 ^ 2 + v.2 ^ 2) ≤ 2 * ‖v‖ := by
  have h₁ : |v.1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le v
  have h₂ : |v.2| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le v
  have hs₁ := (sq_le_sq₀ (abs_nonneg v.1) (norm_nonneg v)).mpr h₁
  have hs₂ := (sq_le_sq₀ (abs_nonneg v.2) (norm_nonneg v)).mpr h₂
  rw [sq_abs] at hs₁ hs₂
  apply (sqrt_le_left (by positivity : 0 ≤ 2 * ‖v‖)).mpr
  nlinarith only [hs₁, hs₂, sq_nonneg ‖v‖]

/-- A relative maximum-norm transfer error gives the required Euclidean
relative error, with the fixed factor two. -/
theorem selectedState_relative_error_of_norm {u v : ℝ × ℝ} {η : ℝ}
    (hη : 0 ≤ η) (herror : ‖v - u‖ ≤ η * ‖u‖) :
    sqrt ((u.1 - v.1) ^ 2 + (u.2 - v.2) ^ 2) ≤
      (2 * η) * sqrt (u.1 ^ 2 + u.2 ^ 2) := by
  calc
    _ ≤ 2 * ‖u - v‖ := selectedState_length_le_two_norm (u - v)
    _ = 2 * ‖v - u‖ := by rw [norm_sub_rev]
    _ ≤ 2 * (η * ‖u‖) := mul_le_mul_of_nonneg_left herror (by norm_num)
    _ = (2 * η) * ‖u‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (selectedState_norm_le_length u) (by positivity)

private theorem selected_angle_left_ne_zero {u v : ℝ × ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hsep : δ ≤ radialAngleSine u v) : u ≠ (0, 0) := by
  intro hzero
  rw [hzero] at hsep
  have hsep' : δ ≤ 0 := by simpa [radialAngleSine] using hsep
  exact (not_le_of_gt hδ) hsep'

private theorem selected_angle_right_ne_zero {u v : ℝ × ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hsep : δ ≤ radialAngleSine u v) : v ≠ (0, 0) :=
  selected_angle_left_ne_zero hδ (by rwa [radialAngleSine_comm])

/-- A solution whose state is nonzero at one point cannot acquire zero
state at another point of the join. This uses the actual reverse ODE
transfer, with no smallness assumption. -/
theorem joinState_ne_zero_of_transfer {J W Λ r₀ r₁ s t : ℝ} {w u : ℝ → ℝ}
    (hr₀ : 0 < r₀) (hJ : 1 ≤ J) (hW : 0 < W) (hΛ : 1 ≤ Λ)
    (hreg : ∀ r ∈ Icc r₀ r₁, DifferentiableAt ℝ w r ∧
      DifferentiableAt ℝ u r ∧ DifferentiableAt ℝ (deriv u) r)
    (hw : ∀ r ∈ Icc r₀ r₁, 0 < w r ∧ w r ≤ Λ * W ∧ W ≤ Λ * w r)
    (hode : ∀ r ∈ Icc r₀ r₁, radialJacobi J w u r = 0)
    (hs : s ∈ Icc r₀ r₁) (ht : t ∈ Icc r₀ r₁)
    (hne : joinState J W w u s ≠ (0, 0)) :
    joinState J W w u t ≠ (0, 0) := by
  intro hz
  have h := joinState_transfer hr₀ hJ hW hΛ hreg hw hode t ht s hs
  have hn : ‖joinState J W w u s‖ ≤ 0 := by
    simpa only [hz, show ((0, 0) : ℝ × ℝ) = 0 from rfl,
      sub_zero, norm_zero, mul_zero] using h
  exact hne (norm_le_zero_iff.mp hn)

/-- Transfer a selected angle between the two actual solutions along the
same positive join. The exponential smallness hypothesis concerns only the
geometry and the frequency, not the unknown transported angle. -/
theorem joinState_selected_angle_lower {J W Λ r₀ r₁ s t δ : ℝ}
    {w u v : ℝ → ℝ}
    (hr₀ : 0 < r₀) (hJ : 1 ≤ J) (hW : 0 < W) (hΛ : 1 ≤ Λ)
    (hregU : ∀ r ∈ Icc r₀ r₁, DifferentiableAt ℝ w r ∧
      DifferentiableAt ℝ u r ∧ DifferentiableAt ℝ (deriv u) r)
    (hregV : ∀ r ∈ Icc r₀ r₁, DifferentiableAt ℝ w r ∧
      DifferentiableAt ℝ v r ∧ DifferentiableAt ℝ (deriv v) r)
    (hw : ∀ r ∈ Icc r₀ r₁, 0 < w r ∧ w r ≤ Λ * W ∧ W ≤ Λ * w r)
    (hodeU : ∀ r ∈ Icc r₀ r₁, radialJacobi J w u r = 0)
    (hodeV : ∀ r ∈ Icc r₀ r₁, radialJacobi J w v r = 0)
    (hs : s ∈ Icc r₀ r₁) (ht : t ∈ Icc r₀ r₁) (hδ : 0 < δ)
    (hsep : δ ≤ radialAngleSine (joinState J W w u s) (joinState J W w v s))
    (hsmall : exp (2 * J * Λ / r₀ * |t - s|) - 1 ≤ δ / 16) :
    joinState J W w u t ≠ (0, 0) ∧ joinState J W w v t ≠ (0, 0) ∧
      δ / 2 ≤ radialAngleSine (joinState J W w u t) (joinState J W w v t) := by
  have hUs := selected_angle_left_ne_zero hδ hsep
  have hVs := selected_angle_right_ne_zero hδ hsep
  have hUt := joinState_ne_zero_of_transfer hr₀ hJ hW hΛ hregU hw hodeU hs ht hUs
  have hVt := joinState_ne_zero_of_transfer hr₀ hJ hW hΛ hregV hw hodeV hs ht hVs
  let η := exp (2 * J * Λ / r₀ * |t - s|) - 1
  have hJ₀ : 0 ≤ J := zero_le_one.trans hJ
  have hΛ₀ : 0 ≤ Λ := zero_le_one.trans hΛ
  have hη : 0 ≤ η := sub_nonneg.mpr (one_le_exp_iff.mpr (by positivity))
  have hηδ : 2 * η ≤ δ / 8 := by dsimp only [η]; linarith only [hsmall]
  refine ⟨hUt, hVt, ?_⟩
  apply radialAngleSine_perturb_half hUs hVs hUt hVt hsep hηδ
  · exact selectedState_relative_error_of_norm hη
      (joinState_transfer hr₀ hJ hW hΛ hregU hw hodeU s hs t ht)
  · exact selectedState_relative_error_of_norm hη
      (joinState_transfer hr₀ hJ hW hΛ hregV hw hodeV s hs t ht)

end ContinuousFlexibility.Radial
