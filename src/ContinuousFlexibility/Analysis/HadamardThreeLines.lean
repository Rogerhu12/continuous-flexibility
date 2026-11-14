module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Hadamard interpolation for operator families

This is the three-lines input used in the angular inverse regularity argument in
Section 8 of the readable manuscript.  The closed-strip boundedness hypothesis is
essential: boundary bounds alone do not imply the conclusion, as the scalar
entire function `exp (sin (π z))` demonstrates.

The operator theorem uses holomorphy, continuity, and strip boundedness separately
for each vector.  In particular, it does not require continuity of imaginary
spectral powers in operator norm.  `DiffContOnCl` means complex differentiability
on the open strip and continuity on its closure.  Neither endpoint constant is
required to be strictly positive.
-/

@[expose] public section

namespace ContinuousFlexibility.Analysis

open Complex.HadamardThreeLines

/-- Banach-valued three-lines estimate on an arbitrary vertical strip. -/
theorem hadamard_threeLines_norm_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℂ → F} {l u M₀ M₁ : ℝ} {z : ℂ}
    (hlu : l < u) (hz : z ∈ verticalClosedStrip l u)
    (hhol : DiffContOnCl ℂ f (verticalStrip l u))
    (hbounded : ∃ C : ℝ, ∀ w ∈ verticalClosedStrip l u, ‖f w‖ ≤ C)
    (hleft : ∀ w : ℂ, w.re = l → ‖f w‖ ≤ M₀)
    (hright : ∀ w : ℂ, w.re = u → ‖f w‖ ≤ M₁) :
    ‖f z‖ ≤ M₀ ^ (1 - (z.re - l) / (u - l)) *
      M₁ ^ ((z.re - l) / (u - l)) := by
  refine norm_le_interp_of_mem_verticalClosedStrip' hlu hz hhol ?_ ?_ ?_
  · rcases hbounded with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro y ⟨w, hw, rfl⟩
    exact hC w hw
  · intro w hw
    exact hleft w (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hw)
  · intro w hw
    exact hright w (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hw)

private theorem threeLines_scale_factor
    {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) (t : ℝ) :
    (a * r) ^ (1 - t) * (b * r) ^ t = (a ^ (1 - t) * b ^ t) * r := by
  rw [Real.mul_rpow ha hr, Real.mul_rpow hb hr]
  calc
    a ^ (1 - t) * r ^ (1 - t) * (b ^ t * r ^ t) =
        (a ^ (1 - t) * b ^ t) * (r ^ (1 - t) * r ^ t) := by ac_rfl
    _ = (a ^ (1 - t) * b ^ t) * r := by
      rw [← Real.rpow_add' hr (show (1 - t) + t ≠ 0 by simp)]
      simp only [sub_add_cancel, Real.rpow_one]

/-- The homogeneous form of the three-lines bound, including a zero scale or a
zero boundary constant.  This is useful for families initially defined on a dense
linear domain. -/
theorem hadamard_threeLines_scaled_norm_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℂ → F} {l u M₀ M₁ r : ℝ} {z : ℂ}
    (hlu : l < u) (hz : z ∈ verticalClosedStrip l u)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hr : 0 ≤ r)
    (hhol : DiffContOnCl ℂ f (verticalStrip l u))
    (hbounded : ∃ C : ℝ, ∀ w ∈ verticalClosedStrip l u, ‖f w‖ ≤ C)
    (hleft : ∀ w : ℂ, w.re = l → ‖f w‖ ≤ M₀ * r)
    (hright : ∀ w : ℂ, w.re = u → ‖f w‖ ≤ M₁ * r) :
    ‖f z‖ ≤ (M₀ ^ (1 - (z.re - l) / (u - l)) *
      M₁ ^ ((z.re - l) / (u - l))) * r := by
  have h := hadamard_threeLines_norm_le hlu hz hhol hbounded hleft hright
  rw [threeLines_scale_factor hM₀ hM₁ hr] at h
  exact h

/-- Hadamard interpolation in the actual operator norm, assuming only strong
holomorphy and strong continuity of the family.  The bound on the closed strip may
depend on the vector; no uniform operator bound on that strip is assumed. -/
theorem hadamard_threeLines_operator_norm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {A : ℂ → E →L[ℂ] F} {l u M₀ M₁ : ℝ} {z : ℂ}
    (hlu : l < u) (hz : z ∈ verticalClosedStrip l u)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hhol : ∀ x : E, DiffContOnCl ℂ (fun w ↦ A w x) (verticalStrip l u))
    (hbounded : ∀ x : E, ∃ C : ℝ,
      ∀ w ∈ verticalClosedStrip l u, ‖A w x‖ ≤ C)
    (hleft : ∀ w : ℂ, w.re = l → ‖A w‖ ≤ M₀)
    (hright : ∀ w : ℂ, w.re = u → ‖A w‖ ≤ M₁) :
    ‖A z‖ ≤ M₀ ^ (1 - (z.re - l) / (u - l)) *
      M₁ ^ ((z.re - l) / (u - l)) := by
  apply (A z).opNorm_le_bound
    (mul_nonneg (Real.rpow_nonneg hM₀ _) (Real.rpow_nonneg hM₁ _))
  intro x
  apply hadamard_threeLines_scaled_norm_le hlu hz hM₀ hM₁ (norm_nonneg x)
    (hhol x) (hbounded x)
  · intro w hw
    exact (A w).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hleft w hw)
      (norm_nonneg x))
  · intro w hw
    exact (A w).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hright w hw)
      (norm_nonneg x))

/-- The unit-strip operator estimate, in the form stated in the appendix. -/
theorem hadamard_threeLines_operator_norm_unit
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {A : ℂ → E →L[ℂ] F} {M₀ M₁ : ℝ} {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hhol : ∀ x : E, DiffContOnCl ℂ (fun w ↦ A w x) (verticalStrip 0 1))
    (hbounded : ∀ x : E, ∃ C : ℝ,
      ∀ w ∈ verticalClosedStrip 0 1, ‖A w x‖ ≤ C)
    (hleft : ∀ w : ℂ, w.re = 0 → ‖A w‖ ≤ M₀)
    (hright : ∀ w : ℂ, w.re = 1 → ‖A w‖ ≤ M₁) :
    ‖A z‖ ≤ M₀ ^ (1 - z.re) * M₁ ^ z.re := by
  simpa only [sub_zero, div_one] using
    hadamard_threeLines_operator_norm zero_lt_one hz hM₀ hM₁ hhol hbounded hleft hright

end ContinuousFlexibility.Analysis
