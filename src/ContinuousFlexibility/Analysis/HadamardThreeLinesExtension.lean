module

public import ContinuousFlexibility.Analysis.HadamardThreeLines
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Three-lines interpolation from a dense linear domain

Weighted spectral families can first be defined on finite spectral vectors.  This
file proves their three-lines bound on that domain and constructs the resulting
bounded operator on the ambient normed space.  Interior boundedness of that
operator is a conclusion.  Holomorphy and strip boundedness are required only for
each vector in the dense domain, which itself needs no norm or topology.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Complex.HadamardThreeLines

variable {D E F : Type*} [AddCommGroup D] [Module ℂ D]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Three-lines bound for a linear family on a domain mapped into the ambient
normed space.  Neither density nor boundedness of the interior operators is
needed to prove this estimate. -/
theorem hadamard_threeLines_linear_bound
    {i : D →ₗ[ℂ] E} {A : ℂ → D →ₗ[ℂ] F} {l u M₀ M₁ : ℝ} {z : ℂ}
    (hlu : l < u) (hz : z ∈ verticalClosedStrip l u)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hhol : ∀ x : D, DiffContOnCl ℂ (fun w ↦ A w x) (verticalStrip l u))
    (hbounded : ∀ x : D, ∃ C : ℝ,
      ∀ w ∈ verticalClosedStrip l u, ‖A w x‖ ≤ C)
    (hleft : ∀ (w : ℂ) (x : D), w.re = l → ‖A w x‖ ≤ M₀ * ‖i x‖)
    (hright : ∀ (w : ℂ) (x : D), w.re = u → ‖A w x‖ ≤ M₁ * ‖i x‖)
    (x : D) :
    ‖A z x‖ ≤ (M₀ ^ (1 - (z.re - l) / (u - l)) *
      M₁ ^ ((z.re - l) / (u - l))) * ‖i x‖ :=
  hadamard_threeLines_scaled_norm_le hlu hz hM₀ hM₁ (norm_nonneg (i x))
    (hhol x) (hbounded x) (fun w hw ↦ hleft w x hw) (fun w hw ↦ hright w x hw)

variable [CompleteSpace F]

/-- The continuous linear extension of the interpolated family.  Theorems below
identify it on the dense domain and establish its operator norm estimate. -/
def hadamardThreeLinesExtension (i : D →ₗ[ℂ] E) (A : ℂ → D →ₗ[ℂ] F)
    (z : ℂ) : E →L[ℂ] F :=
  (A z).extendOfNorm i

/-- Agreement of the constructed extension with a bounded map on its dense
domain. -/
theorem hadamardThreeLinesExtension_apply_of_bound
    {i : D →ₗ[ℂ] E} {A : ℂ → D →ₗ[ℂ] F} {z : ℂ}
    (hdense : DenseRange i)
    (hbound : ∃ C : ℝ, ∀ x : D, ‖A z x‖ ≤ C * ‖i x‖) (x : D) :
    hadamardThreeLinesExtension i A z (i x) = A z x :=
  LinearMap.extendOfNorm_eq hdense hbound x

/-- The three-lines hypotheses on a dense domain produce an actual bounded
operator on the whole space, with the asserted geometric mean bound. -/
theorem hadamardThreeLinesExtension_spec
    {i : D →ₗ[ℂ] E} {A : ℂ → D →ₗ[ℂ] F} {l u M₀ M₁ : ℝ} {z : ℂ}
    (hdense : DenseRange i) (hlu : l < u) (hz : z ∈ verticalClosedStrip l u)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hhol : ∀ x : D, DiffContOnCl ℂ (fun w ↦ A w x) (verticalStrip l u))
    (hbounded : ∀ x : D, ∃ C : ℝ,
      ∀ w ∈ verticalClosedStrip l u, ‖A w x‖ ≤ C)
    (hleft : ∀ (w : ℂ) (x : D), w.re = l → ‖A w x‖ ≤ M₀ * ‖i x‖)
    (hright : ∀ (w : ℂ) (x : D), w.re = u → ‖A w x‖ ≤ M₁ * ‖i x‖) :
    (∀ x : D, hadamardThreeLinesExtension i A z (i x) = A z x) ∧
      ‖hadamardThreeLinesExtension i A z‖ ≤
        M₀ ^ (1 - (z.re - l) / (u - l)) * M₁ ^ ((z.re - l) / (u - l)) := by
  have hbound := hadamard_threeLines_linear_bound hlu hz hM₀ hM₁ hhol hbounded hleft hright
  constructor
  · exact hadamardThreeLinesExtension_apply_of_bound hdense ⟨_, hbound⟩
  · exact LinearMap.opNorm_extendOfNorm_le hdense
      (mul_nonneg (Real.rpow_nonneg hM₀ _) (Real.rpow_nonneg hM₁ _)) hbound

/-- The extension is the unique continuous linear operator with the prescribed
values on the dense domain. -/
theorem hadamardThreeLinesExtension_unique
    {i : D →ₗ[ℂ] E} {A : ℂ → D →ₗ[ℂ] F} {z : ℂ}
    (hdense : DenseRange i) {C : ℝ}
    (hbound : ∀ x : D, ‖A z x‖ ≤ C * ‖i x‖)
    (B : E →L[ℂ] F) (hB : B.toLinearMap.comp i = A z) :
    hadamardThreeLinesExtension i A z = B :=
  LinearMap.extendOfNorm_unique hdense C hbound B hB

/-- Unit-strip form for finite spectral approximations in the angular
commutator argument. -/
theorem hadamardThreeLinesExtension_spec_unit
    {i : D →ₗ[ℂ] E} {A : ℂ → D →ₗ[ℂ] F} {M₀ M₁ : ℝ} {z : ℂ}
    (hdense : DenseRange i) (hz : z ∈ verticalClosedStrip 0 1)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hhol : ∀ x : D, DiffContOnCl ℂ (fun w ↦ A w x) (verticalStrip 0 1))
    (hbounded : ∀ x : D, ∃ C : ℝ,
      ∀ w ∈ verticalClosedStrip 0 1, ‖A w x‖ ≤ C)
    (hleft : ∀ (w : ℂ) (x : D), w.re = 0 → ‖A w x‖ ≤ M₀ * ‖i x‖)
    (hright : ∀ (w : ℂ) (x : D), w.re = 1 → ‖A w x‖ ≤ M₁ * ‖i x‖) :
    (∀ x : D, hadamardThreeLinesExtension i A z (i x) = A z x) ∧
      ‖hadamardThreeLinesExtension i A z‖ ≤ M₀ ^ (1 - z.re) * M₁ ^ z.re := by
  simpa only [sub_zero, div_one] using
    hadamardThreeLinesExtension_spec hdense zero_lt_one hz hM₀ hM₁
      hhol hbounded hleft hright

end ContinuousFlexibility.Analysis
