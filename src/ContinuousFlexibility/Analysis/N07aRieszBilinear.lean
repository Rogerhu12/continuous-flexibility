import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Riesz realization of a pointwise summable bilinear form

The hypothesis concerns absolute scalar sums, not a vector-valued series.
It constructs a genuine bounded operator whose every pairing is the
prescribed sum.  Angular block estimates supply these hypotheses.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped RealInnerProductSpace

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def n07aSummableBilinear (b : ι → E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    (hb : ∀ x y, Summable (fun i => b i x y)) : E →ₗ[ℝ] F →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑' i, b i x y)
    (by
      intro x z y
      simp only [map_add, LinearMap.add_apply]
      exact (hb x y).tsum_add (hb z y))
    (by
      intro c x y
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact tsum_mul_left)
    (by
      intro x y z
      simp only [map_add]
      exact (hb x y).tsum_add (hb x z))
    (by
      intro c x y
      simp only [map_smul, smul_eq_mul]
      exact tsum_mul_left)

theorem n07aSummableBilinear_apply
    (b : ι → E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    (hb : ∀ x y, Summable (fun i => b i x y)) (x : E) (y : F) :
    n07aSummableBilinear b hb x y = ∑' i, b i x y := rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem n07aSummableBilinear_bound
    (b : ι → E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (hb : ∀ x y, Summable (fun i => b i x y)) (C : ℝ)
    (hC : ∀ x y, ‖∑' i, b i x y‖ ≤ C * ‖x‖ * ‖y‖) :
    ∀ x y, ‖n07aSummableBilinear b hb x y‖ ≤ C * ‖x‖ * ‖y‖ := hC

def n07aBilinearRiesz
    (b : ι → E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (hb : ∀ x y, Summable (fun i => b i x y)) (C : ℝ)
    (hC : ∀ x y, ‖∑' i, b i x y‖ ≤ C * ‖x‖ * ‖y‖) : E →L[ℝ] H :=
  (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((n07aSummableBilinear b hb).mkContinuous₂ C (n07aSummableBilinear_bound b hb C hC))

theorem n07aBilinearRiesz_pairing
    (b : ι → E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (hb : ∀ x y, Summable (fun i => b i x y)) (C : ℝ)
    (hC : ∀ x y, ‖∑' i, b i x y‖ ≤ C * ‖x‖ * ‖y‖) (x : E) (y : H) :
    ⟪n07aBilinearRiesz b hb C hC x, y⟫ = ∑' i, b i x y := by
  change ⟪(InnerProductSpace.toDual ℝ H).symm
    (((n07aSummableBilinear b hb).mkContinuous₂ C
      (n07aSummableBilinear_bound b hb C hC)) x), y⟫ = _
  rw [InnerProductSpace.toDual_symm_apply, LinearMap.mkContinuous₂_apply,
    n07aSummableBilinear_apply]

theorem n07aBilinearRiesz_norm_le
    (b : ι → E →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (hb : ∀ x y, Summable (fun i => b i x y)) {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ∀ x y, ‖∑' i, b i x y‖ ≤ C * ‖x‖ * ‖y‖) :
    ‖n07aBilinearRiesz b hb C hC‖ ≤ C := by
  let B := (n07aSummableBilinear b hb).mkContinuous₂ C (n07aSummableBilinear_bound b hb C hC)
  have hB : ‖B‖ ≤ C :=
    LinearMap.mkContinuous₂_norm_le _ hC₀ (n07aSummableBilinear_bound b hb C hC)
  apply ContinuousLinearMap.opNorm_le_bound _ hC₀
  intro x
  have he : ‖n07aBilinearRiesz b hb C hC x‖ = ‖B x‖ :=
    (InnerProductSpace.toDual ℝ H).symm.norm_map (B x)
  exact he.le.trans ((B.le_opNorm x).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg x)))

end ContinuousFlexibility.Analysis
